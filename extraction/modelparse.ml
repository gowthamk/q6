open Utils
open Speclang
open Vc
module S = SymbolicVal

module type T = 
sig
  type t
  val get_counterexample : unit -> t
end

module type Z3 = module type of Z3encode

class encoding_env = Encoding_env.encoding_env

(*
 * A function that returns modelparse module.
 *)
let make (module Z3: Z3) (env:#encoding_env) vc = 
(module struct

  open Z3

  let ke = vc.kbinds
  let te = vc.tbinds
  let ve = vc.vbinds

  let cmap = env#get_cmap
  let tmap = env#get_tmap
  let fmap = env#get_fmap
  let sort_of_typ = env#sort_of_typ
  let fun_of_str = env#fun_of_str
  let const_of_name = env#const_of_name
  let const_of_id = env#const_of_id 
  let all_mkkey_funs = env#all_mkkey_funs
  let vis = env#vis
  let so = env#so
  let hb = env#hb
  let ar = env#ar
  let sameobj = env#sameobj
  let objtyp = env#objtyp
  let objid = env#objid
  let replid = env#replid
  let ssn = env#ssn
  let txn = env#txn
  let currtxn = env#currtxn
  let seqno = env#seqno
  let oper = env#oper

  (*
   * The type of an effect
   *)
  class eff id = 
    object (self)
      val id: Ident.t = id
      val mutable oper: Ident.t = L.e_nop
      val mutable txn: Ident.t = L.txn_nop
      val mutable objid: string = ""
      val mutable replid: Ident.t = List.nth L.replids 0
      val mutable args: (string*string) list = []

      method get_id = id
      method set_oper op = oper <- op
      method get_oper = oper
      method set_txn t = txn <- t
      method get_txn = txn
      method set_objid i = objid <- i
      method get_objid = objid
      method set_replid i = replid <- i
      method get_replid = replid
      method set_arg (k:Ident.t) (v:Expr.expr) = 
        args <- args@[(Ident.name k, Expr.to_string v)]
      method set_args a = 
        args <- (List.map (fun (id,e) -> 
                            (Ident.name id, Expr.to_string e)) a)
      method get_args = args
      method to_string = 
        let args_str = String.concat "; " @@ 
              List.map (fun (a,b) -> a^":"^b) args in
        Printf.sprintf "{id:%s; oper:%s; txn:%s; objid:%s; \
                        replid:%s; args:{%s}}" 
                       (Ident.name id) (Ident.name oper) 
                       (Ident.name txn) objid (Ident.name replid) 
                       args_str

    end 
  (*
   * The type of a (high-level) model 
   *)

  type t = {effs: eff list; 
            vis: (eff*eff) list;
            so: (eff*eff) list;}

  (*
   * HACK!! TODO: Fixme
   *)
  let cached_model = ref None

  let eval e = match Model.eval (from_just !cached_model) e false with 
    | Some res -> res 
    | None -> failwith "Model.eval returned null!"

  (*
   * Returns true iff M |= e1 = e2, where M is the current model.
   *)
  let model_eq e1 e2 = 
    let eq_expr = e1 @= e2 in 
    let eq_res = eval eq_expr in
    let _ = if not (Expr.is_const eq_res && Bool.is_bool eq_res) 
        then printf "!!! %s -~> %s !!!\n" (Expr.to_string eq_expr)
            (Expr.to_string eq_res)
        else () in
    let _ = assert (Expr.is_const eq_res && Bool.is_bool eq_res) in
    Bool.is_true eq_res

  (*
   * Return a list of eff objects, one for each eff_const created
   * during specverify.
   *)
  let mk_effs () = 
    let eff_ids = match KE.find_same (Type.other_id Type.eff) ke with
      | Kind.Enum eff_consts -> List.rev @@ List.tl @@ List.rev
                                  eff_consts (* drop E_NOP *)
      | _ -> failwith "Modelparse.mk_effs: Unexpected!" in
    let new_effs = List.map (fun eff_id -> new eff(eff_id)) eff_ids in
      new_effs
  (*
   * Set the oper attribute for the given list of eff objects based 
   * on the model assignment.
   *)
  let set_opers effs = 
    let es = List.map (fun e -> const_of_id @@ e#get_id) effs in
    let operes = List.map (fun e -> eval (oper e)) es in
    let oper_type_def = KE.find_same (Type.other_id Type.oper) ke in
    let oper_ids = match oper_type_def with
      | Kind.Enum xs -> xs
      | _ -> failwith "Modelparse.set_opers: Unexpected!" in
    let oper_id_eq_to opere = 
      try 
        List.find (fun oper_id -> model_eq opere @@ 
                                  const_of_id oper_id) oper_ids
      with Not_found -> failwith "Modelparse.set_opers: \
                                  partial model?" in
    let oper_ids_eq_to_operes = List.map oper_id_eq_to operes in
    let _ = List.iter2 (fun e oper_id -> e#set_oper oper_id) 
                       effs oper_ids_eq_to_operes in
      effs
  (*
   * Set the replid attribute for the given list of eff objects based
   * on the model assignment.
   *)
  let set_replids (effs: eff list) = 
    let es = List.map (fun e -> const_of_id @@ e#get_id) effs in
    let replid_exprs = List.map (fun e -> replid e) es in
    let replid_type_def = KE.find_same 
                            (Type.other_id Type.replid) ke in
    let replids = match replid_type_def with
      | Kind.Enum xs -> xs
      | _ -> failwith "Modelparse.set_opers: Unexpected!" in
    let replid_eq_to replid_expr = 
      try 
        List.find (fun replid  -> model_eq replid_expr @@ 
                                  const_of_id replid) replids
      with Not_found -> failwith "Modelparse.set_replids: \
                                  partial model?" in
    let eff_replids = List.map replid_eq_to replid_exprs in
    let _ = List.iter2 (fun e replid -> e#set_replid replid) 
                       effs eff_replids in
      effs

  (*
   * Set the txn attribute for the given list of eff objects 
   * (i.e., the app function name that generated each effect). 
   *)
  let set_txns effs = 
    let es = List.map (fun e -> const_of_id @@ e#get_id) effs in
    let txnes = List.map (fun e -> eval (txn e)) es in
    let txn_type_def = KE.find_same (Type.other_id Type.txn) ke in
    let txn_ids = match txn_type_def with
      | Kind.Enum xs -> xs
      | _ -> failwith "Modelparse.set_opers: Unexpected!" in
    let txn_id_eq_to txne = 
      try 
        List.find (fun txn_id -> model_eq txne @@ 
                                  const_of_id txn_id) txn_ids
      with Not_found -> failwith "Modelparse.set_opers: \
                                  partial model?" in
    let txn_ids_eq_to_txnes = List.map txn_id_eq_to txnes in
    let _ = List.iter2 (fun eff txn_id -> eff#set_txn txn_id) 
                       effs txn_ids_eq_to_txnes in
      effs

  (*
   * Set the object id (objid attribute) for the given list of eff
   * objects based on the model assignment.
   *)
  let set_objids effs = 
    (*
     * ObjIds are of type Id, which is uninterpreted, hence assigned
     * by Z3 directly.
     *)
    let es = List.map (fun e -> const_of_id @@ e#get_id) effs in
    let objides = List.map (fun e -> eval (objid e)) es in
    let _ = List.iter2 (fun eff objide -> eff#set_objid @@
                                          Expr.to_string objide) 
                       effs objides in 
      effs

  (*
   * Set the args (attributes) for the given effect. 
   *)
  let set_args eff = 
    (*
     * Effect constructors (Cons.t) are accessible through VE.
     * Find the constructor C of eff (i.e., e.oper = C). C's
     * attributes are what we want.
     *)
    let Cons.T {args}= from_just @@ VE.fold_all 
        (fun id sv acc -> match sv with
           | S.EffCons (Cons.T{name} as cons) 
             when (Ident.name name = Ident.name eff#get_oper) -> 
               Some cons
           | _ -> acc) ve None in
    let accessor_ids = List.map fst args in
    (* Get Z3 functions corresponding to accessors *)
    let accessor_fs = List.map (fun acc_id -> fun_of_str @@
                                  Ident.name acc_id) accessor_ids in
    (* Evaluate the functions for each effect *)
    let e = const_of_id @@ eff#get_id in
    let accessor_vals = List.map 
        (fun f -> eval (mk_app f [e])) accessor_fs in
    let _ = eff#set_args @@ List.zip accessor_ids accessor_vals in
      eff

  (*
   * Set the args (attributes) for the given list of effects.
   *)
  let set_args effs = List.map set_args effs

  (*
   * Returns list of Effect pairs constituting the given relation in
   * the current model.
   *)
  let eval_rel rel effs = 
    List.filter 
      (fun (eff,eff') -> 
        let str = Ident.name eff#get_id in
        let str' = Ident.name eff'#get_id in 
        let e = const_of_id eff#get_id in
        let e' = const_of_id eff'#get_id in
        let rel_e_e' = rel(e,e') in
        let res = eval rel_e_e' in
        let _ = assert (Expr.is_const res && Bool.is_bool res) in
        (*let _ = if Bool.is_true res 
          then 
            printf "%s (%s,%s) is %s\n" 
              (Expr.to_string rel_e_e') str str' (Expr.to_string res)
          else () in*)
        Bool.is_true res) @@
      List.cross_product effs effs

  (*
   * ---------------- MODEL VISUALIZING ---------------
   *)    
  module ExecVertex = struct
    type t = eff
    let compare eff1 eff2 = Ident.compare eff1#get_id eff2#get_id
    let hash = Hashtbl.hash
    let equal eff1 eff2 = Ident.equal eff1#get_id eff2#get_id
  end 

  module ExecEdge = struct
    type t = string
    let compare = String.compare
    let default = "??"
  end

  module ExecGraph : 
  sig
    type t
    type node = eff
    type edge = eff*string*eff
    val create : unit -> t
    val add_vertex : t -> node -> unit
    val remove_vertex : t -> node -> unit
    val add_edge : t -> edge  -> unit
    val fold_edges : (edge -> 'a -> 'a) -> t -> 'a -> 'a
    val output_graph : out_channel -> t -> unit
  end= 
  struct
    type node = eff

    module DiGraph : Graph.Sig.I with type V.t = eff 
                                  and type V.label = eff 
                                  and type E.t = eff*string*eff 
                                  and type E.label = string
      = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled
            (ExecVertex)(ExecEdge)

    module Dot = Graph.Graphviz.Dot
      (struct
        type t = DiGraph.t 
        module V = DiGraph.V
        module E = DiGraph.E
        let iter_edges_e = DiGraph.iter_edges_e
        let iter_vertex = DiGraph.iter_vertex
        let edge_attributes (v1,e,v2)= match e with
          | "vis" -> [`Style `Dashed]
          | "so" -> [`Style `Solid]
          | _ -> failwith "Unexpected!!"
        let default_edge_attributes _ = []
        let get_subgraph _ = None
        let sanitize s = Str.global_replace 
                          (Str.regexp "!") "_" s
        let vertex_name (eff:V.t) = sanitize @@ Ident.name eff#get_id
        let vertex_label (eff:V.t) = 
          let f id = sanitize @@ Ident.name id in
          let g = sanitize in
          String.escaped @@ Printf.sprintf "%s: %s.%s(%s)\nTxn: %s"
            (f eff#get_id) (g eff#get_objid) (f eff#get_oper)
            (g @@ String.concat "," @@ List.map snd eff#get_args)
            (f @@ eff#get_txn)
        let vertex_attributes v = [`Label (vertex_label v)]
        let default_vertex_attributes _ = []
        let graph_attributes _ = []
       end)
    include DiGraph
    include Dot
    let create () = create ()
    (* 
     * add_edge should necessarily take a labeled edge.
     * Note: type edge = V.t*E.t*V.t = eff*string*eff
     *)
    let add_edge  = add_edge_e
    let fold_edges = fold_edges_e
  end

  let mk_exec_graph ({effs; vis; so}) = 
    let g = ExecGraph.create () in
    let _ = List.iter
        (fun (eff1,eff2) -> 
           ExecGraph.add_edge g (eff1,"vis",eff2)) vis in
    let _ = List.iter
        (fun (eff1,eff2) -> 
           ExecGraph.add_edge g (eff1,"so",eff2)) so in
    let _ = ExecGraph.output_graph 
            (open_out_bin "./Graphs/exec_graph.dot") g in
    ()

  let get_counterexample () = 
    let model = Z3.get_model () in 
    let _ = cached_model := Some model in
    (*let _ = 
      let so01 = so (const_of_name "E0", const_of_name "E1") in
      let res = from_just @@ Z3.Model.eval model so01 false  in
      printf "%s = %s\n" (Expr.to_string so01) (Expr.to_string res) in*)
    let _ = try Unix.mkdir "Models" 0o777 
            with Unix.Unix_error(Unix.EEXIST,_,_) -> () in
    let txn_id = vc.txn in
    let inv_id = vc.inv in
    let vc_name = (Ident.name txn_id)^"_" ^(Ident.name inv_id) in
    let out_chan = open_out @@ "Models/"^vc_name^".z3" in
    let _ = output_string out_chan @@ Z3.Model.to_string model in
    let string_of_rel eff_pairs = String.concat "; " @@ 
      List.map (fun (eff,eff') -> Printf.sprintf "(%s,%s)" 
                  (Ident.name eff#get_id) (Ident.name eff'#get_id))
               eff_pairs in
    let effs = set_args @@ (*set_replids @@*) set_objids 
                @@ set_txns @@ set_opers @@ mk_effs () in
    let vis_rel = eval_rel vis effs in
    let so_all_pairs = eval_rel so effs in
    let so_rel = reduce_transitive (module ExecVertex) so_all_pairs in
    (*let _ = printf "\nso forest:\n" in
    let _ = List.iter (fun l -> printf "  [%s]\n" 
                          (String.concat ", " @@ 
                            List.map (fun eff -> 
                                        Ident.name eff#get_id) l)) 
                      so_forest in*)
    (*let _ = List.iter (fun e -> printf "%s\n" @@ e#to_string)
                      effs in*)
    (*let _ = printf "---------- visibility ------\n" in
    let _ = printf "[%s]\n" @@ string_of_rel vis_rel in
    let _ = printf "---------- session order (all pairs) ------\n" in
    let _ = printf "[%s]\n" @@ string_of_rel so_all_pairs in
    let _ = printf "---------- session order ------\n" in
    let _ = printf "[%s]\n" @@ string_of_rel so_rel in*)
    let exec = {effs=effs; vis=vis_rel; so=so_rel} in
    let _ = mk_exec_graph exec in
      exec
end : T) 
