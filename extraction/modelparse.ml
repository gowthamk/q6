open Utils
open Speclang
open Vc
module S = SymbolicVal

module type T = 
sig
  val get_counterexample : unit -> unit
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

  class eff id = 
    object (self)
      val id: Ident.t = id
      val mutable oper: Ident.t = L.e_nop
      val mutable txn: Ident.t = L.txn_nop
      val mutable objid: string = ""
      val mutable args: (string*string) list = []

      method get_id = id
      method set_oper op = oper <- op
      method set_txn t = txn <- t
      method set_objid i = objid <- i
      method set_arg (k:Ident.t) (v:Expr.expr) = 
        args <- (Ident.name k, Expr.to_string v)::args
      method to_string = 
        Printf.sprintf "{id:%s; oper:%s; txn:%s; objid:%s}" 
                       (Ident.name id) (Ident.name oper) 
                       (Ident.name txn) objid
    end 
 
  let eval e = match Model.eval (Z3.get_model ()) e true with 
    | Some res -> res 
    | None -> failwith "Model.eval returned null!"

  (*
   * Returns true iff M |= e1 = e2, where M is the current model.
   *)
  let model_eq e1 e2 = 
    let eq_res = eval (e1 @= e2) in
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
   * Set the args for the given effect
   *)
  let set_args eff = 
    (*
     * Effect constructors (Cons.t) are accessible through VE.
     * Constructor attributes are what we want.
     *)
    let eff_cons = VE.fold_all 
        (fun id sv acc -> match sv with
           | S.EffCons cons -> cons::acc
           | _ -> acc) ve [] in
    let accessors = List.concat @@ List.map 
        (fun (Cons.T {args}) -> List.map fst args) 
        eff_cons in
    ()

  let get_counterexample () = 
    let model = Z3.get_model () in 
    let _ = try Unix.mkdir "Models" 0o777 
            with Unix.Unix_error(Unix.EEXIST,_,_) -> () in
    let txn_id = vc.txn in
    let inv_id = vc.inv in
    let vc_name = (Ident.name txn_id)^"_" ^(Ident.name inv_id) in
    let out_chan = open_out @@ "Models/"^vc_name^".z3" in
    let _ = output_string out_chan @@ Z3.Model.to_string model in
    let effs = set_objids @@ set_txns @@ set_opers @@ mk_effs () in
    let _ = List.iter (fun e -> printf "%s\n" @@ e#to_string)
                      effs in
      ()
end : T)
