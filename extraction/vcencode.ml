open Utils
open Speclang
open Specelab
open Z3
open Z3.SMT
open Z3.Sort
open Z3.Expr
open Z3.Optimize
open Z3.Solver
open Z3.Symbol
open Z3.Datatype
open Z3.FuncDecl
open Z3.Boolean
open Z3.Arithmetic 
open Z3.Arithmetic.Integer
open Z3.Quantifier
module Solver = Z3.Solver
module OptSolver = Z3.Optimize
module Model = Z3.Model
module Symbol = Z3.Symbol
module Optimize = Z3.Optimize
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Quantifier = Z3.Quantifier
module Expr = Z3.Expr
module Constructor = Z3.Datatype.Constructor
module VC = Vc

let mk_new_ctx () = 
  let cfg = [("model", "true"); ("proof", "false")] in
    mk_context cfg

let ctx = ref @@ mk_new_ctx ()
let solver = ref @@ mk_solver !ctx None 
let (cmap : (string,Expr.expr) Hashtbl.t) = Hashtbl.create 211
let (tmap : (Type.t,Sort.sort) Hashtbl.t) = Hashtbl.create 47
let (fmap : (string,FuncDecl.func_decl) Hashtbl.t) = Hashtbl.create 47


let reset () = 
  begin
    ctx := mk_new_ctx ();
    solver := mk_solver !ctx None;
    Hashtbl.clear cmap;
    Hashtbl.clear tmap;
    Hashtbl.clear fmap;
  end

let sort_of_typ typ = try Hashtbl.find tmap typ 
                      with Not_found ->
                        (printf "%s not found in tmap" 
                           (Type.to_string typ); raise Not_found)
let fun_of_str str = try Hashtbl.find fmap str
                      with Not_found ->
                        (printf "%s not found in fmap" str;
                         raise Not_found)
(*
 * Z3 API for the current ctx
 *)
let sym s = Symbol.mk_string !ctx s
let mk_app f args = mk_app !ctx f args
let mk_int_sort () = Int.mk_sort !ctx
let mk_bool_sort () = Bool.mk_sort !ctx
let mk_int i = Int.mk_numeral_i !ctx i
let mk_uninterpreted_s s = mk_uninterpreted_s !ctx s
let mk_const_s str sort = Expr.mk_const_s !ctx str sort
let mk_constructor_s a b c d e = mk_constructor_s !ctx a b c d e
let mk_sort_s a b = mk_sort_s !ctx a b
let mk_func_decl_s name arg_sorts res_sort = 
  mk_func_decl_s !ctx name arg_sorts res_sort
let mk_and conjs = mk_and !ctx conjs
let mk_or conjs = mk_or !ctx conjs
let mk_eq e1 e2 = mk_eq !ctx e1 e2
let mk_not e = mk_not !ctx e
let _assert e = Solver.add !solver [e]
let _assert_all e = Solver.add !solver e

let vis (e1,e2) = mk_app (fun_of_str "vis") [e1; e2]
let so (e1,e2) = mk_app (fun_of_str "so") [e1; e2]
let hb (e1,e2) = mk_app (fun_of_str "hb") [e1; e2]
let sameobj (e1,e2) = mk_app (fun_of_str "sameobj") [e1; e2]
let objtyp e = mk_app (fun_of_str "objtyp") [e]
let objid e = mk_app (fun_of_str "objid") [e]
let (@=>) e1 e2 = mk_implies !ctx e1 e2
let (@<=>) e1 e2 = mk_iff !ctx e1 e2
let (@&) e1 e2 = mk_and [e1; e2]
let (@|) e1 e2 = mk_or [e1; e2]
let (@=) e1 e2 = mk_eq e1 e2
let (!@) e = mk_not e

let forall sorts f = 
  let n = List.length sorts in
  let names = List.tabulate n 
                (fun i -> sym @@ "a"^(string_of_int i)) in
  let vars = List.tabulate n 
               (fun i -> mk_bound !ctx (n-i-1) 
                           (List.nth sorts i)) in
  let body = f vars in
    mk_forall !ctx sorts names body None [] [] None None

let forallE1 f = 
  let s_Eff = Hashtbl.find tmap Type.eff in
  let sorts = [s_Eff] in
  let f' vars = match vars with 
    | [x] -> f x | _ -> failwith "Unexpected!" in
    forall sorts f' 

let forallE2 f = 
  let s_Eff = Hashtbl.find tmap Type.eff in
  let sorts = [s_Eff; s_Eff] in
  let f' vars = match vars with 
    | [x; y] -> f x y | _ -> failwith "Unexpected!!" in
    forall sorts f' 

let forallE3 f = 
  let s_Eff = Hashtbl.find tmap Type.eff in
  let sorts = [s_Eff; s_Eff; s_Eff] in
  let f' vars = match vars with 
    | [x; y; z] -> f x y z | _ -> failwith "Unexpected!!!" in
    forall sorts f' 

let declare_enum_type (ty:Type.t) (consts: Ident.t list) =
  let mk_cstr e = 
    let name = Ident.name e in 
      mk_constructor_s name (sym @@ "is"^name) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap ty s_ty;
    List.iter (fun (c,s_c) -> 
                 Hashtbl.add cmap (Ident.name c) s_c)
      (List.zip consts s_consts);
    printf "%s added\n" (Type.to_string ty);
  end

let declare_variant_type (ty:Type.t) (consts: Cons.t list) =
  let mk_cstr (Cons.T {name; recognizer}) = 
      mk_constructor_s (Ident.name name) 
        (sym @@ Ident.name recognizer) [] [] [] in
  let cstrs = List.map mk_cstr consts in
  let s_ty = mk_sort_s (Type.to_string ty) cstrs in
  let s_consts = List.map (fun f -> mk_app f []) @@
                      Datatype.get_constructors s_ty in
  begin
    Hashtbl.add tmap ty s_ty;
    List.iter (fun (Cons.T {name},s_c) -> 
                 Hashtbl.add cmap (Ident.name name) s_c)
      (List.zip consts s_consts);
    printf "%s added\n" (Type.to_string ty);
  end

let declare_types (ke,te) =
  begin
    Hashtbl.add tmap Type.Int (mk_int_sort ());
    Hashtbl.add tmap Type.Bool (mk_bool_sort ());
    Hashtbl.add tmap Type.String (mk_uninterpreted_s "Stringe");
    KE.iter (fun tyid kind -> 
               let tyname () = Type._of @@ Ident.name tyid in
                 match kind with
                   | Kind.Variant consts -> 
                       declare_variant_type (tyname ()) consts
                   | Kind.Enum consts -> 
                       declare_enum_type (tyname ()) consts
                   | Kind.Extendible consts ->
                       declare_enum_type (tyname ()) !consts
                   | _ -> ()) ke;
    (* If the type is not already mapped by tmap, map it to an 
     * uninterpreted sort (including option and list types) *)
    let rec add_if_unknown typ = let f = add_if_unknown in 
      match typ with | Type.Arrow (t1,t2) -> (f t1; f t2)
        | Type.Int | Type.Bool | Type.String | Type.Unit -> ()
        | _ -> if Hashtbl.mem tmap typ then () 
               else let sort_name = Str.strip_ws (Type.to_string typ) in
                    let _ = printf "%s added\n" sort_name in
                    let sort = mk_uninterpreted_s sort_name in
                      Hashtbl.add tmap typ sort in
      TE.iter (fun _ typ -> add_if_unknown typ) te;
  end

let declare_vars te = 
  let rec uncurry_arrow = function 
      Type.Arrow (t1, (Type.Arrow (_,_) as t2)) ->
        (fun (x,y) -> (t1::x,y)) (uncurry_arrow t2)
    | Type.Arrow (t1,t2) -> ([t1],t2)
    | _ -> failwith "uncurry_arrow called on a non-arrow type" in
  let declare_fun name typ = 
    let (arg_typs,res_typ) = uncurry_arrow typ in
    let (arg_sorts,res_sort) = (List.map sort_of_typ arg_typs, 
                                sort_of_typ res_typ) in
    let func_decl = mk_func_decl_s name arg_sorts res_sort in
    let _ = printf "%s being added\n" name in
      Hashtbl.add fmap name func_decl in
  let declare_const name typ = 
    let sort = sort_of_typ typ in
    let const_decl = mk_const_s name sort in
      Hashtbl.add cmap name const_decl in
    TE.iter (fun id typ -> let name = Ident.name id in 
               match typ with
                 | Type.Arrow _ -> declare_fun name typ
                 | Type.Unit -> ()
                 | _ -> declare_const name typ) te

let assert_axioms () =
  (* sameobj *)
  let sameobj_def = forallE2 
                      (fun a b -> 
                         sameobj(a,b) @=> 
                           ((objtyp(a) @= objtyp(b)) @&
                            (objid(a) @= objid(b)))) in
  (* so is transitive *)
  let so_trans = forallE3 
                   (fun a b c -> 
                      (so(a,b) @& so(b,c)) @=> so(a,c)) in
  (* vis => sameobj *)
  let vis_sameobj = forallE2 
                      (fun a b -> vis(a,b) @=> sameobj(a,b)) in
  (* hb is (vis U so)+ *)
  let hb_def1 = forallE2
                  (fun a b -> 
                     (vis(a,b) @| so(a,b)) @=> hb(a,b)) in
  let hb_def2 = forallE3 
                  (fun a b c -> 
                     (hb(a,b) @& hb(b,c)) @=> hb(a,c)) in
  (* hb is acyclic *)
  let hb_acyclic = forallE1 (fun a -> mk_not @@ hb(a,a)) in
  let asns = List.map (fun q -> expr_of_quantifier q) 
               [sameobj_def; so_trans; vis_sameobj;
                hb_def1; hb_def2; hb_acyclic] in
    _assert_all asns

let declare_inv inv = 
  failwith "declare_inv: Unimpl."

let discharge (txn_id, vc) = 
  let open VC in
    begin
      declare_types (vc.kbinds, vc.tbinds);
      declare_vars vc.tbinds;
      assert_axioms ();
      Printf.printf "*****  CONTEXT ******\n";
      print_string @@ Solver.to_string !solver;
      Printf.printf "\n*********************\n";
      declare_inv vc.inv;
    end

let doIt vcs = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let _ = List.iter discharge vcs in
    begin
      Printf.printf "Disposing...\n";
      Gc.full_major ();
    end
