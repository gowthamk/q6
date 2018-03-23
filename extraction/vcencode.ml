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

let fresh_bv_name = gen_name "bv" 
let fresh_bv () = Ident.create @@  fresh_bv_name ()

type  bv_t = {id:Ident.t;const:Z3.Expr.expr; name:string;}

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
let const_of_name n = try Hashtbl.find cmap n 
                      with Not_found -> (printf "%s not found in cmap" n; 
                                         raise Not_found)
let const_of_id id = const_of_name @@ Ident.name id
let all_mkkey_funs () = Hashtbl.fold (fun name func acc -> 
                          if Str.string_match (Str.regexp "^mkkey_") name 0
                          then func::acc else acc) fmap []
(*let new_bv ?sort () = 
  let s = match sort with | Some s -> s
                          | _ -> raise Not_found in
  let bv_name = fresh_bv_name () in
  let bv_id = Ident.create bv_name in
  let bv_const = mk_const_s bv_name s in
    {name=bv_name; id=bv_id; const=bv_const}*)

(*
 * Z3 API for the current ctx
 *)
let sym s = Symbol.mk_string !ctx s
let mk_app f args = mk_app !ctx f args
let mk_int_sort () = Int.mk_sort !ctx
let mk_bool_sort () = Bool.mk_sort !ctx
let mk_numeral_i i = Int.mk_numeral_i !ctx i
let mk_uninterpreted_s s = mk_uninterpreted_s !ctx s
let mk_const_s str sort = Expr.mk_const_s !ctx str sort
let mk_constructor_s a b c d e = mk_constructor_s !ctx a b c d e
let mk_sort_s a b = mk_sort_s !ctx a b
let mk_func_decl_s name arg_sorts res_sort = 
  mk_func_decl_s !ctx name arg_sorts res_sort
let mk_and conjs = mk_and !ctx conjs
let mk_or conjs = mk_or !ctx conjs
let mk_eq e1 e2 = mk_eq !ctx e1 e2
let mk_gt e1 e2 = mk_gt !ctx e1 e2
let mk_lt e1 e2 = mk_lt !ctx e1 e2
let mk_ge e1 e2 = mk_ge !ctx e1 e2
let mk_le e1 e2 = mk_le !ctx e1 e2
let mk_not e = mk_not !ctx e
let mk_true () = mk_true !ctx
let mk_false () = mk_false !ctx
let mk_ite e1 e2 e3 = mk_ite !ctx e1 e2 e3
let mk_distinct es = mk_distinct !ctx es
let mk_add es = mk_add !ctx es
let mk_sub es = mk_sub !ctx es
let mk_mul es = mk_mul !ctx es
let _assert e = Solver.add !solver [e]
let _assert_all e = Solver.add !solver e
let check_sat () = Solver.check !solver []

let (@=>) e1 e2 = mk_implies !ctx e1 e2
let (@<=>) e1 e2 = mk_iff !ctx e1 e2
let (@&) e1 e2 = mk_and [e1; e2]
let (@|) e1 e2 = mk_or [e1; e2]
let (@=) e1 e2 = mk_eq e1 e2
let (@<) e1 e2 = mk_lt e1 e2
let (@>) e1 e2 = mk_gt e1 e2
let (@>=) e1 e2 = mk_ge e1 e2
let (@<=) e1 e2 = mk_le e1 e2
let (@!=) e1 e2 = mk_not (e1 @= e2)
let (!@) e = mk_not e
let vis (e1,e2) = mk_app (fun_of_str "vis") [e1; e2]
let so (e1,e2) = mk_app (fun_of_str "so") [e1; e2]
let hb (e1,e2) = mk_app (fun_of_str "hb") [e1; e2]
let ar (e1,e2) = mk_app (fun_of_str "ar") [e1; e2]
let ar_id (id1,id2) = mk_app (fun_of_str "ar_id") [id1; id2]
let ar_oper (op1,op2) = mk_app (fun_of_str "ar_oper") [op1; op2]
let sameobj (e1,e2) = mk_app (fun_of_str "sameobj") [e1; e2]
let objtyp e = mk_app (fun_of_str "objtyp") [e]
let objid e = mk_app (fun_of_str "objid") [e]
let replid e = mk_app (fun_of_str "replid") [e]
let ssn e = mk_app (fun_of_str "ssn") [e]
let txn e = mk_app (fun_of_str "txn") [e]
let currtxn e = mk_app (fun_of_str "currtxn") [e]
let sametxn (e1,e2) = (txn(e1) @= txn(e2)) @& (ssn(e1) @= ssn(e2))
let notsametxn (e1,e2) = mk_not ((txn(e1) @= txn(e2)) @& (ssn(e1) @= ssn(e2)))
let seqno e = mk_app (fun_of_str "seqno") [e]
let oper e = mk_app (fun_of_str "oper") [e]

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

let forallE4 f = 
  let s_Eff = Hashtbl.find tmap Type.eff in
  let sorts = [s_Eff; s_Eff; s_Eff; s_Eff] in
  let f' vars = match vars with 
    | [w; x; y; z] -> f w x y z | _ -> failwith "Unexpected!!!" in
    forall sorts f' 

let forallId1 f = 
  let s_Id = Hashtbl.find tmap Type.id in
  let sorts = [s_Id] in
  let f' vars = match vars with 
    | [x] -> f x | _ -> failwith "Unexpected!" in
    forall sorts f' 

let forallId2 f = 
  let s_Id = Hashtbl.find tmap Type.id in
  let sorts = [s_Id; s_Id] in
  let f' vars = match vars with 
    | [x; y] -> f x y | _ -> failwith "Unexpected!!" in
    forall sorts f' 

let forallId3 f = 
  let s_Id = Hashtbl.find tmap Type.id in
  let sorts = [s_Id; s_Id; s_Id] in
  let f' vars = match vars with 
    | [x; y; z] -> f x y z | _ -> failwith "Unexpected!!!" in
    forall sorts f' 

let forallO1 f = 
  let s_Oper = Hashtbl.find tmap Type.oper in
  let sorts = [s_Oper] in
  let f' vars = match vars with 
    | [x] -> f x | _ -> failwith "Unexpected!" in
    forall sorts f' 

let forallO2 f = 
  let s_Oper = Hashtbl.find tmap Type.oper in
  let sorts = [s_Oper; s_Oper] in
  let f' vars = match vars with 
    | [x; y] -> f x y | _ -> failwith "Unexpected!!" in
    forall sorts f' 

let forallO3 f = 
  let s_Oper = Hashtbl.find tmap Type.oper in
  let sorts = [s_Oper; s_Oper; s_Oper] in
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
  end

let declare_enum_type (ty:Type.t) (consts: Ident.t list) =
  let tyname = Type.to_string ty in
  let s = mk_uninterpreted_s tyname in
  let consts = List.map (Ident.name) consts in
  let tags = List.map (fun c -> 
                         mk_const_s c s) consts in
  let s_univ_cstr = expr_of_quantifier @@ 
    forall [s] (fun [a] -> mk_or 
                   (List.map (fun tag -> a @= tag) tags)) in
  let s_distinct_cstr = mk_distinct tags in
  begin
    Hashtbl.replace tmap ty s;
    List.iter2 (Hashtbl.replace cmap) consts tags;
    _assert s_univ_cstr;
    _assert s_distinct_cstr;
    (*dprintf !_ddecls "%s added\n" tyname;
    bv_reset ();*)
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
                 (*let _ = printf "%s added\n" (Ident.name name) in*)
                 Hashtbl.add cmap (Ident.name name) s_c)
      (List.zip consts s_consts);
    (*printf "%s added\n" (Type.to_string ty);*)
  end

let declare_extendible_type (ty:Type.t) (consts: Ident.t list) =
  let sort = mk_uninterpreted_s (Type.to_string ty) in
  let s_consts = List.map (fun c -> 
                         mk_const_s (Ident.name c) sort) consts in
  let distinct_asn = mk_distinct s_consts in
    begin
      Hashtbl.add tmap ty sort;
      List.iter (fun (c,s_c) -> 
                   Hashtbl.add cmap (Ident.name c) s_c)
        (List.zip consts s_consts);
      _assert distinct_asn;
      (*printf "%s added\n" (Type.to_string ty);*)
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
                       declare_extendible_type (tyname ()) !consts
                   | _ -> ()) ke;
    (* If the type is not already mapped by tmap, map it to an 
     * uninterpreted sort (including option and list types) *)
    let rec add_if_unknown typ = let f = add_if_unknown in 
      match typ with | Type.Arrow (t1,t2) -> (f t1; f t2)
        | Type.Int | Type.Bool | Type.String | Type.Unit -> ()
        | _ -> if Hashtbl.mem tmap typ then () 
               else let sort_name = Str.strip_ws (Type.to_string typ) in
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

let assert_arbitration_axioms ke = 
  (* Arbitration relations are total orders *)
  let ar_irrefl = forallE1 (fun a -> mk_not @@ ar(a,a)) in
  let ar_trans = forallE3 
                  (fun a b c -> 
                     (ar(a,b) @& ar(b,c)) @=> ar(a,c)) in
  let ar_total = forallE2 (fun a b -> 
                    mk_or [ar(a,b); ar(b,a); a @= b]) in
  let aro_irrefl = forallO1 (fun a -> mk_not @@ ar_oper(a,a)) in
  let aro_trans = forallO3 
                  (fun a b c -> 
                     (ar_oper(a,b) @& ar_oper(b,c)) 
                            @=> ar_oper(a,c)) in
  let aro_total = forallO2 (fun a b -> 
                    mk_or [ar_oper(a,b); ar_oper(b,a); a @= b]) in     
  let ari_irrefl = forallId1 (fun a -> mk_not @@ ar_id(a,a)) in
  let ari_trans = forallId3 
                  (fun a b c -> 
                     (ar_id(a,b) @& ar_id(b,c)) 
                            @=> ar_id(a,c)) in
  let ari_total = forallId2 (fun a b -> 
                    mk_or [ar_id(a,b); ar_id(b,a); a @= b]) in
  (* concretizing arbitration *)
  let eff_consts = match KE.find_name "Eff" ke with
                    | Kind.Enum es -> es
                    | _ -> failwith "Unexpected!" in
  let s_effs = List.map (const_of_id) eff_consts in
  let (_,s_eff_pairs) = 
        List.fold_left (fun (pre,acc) cur -> 
                              (cur,(pre,cur)::acc)) 
        (List.hd s_effs,[]) 
        (List.tl s_effs) in
  let ar_of_effs = mk_and @@ List.rev_map ar s_eff_pairs in
  let oper_consts = match KE.find_name "Oper" ke with
                     | Kind.Enum os -> os
                     | _ -> failwith "Unexpected!" in
  let s_opers = List.map (const_of_id) oper_consts in
  let (_,s_oper_pairs) = 
        List.fold_left (fun (pre,acc) cur -> 
                              (cur,(pre,cur)::acc)) 
        (List.hd s_opers,[]) 
        (List.tl s_opers) in
  let ar_of_opers = mk_and @@ List.rev_map ar_oper s_oper_pairs in
  let ar_aro_ari =  forallE2
        (fun e1 e2 -> 
          let (oe1,oe2) = (oper e1, oper e2) in
          let (ie1,ie2) = (objid e1, objid e2) in
          ar(e1,e2) @=> mk_or [ar_oper(oe1,oe2); 
                               mk_and [oe1 @= oe2; 
                                       (*ar_id(ie1,ie2)*)]]) in
  let ar_q_axioms = [ar_irrefl; ar_trans; ar_total;
                     aro_irrefl; aro_trans; aro_total;
                     (*ari_irrefl; ari_trans; ari_total;*)
                     ar_aro_ari] in
  let ar_qf_axioms = [ar_of_effs; ar_of_opers] in
  let ar_axioms = (List.map expr_of_quantifier ar_q_axioms) 
                    @ ar_qf_axioms in
  _assert_all ar_axioms


let assert_mkey_axioms () = 
  let mkkeys = all_mkkey_funs () in 
  let bijection f a b = ((mk_app f [a]) @= (mk_app f [b])) @=> (a @= b) in
  let mkkey_bijections = 
    List.map (fun mkkey_f -> 
                let sorts = match FuncDecl.get_domain mkkey_f with
                  | [dom] -> [dom; dom] 
                  | _ -> failwith "mkkey_bijections: Unexpected" in
                  forall sorts (function [a;b] -> bijection mkkey_f a b
                                  | _ -> failwith "Impossible!")) mkkeys in
  let mkkey_axioms = List.map expr_of_quantifier @@ 
                      mkkey_bijections in
  _assert_all mkkey_axioms

let assert_nop_axioms () = 
  let s_NOP = const_of_id (Cons.name Cons.nop) in 
  let s_ENOP = const_of_id (L.e_nop) in
  let s_ssn_nop = const_of_id (L.ssn_nop) in
  let s_txn_nop = const_of_id (L.txn_nop) in
  (* _ENOP is the only NOP effect *)
  let e_not_nop = expr_of_quantifier @@ 
          forallE1 (fun a -> 
            (oper(a) @= s_NOP) @<=> (a @= s_ENOP)) in
  (* ssn(_ENOP) = _nop_ssn *)
  let enop_ssn = ssn(s_ENOP) @= s_ssn_nop in
  (* txn(_ENOP) = _nop_txn *)
  let enop_txn = txn(s_ENOP) @= s_txn_nop in
  let nop_axioms = [e_not_nop; enop_ssn; enop_txn] in
  _assert_all nop_axioms

let assert_so_axioms () = 
  let s_NOP = const_of_id (Cons.name Cons.nop) in 
  (* seq. nos are non-negative *)
  let seqno_pos = forallE1 (fun a -> seqno(a) @>= (mk_numeral_i 0)) in
  (* so *)
  let so_def = forallE2 
                 (fun a b -> 
                    so(a,b) @<=> mk_and [oper(a) @!= s_NOP; 
                                         oper(b) @!= s_NOP;
                                         ssn(a) @= ssn(b); 
                                         seqno(a) @< seqno(b)]) in
  (* so is transitive *)
  let so_trans = forallE3 
                   (fun a b c -> 
                      (so(a,b) @& so(b,c)) @=> so(a,c)) in
  let so_axioms = List.map expr_of_quantifier @@ 
                  [seqno_pos; so_def; so_trans] in
  _assert_all so_axioms

let assert_vis_axioms () = 
  let s_NOP = const_of_id (Cons.name Cons.nop) in 
  (* sameobj *)
  let sameobj_def = forallE2 
                      (fun a b -> 
                         sameobj(a,b) @<=> mk_and 
                                            [oper(a) @!= s_NOP; 
                                             oper(b) @!= s_NOP;
                                             objtyp(a) @= objtyp(b);
                                             objid(a) @= objid(b) ]) in
  (* vis => sameobj *)
  let vis_sameobj = forallE2 
                      (fun a b -> vis(a,b) @=> sameobj(a,b)) in
  (* vis is irrefl *)
  let vis_irrefl = forallE1 (fun a -> mk_not @@ vis(a,a)) in
  (* vis is anti-symmetric *)
  let vis_antisym = forallE2 
                    (fun a b -> (vis(a,b) @& vis(b,a)) @=> a @=b) in
  (* replica-local vis is a total-order *)
  let repl_local_vis_total = forallE2 
      (fun a b -> (replid(a) @= replid(b)) 
                      @=> mk_or [vis(a,b); vis(b,a); a @= b]) in
  let vis_axioms = List.map expr_of_quantifier @@
                   [sameobj_def; vis_sameobj; 
                    vis_irrefl; vis_antisym] in
  _assert_all vis_axioms

let assert_hb_axioms () = 
  (* hb is (vis U so)+ *)
  let hb_def1 = forallE2
                  (fun a b -> 
                     (vis(a,b) @| so(a,b)) @=> hb(a,b)) in
  let hb_def2 = forallE3 
                  (fun a b c -> 
                     (hb(a,b) @& hb(b,c)) @=> hb(a,c)) in
  (* hb is irrefl *)
  let hb_irrefl = forallE1 (fun a -> mk_not @@ hb(a,a)) in
  let hb_axioms = List.map expr_of_quantifier @@
                   [hb_def1; hb_def2; hb_irrefl] in
    _assert_all @@ hb_axioms

let assert_axioms ke =
  begin
    assert_nop_axioms ();
    assert_so_axioms ();
    assert_vis_axioms ();
    assert_hb_axioms ();
    assert_mkey_axioms ();
    assert_arbitration_axioms ke;
  end
                   

let assert_mb_contracts () = 
  let gt = const_of_name "Tweet_Get" in
  let f a b c d = 
    mk_and [oper(d) @= gt; so(a,b); 
            vis(b,c); so(c,d); sameobj(a,d)] @=> vis(a,d) in
  let asns = List.map expr_of_quantifier [forallE4 f] in
    _assert_all asns

let assert_ba_contracts () =
  let do_withdraw = const_of_name "do_withdraw" in
  (*let do_txn = const_of_name "do_txn" in*)
  let wd = const_of_name "BA_Withdraw" in
  let dp = const_of_name "BA_Deposit" in
  let gb = const_of_name "BA_GetBalance" in
  let amt = fun_of_str "amt" in
  (* Every withdraw is visible to getbalance. *)
  let f a b =
    mk_and [oper(a) @= wd; 
            oper(b) @= gb; 
            txn(b) @= do_withdraw; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let g a b c d =
    mk_and [oper(a) @= dp; oper(b) @= gb; 
            oper(c) @= wd; so(b,c);
            txn(b) @= do_withdraw; 
            sametxn(b,c); 
            oper(d) @= gb; 
            vis(a,b) ; vis(c,d); sameobj(a,d)] @=> vis(a,d) in
  (* Additional high-level invariant: ∀e. amt(e) >= 0 *)
  let h a = (mk_app amt [a]) @>= (mk_numeral_i 0) in
  (* Every withdraw is visible to the current transaction's getbalance *)
  let i a b =
    mk_and [oper(a) @= wd;
            notsametxn(a,b);
            currtxn(b)] @=> vis(a, b) in
  let asns = List.map expr_of_quantifier [forallE2 f; 
                                          forallE4 g; 
                                          forallE1 h;
                                          forallE2 i] in
    _assert_all asns

let assert_rubis_contracts () =
  let do_withdraw = const_of_name "do_withdraw_wallet" in
  let wd = const_of_name "Wallet_WithdrawFromWallet" in
  let dp = const_of_name "Wallet_DepositToWallet" in
  let gb = const_of_name "Wallet_GetBalance" in
  let amt = fun_of_str "amt" in
  let gt = const_of_name "Bids_GetBid" in
  let f' a b c d = 
    mk_and [oper(d) @= gt; so(a,b); 
            vis(a,c); so(c,d); 
            sameobj(a,c);sameobj(b,d)] @=> vis(a,d) in
  (* Every withdraw is visible to getbalance. *)
  let f a b =
    mk_and [oper(a) @= wd; 
            oper(b) @= gb; 
            txn(b) @= do_withdraw; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let g a b c d =
    mk_and [oper(a) @= dp; oper(b) @= gb; 
            oper(c) @= wd; so(b,c);
            txn(b) @= do_withdraw; 
            sametxn(b,c); 
            oper(d) @= gb; 
            vis(a,b) ; vis(c,d); sameobj(a,d)] @=> vis(a,d) in
  (* Additional high-level invariant: ∀e. amt(e) >= 0 *)
  let h a = (mk_app amt [a]) @>= (mk_numeral_i 0) in
  (* Every withdraw is visible to the current transaction's getbalance *)
  let i a b =
    mk_and [oper(a) @= wd;
            notsametxn(a,b);
            currtxn(b)] @=> vis(a, b) in
  let asns = List.map expr_of_quantifier [forallE2 f; 
                                          forallE4 g; 
                                          forallE4 f';
                                          forallE1 h;
                                          forallE2 i] in
    _assert_all asns

let assert_shcart_contracts () = 
  let rm = const_of_name "do_removeItemsFromCart" in
  let add = const_of_name "do_addItemsToCart" in
  let cart_add = const_of_name "Cart_AddItemsToCart" in
  let cart_rm = const_of_name "Cart_RemoveItemsFromCart" in
  let item_add = const_of_name "Item_AddToStock" in
  let item_rm = const_of_name "Item_RemoveFromStock" in
  let item_sh = const_of_name "Item_ShowItem" in
  let cart_sm = const_of_name "Cart_GetCartSummary" in
  let qty = fun_of_str "qty" in
  let f1 a b =
    mk_and [oper(a) @= cart_rm; 
            oper(b) @= cart_sm; 
            txn(b) @= rm; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let f2 a b =
    mk_and [oper(a) @= item_rm; 
            oper(b) @= item_sh; 
            txn(b) @= add; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let g1 a b c d =
    mk_and [oper(a) @= item_add; oper(b) @= item_sh; 
            oper(c) @= item_rm; so(b,c);
            txn(b) @= add; 
            sametxn(b,c); 
            oper(d) @= item_sh; 
            vis(a,b) ; vis(c,d); sameobj(a,d)] @=> vis(a,d) in
  let g2 a b c d =
    mk_and [oper(a) @= cart_add; oper(b) @= cart_sm; 
            oper(c) @= cart_rm; so(b,c);
            txn(b) @= rm; 
            sametxn(b,c); 
            oper(d) @= cart_sm; 
            vis(a,b) ; vis(c,d); sameobj(a,d)] @=> vis(a,d) in
  let h a = (mk_app qty [a]) @>= (mk_numeral_i 0) in
  let i1 a b =
    mk_and [oper(a) @= item_rm;
            notsametxn(a,b);
            currtxn(b)] @=> vis(a, b) in
  let i2 a b =
    mk_and [oper(a) @= cart_rm;
            notsametxn(a,b);
            currtxn(b)] @=> vis(a, b) in
  let asns = List.map expr_of_quantifier [forallE2 f1;
                                          forallE2 f2; 
                                          forallE4 g1; 
                                          forallE4 g2;
                                          forallE1 h;
                                          forallE2 i1;
                                          forallE2 i2] in
    _assert_all asns

let assert_tpcc_contracts () = 
  let nwordtxn = const_of_name "do_new_order_txn" in
  let ptxn = const_of_name "do_payment_txn" in
  let dget = const_of_name "District_Get" in
  let oget = const_of_name "Order_Get" in
  let olget = const_of_name "Orderline_Get" in
  let dsetnoid = const_of_name "District_SetNextOID" in
  let oadd = const_of_name "Order_Add" in
  let oladd = const_of_name "Orderline_Add" in
  let wsetytd = const_of_name "Warehouse_SetYTD" in
  let dsetytd = const_of_name "District_SetYTD" in
  let dgetytd = const_of_name "District_GetYTD" in
  let wgetytd = const_of_name "Warehouse_GetYTD" in
  let hget = const_of_name "History_Get" in
  let hadd = const_of_name "History_Append" in
  let f a b c d =
    mk_and [(*oper(a) @= dsetnoid;*)
            txn(a) @= nwordtxn;
            (*oper(b) @= dget;
            oper(c) @= oadd;
            oper(d) @= oget;*)
            vis(a, b);
            so(a, c);
            so(b, d);
            sameobj(a, b);
            sameobj(c, d);
            sametxn(a,c)] @=> vis(c,d) in
  let g a b c d = 
    mk_and [(*oper(a) @= dsetytd;
            oper(b) @= wsetytd;
            oper(c) @= dgetytd;
            oper(d) @= wgetytd;*)
            txn(a) @= ptxn;
            sametxn(a,b);
            so(b, a);
            so(d, c);
            sameobj(a, c);
            sameobj(b, d);
            sametxn(c, d);
            vis(b, d)] @=> vis(a, c) in
  (*let h a b c d = 
    mk_and [oper(a) @= dsetytd;
            oper(b) @= hadd;
            oper(c) @= dgetytd;
            oper(d) @= hget;
            txn(a) @= ptxn;
            sametxn(a,b);
            so(a, b);
            so(c, d);
            sameobj(a, c);
            sameobj(b, d);
            sametxn(c, d);
            vis(a, c)] @=> vis(b, d) in*)
  (*let g a b = (mk_app ts [a]) @!= (mk_app ts [b]) in*)
  let asns = List.map expr_of_quantifier [forallE4 f; forallE4 g(*); forallE4 h*)] in
    _assert_all asns

let mk_cc op = 
  let f a b = mk_and [oper(b)@=op;
          hb(a, b);
          sameobj(a, b)] @=> vis(a, b) in
  forallE2 f

let mk_sc op op_list = 
  let f a b = 
      let op_cond = List.map (fun op1 -> oper(a)@=op1) op_list in
      mk_and [mk_or op_cond;
        oper(b)@=op;
        sameobj(a, b)] @=> 
        vis(a, b) @| vis(b, a) (*@| (a@=b)*) in
  forallE2 f

(*let assert_paxos_contracts () = 
  let op1 = const_of_name "Acceptor_Accept" in
  let op2 = const_of_name "Proposer_Ack" in
  let op3 = const_of_name "Acceptor_PrepareRequest" in
  let op4 = const_of_name "Proposer_PrepareResponse" in
  let op5 = const_of_name "Proposer_GetSummary" in
  let op6 = const_of_name "Acceptor_SetPromise" in
  let op7 = const_of_name "Proposer_AcceptRequested" in
  let op8 = const_of_name "Acceptor_Accepted" in
  let op9 = const_of_name "Acceptor_GetSummary" in
  let txn1 = const_of_name "do_proposal_response" in
  let n  = fun_of_str "n" in
  let v  = fun_of_str "v" in
  let prop_id  = fun_of_str "proposal_id" in
  let h_n a = (mk_app n [a]) @>= (mk_numeral_i 0) in
  let h_v a = (mk_app v [a]) @>= (mk_numeral_i 0) in
  let h_prop_id a = (mk_app prop_id [a]) @>= (mk_numeral_i 0) in
  let h_assertions = List.map forallE1 [h_n; h_v; h_prop_id] in
  let acc_assertions = mk_sc op9 [op1; op3; op6; op8] in
  let prop_assertions = 
  let sc_assertions = List.map mk_sc [(*op1;op2;op3;*)(*op4;op5;op6;op7;op8;*)op9] in
  let assertions = List.concat [h_assertions; sc_assertions] in
  let asns = List.map expr_of_quantifier assertions in
  _assert_all asns*)

let assert_contracts () = assert_shcart_contracts ()

(*
let assert_contracts () = ()
   *)
(*let assert_contracts () = assert_mb_contracts ()*)
(*
 * Encoding
 *)
module P = Predicate
module S = SymbolicVal

let rec doIt_sv sv = 
  let open S in 
  let f = doIt_sv in 
    match sv with 
      | Var id -> const_of_id id
      | App (id,svs) when (Ident.name id = "+") -> mk_add (List.map f svs)
      | App (id,svs) when (Ident.name id = "-") -> mk_sub (List.map f svs)
      | App (id,svs) when (Ident.name id = "*") -> mk_mul (List.map f svs)
      | App (id,[v1;v2]) when (Ident.name id = "=") -> (f v1) @= (f v2)
      | App (id,[v1;v2]) when (Ident.name id = "<") -> (f v1) @< (f v2)
      | App (id,[v1;v2]) when (Ident.name id = "<=") -> (f v1) @<= (f v2)
      | App (id,[v1;v2]) when (Ident.name id = ">") -> (f v1) @> (f v2)
      | App (id,[v1;v2]) when (Ident.name id = ">=") -> (f v1) @>= (f v2)
      | App (id,svs) -> mk_app (fun_of_str @@ Ident.name id)
                          (List.map f svs) 
      | Eq (v1,v2) -> (f v1) @= (f v2)
      | Lt (v1,v2) -> (f v1) @< (f v2)
      | Gt (v1,v2) -> (f v1) @> (f v2)
      | Not v -> mk_not @@ f v
      | And vs -> mk_and @@ List.map f vs
      | Or vs -> mk_or @@ List.map f vs
      | ConstInt i -> mk_numeral_i i
      | ConstBool true -> mk_true ()
      | ConstBool false -> mk_false ()
      | ITE (v1,v2,v3) -> mk_ite (f v1) (f v2) (f v3)
      | _ -> failwith @@ "doIt_sv: Unimpl. "^(S.to_string sv)

let rec doIt_pred p = match p with
  | P.BoolExpr v -> doIt_sv v
  | P.If (t1,t2) -> (doIt_pred t1) @=> (doIt_pred t2)
  | P.Iff (t1,t2) -> (doIt_pred t1) @<=> (doIt_pred t2)
  | P.Forall (ty,f) -> expr_of_quantifier @@
      forall [sort_of_typ ty] 
        (fun exprs -> match exprs with 
           | [expr] -> 
               let bv = fresh_bv () in
               let _ = Hashtbl.add cmap (Ident.name bv) expr in
               let p = doIt_pred @@ f bv in
               let _ = Hashtbl.remove cmap (Ident.name bv) in
                 p
           | _ -> failwith "doIt_pred: Unexpected")

let declare_pred name p =
  let s_pred = mk_const_s name (sort_of_typ Type.Bool) in
  let e_pred = doIt_pred p in
    begin
      Hashtbl.add cmap name s_pred;
      _assert @@ s_pred @<=> e_pred 
    end

let assert_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert s_pred

let assert_prog prog = 
  _assert_all @@ List.map doIt_pred prog

let assert_neg_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert (mk_not s_pred)

let discharge (txn_id, vc) = 
  let open VC in
  let vc_name = "VC_"^(Ident.name txn_id)(*fresh_vc_name ()*) in
  let out_chan = open_out @@ vc_name^".z3" in
    begin
      declare_types (vc.kbinds, vc.tbinds);
      declare_vars vc.tbinds;
      assert_axioms vc.kbinds;
      assert_contracts ();
      assert_prog vc.prog;
      declare_pred "pre" vc.pre;
      declare_pred "post" vc.post;
      assert_const "pre";
      assert_neg_const "post";
      output_string out_chan @@ Solver.to_string !solver;
      output_string out_chan "(check-sat)\n";
      output_string out_chan "(get-model)\n";
      printf "Context printed in %s.z3\n" vc_name;
      flush_all ();
      Printf.printf "Time before execution of check_sat: %fs\n" (Sys.time());
      check_sat ()
    end

let doIt vcs = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let _ = List.map (fun vc ->
      let res = discharge vc in
      let _ = reset () in
      begin
        (match res with 
          | SATISFIABLE -> printf "SAT\n"
          | UNSATISFIABLE -> 
              printf "Verified!\n" 
                (*(Ident.name @@ fst @@ vc)*)
          | UNKNOWN -> printf "UNKNOWN\n");
        Printf.printf "Disposing...\n";
        Printf.printf "Time after execution of check_sat: %fs\n" (Sys.time());
      end
    ) vcs in
    Gc.full_major ()
