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
let push () = Solver.push !solver
let pop () = Solver.pop !solver 1
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

let forallE6 f = 
  let s_Eff = Hashtbl.find tmap Type.eff in
  let sorts = [s_Eff; s_Eff; s_Eff; s_Eff; s_Eff; s_Eff] in
  let f' vars = match vars with 
    | [w; x; y; z; a; b] -> f w x y z a b | _ -> failwith "Unexpected!!!" in
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
  let asns = List.map expr_of_quantifier [(*forallE2 f;*) 
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
  let asns = List.map expr_of_quantifier [forallE4 f';
                                          (*forallE2 f;*) 
                                          forallE4 g; 
                                          forallE1 h;
                                          (*forallE2 i*)] in
    _assert_all asns

let assert_shcart_contracts () = 
  let rm = const_of_name "do_removeItemsFromCart" in
  let add = const_of_name "do_addItemsToCart" in
  let cart_add = const_of_name "Cart_AddItemsToCart" in
  let cart_rm = const_of_name "Cart_RemoveItemsFromCart" in
  let item_add = const_of_name "Item_AddToStock" in
  let item_rm = const_of_name "Item_RemoveFromStock" in
  let item_get = const_of_name "Item_ShowItem" in
  let cart_get = const_of_name "Cart_GetCartSummary" in
  let qty = fun_of_str "qty" in
  let f1 a b =
    mk_and [oper(a) @= cart_rm; 
            oper(b) @= cart_get; 
            txn(b) @= rm; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let f2 a b =
    mk_and [oper(a) @= item_rm; 
            oper(b) @= item_get; 
            txn(b) @= add; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let g1 a b c d =
    mk_and [oper(a) @= item_add; oper(b) @= item_get; 
            oper(c) @= item_rm; so(b,c);
            txn(b) @= add; 
            sametxn(b,c); 
            oper(d) @= item_get; 
            vis(a,b) ; vis(c,d); sameobj(a,d)] @=> vis(a,d) in
  let g2 a b c d =
    mk_and [oper(a) @= cart_add; oper(b) @= cart_get; 
            oper(c) @= cart_rm; so(b,c);
            txn(b) @= rm; 
            sametxn(b,c); 
            oper(d) @= cart_get; 
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
  let asns = List.map expr_of_quantifier [(*forallE2 f1;
                                          forallE2 f2; 
                                          forallE4 g1;
                                          forallE4 g2;*)
                                          forallE1 h;
                                          forallE2 i1;
                                          forallE2 i2] in
    _assert_all asns

let assert_tpcc_contracts () = 
  let nwordtxn = const_of_name "do_new_order_txn" in
  let ptxn = const_of_name "do_payment_txn" in
  let dtxn = const_of_name "do_delivery_txn" in
  let dget = const_of_name "District_Get" in
  let oget = const_of_name "Order_Get" in
  let olget = const_of_name "Orderline_Get" in
  let hget = const_of_name "History_Get" in
  let wget = const_of_name "Warehouse_Get" in
  let cget = const_of_name "Customer_Get" in
  let caddbal = const_of_name "Customer_AddBal" in
  let dincnoid = const_of_name "District_IncNextOID" in
  let oadd = const_of_name "Order_Add" in
  let oladd = const_of_name "Orderline_Add" in
  let olsetdel = const_of_name "Orderline_SetDeliveryDate" in
  let osetcarrier = const_of_name "Order_SetCarrier" in
  let waddytd = const_of_name "Warehouse_AddYTD" in
  let hadd = const_of_name "History_Append" in
  let oid = fun_of_str "o_id" in
  let ocid = fun_of_str "o_c_id" in
  let cid = fun_of_str "c_id" in
  let cdid = fun_of_str "c_d_id" in
  let cwid = fun_of_str "c_w_id" in
  let hcid = fun_of_str "h_c_id" in
  let hcdid = fun_of_str "h_c_d_id" in
  let hcwid = fun_of_str "h_c_w_id" in
  let olid = fun_of_str "ol_o_id" in
  let oldid = fun_of_str "ol_d_id" in
  let olwid = fun_of_str "ol_w_id" in
  let odid = fun_of_str "o_d_id" in
  let owid = fun_of_str "o_w_id" in
  let f11 a b c d = 
    mk_and [oper(a)@=dincnoid;
            oper(b)@=oadd;
            oper(c)@=dget;
            oper(d)@=oget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d);] @=> mk_or [mk_and [vis(b,d);vis(a,c)];
                                      mk_and [mk_not(vis(b,d));
                                              mk_not(vis(a,c))]] in
  let f11' a b =
    mk_and [oper(a) @= dincnoid; 
            oper(b) @= dget; 
            sameobj(a,b)] @=> (sametxn(a,b) @| vis(a,b)) in
  let f12 a b c d = 
    mk_and [oper(a)@=oadd;
            oper(b)@=oladd;
            oper(c)@=oget;
            oper(d)@=olget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> mk_or [mk_and [vis(b,d);vis(a,c)];
                                     mk_and [mk_not(vis(b,d));
                                             mk_not(vis(a,c))]] in
  let f12' a b = mk_and 
                  [(mk_app oid [a]) @= (mk_app oid [b]);
                   (mk_app odid [a]) @= (mk_app odid [b]);
                   (mk_app owid [a]) @= (mk_app owid [b])] @=> (a@=b) in
  let f23 a b c d = 
    mk_and [oper(a)@=waddytd;
            oper(b)@=hadd;
            oper(c)@=wget;
            oper(d)@=hget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> mk_or [mk_and [vis(b,d);vis(a,c)];
                                     mk_and [mk_not(vis(b,d));
                                             mk_not(vis(a,c))]] in
  let f31 a b c d = 
    mk_and [oper(a)@=caddbal;
            oper(b)@=hadd;
            oper(c)@=cget;
            oper(d)@=hget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> mk_or [mk_and [vis(b,d);vis(a,c)];
                                     mk_and [mk_not(vis(b,d));
                                             mk_not(vis(a,c))]] in
  let f31' a b c d e f =
    mk_and [oper(a)@=oadd;
            oper(b)@=oladd;
            (mk_app oid [a]) @= (mk_app olid [b]);
            oper(c)@=oget;
            oper(d)@=olget;
            so(c,d);
            currtxn(c);
            sametxn(c,d);
            oper(e)@=olget;
            oper(f)@=oget;
            so(e,f);
            mk_not(currtxn(e));
            sametxn(e,f)] @=> (mk_and [vis(a,c);vis(b,d)] @<=>
                              mk_and [vis(a,f);vis(b,e)]) in
  let f31'' a b = mk_and 
                [(mk_app cid [a]) @= (mk_app cid [b]);
                 (mk_app cdid [a]) @= (mk_app cdid [b]);
                 (mk_app cwid [a]) @= (mk_app cwid [b])] @=> (a@=b) in

  let f41 a b c d = 
    mk_and [oper(a)@=osetcarrier;
            oper(b)@=olsetdel;
            oper(c)@=oget;
            oper(d)@=olget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> (vis(b,d) @<=> vis(a,c)) in
  (*Since we're not dealing with Orderline set delivery date, we need to
    assert that the delivery transaction only handles one order at a time.*)
  let f31''' a b c = mk_and
                [oper(a)@=oadd;
                 oper(b)@=oadd;
                 oper(c)@=oget;
                 txn(c)@=dtxn;
                 vis(a,c);
                 vis(b,c)] @=> a@=b in
  let assertions = List.concat [[forallE4 f11;
                                 forallE2 f11';
                                 forallE4 f12;
                                 forallE2 f12';
                                 forallE4 f23;
                                 forallE4 f31;
                                 forallE6 f31';
                                 forallE2 f31'';
                                 forallE3 f31''';
                                 forallE4 f41];] in
  let asns = List.map expr_of_quantifier assertions in
    _assert_all asns

let assert_tpce_contracts () =
  let tget = const_of_name "Trade_Get" in
  let bget = const_of_name "Broker_Get" in
  let hget = const_of_name "Holding_Get" in
  let hsget = const_of_name "HoldingSummary_Get" in
  let tadd = const_of_name "Trade_AddTrade" in
  let tcmplt = const_of_name "Trade_SetCmpltAndComm" in
  let hadd = const_of_name "Holding_AddHolding" in
  (*let tr_txn = const_of_name "do_trade_order_res_txn" in*)
  let hsaddqty = const_of_name "HoldingSummary_AddHoldingQty" in
  let bincnum = const_of_name "Broker_AddCommision" in
  let baddcomm = const_of_name "Broker_AddCommision" in
  let tid = fun_of_str "t_id" in
  let f1 a b c d = 
    mk_and [oper(a)@=tcmplt;
            oper(b)@=bincnum;
            oper(c)@=tget;
            oper(d)@=bget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> (vis(b,d) @<=> vis(a,c)) in
  let f1' a b c =
    mk_and [oper(a)@=tadd;
            oper(b)@=tget;
            currtxn(b);
            sameobj(a,b);
            oper(c)@=tget;
            sameobj(a,c);
            notsametxn(a,c);
            vis(a,b)] @=> vis(a,c) in
  let f1'' a b =
    mk_and [mk_app tid [a]@=mk_app tid [b]; 
            oper(a)@=oper(b);
            oper(a)@=tadd] @=> a@=b in
  let f1''' a b =
    mk_and [oper(a)@=tcmplt;
            oper(b)@=tget;
            sameobj(a,b)] @=> sametxn(a,b) @| vis(a,b) in
  let f2 a b c d = 
    mk_and [oper(a)@=tcmplt;
            oper(b)@=baddcomm;
            oper(c)@=tget;
            oper(d)@=bget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> (vis(b,d) @<=> vis(a,c)) in
  let f3 a b c d = 
    mk_and [oper(a)@=hsaddqty;
            oper(b)@=hadd;
            oper(c)@=hsget;
            oper(d)@=hget;
            so(a,b);
            so(c,d);
            sameobj(a,c);
            sameobj(b,d)] @=> (vis(b,d) @<=> vis(a,c)) in
  let asns = List.map expr_of_quantifier [forallE4 f1;
                                          forallE3 f1';
                                          forallE2 f1'';
                                          forallE2 f1''';
                                          forallE4 f2;
                                          forallE4 f3] in
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
        vis(a, b) @| vis(b, a) @| (a@=b) in
  forallE2 f

let assert_paxos_contracts () = 
  let propose = const_of_name "Proposer_Propose" in
  let promise = const_of_name "Acceptor_Promise" in
  let accept = const_of_name "Acceptor_Accept" in
  let proposal_txn = const_of_name "do_proposer_action" in
  let ac_get = const_of_name "Acceptor_Get" in
  let pr_get = const_of_name "Proposer_Get" in
  let lr_get = const_of_name "Learner_Get" in
  let prev_val = fun_of_str "prev_vote_val" in
  let prev_round = fun_of_str "prev_vote_round" in
  let round = fun_of_str "round" in
  let value = fun_of_str "value" in
  let h_prev_v a = (mk_app prev_val [a]) @> (mk_numeral_i (0-1)) in
  let h_prev_r a = (mk_app prev_round [a]) @> (mk_numeral_i (0-1)) in
  let h_v a = (mk_app value [a]) @> (mk_numeral_i (0-1)) in
  let h_round a = (mk_app round [a]) @> (mk_numeral_i (0-1)) in
  let prop_uniq a b = mk_and [oper(a)@=propose;
                              oper(b)@=propose]
                      @=> ((mk_app round [a]) @!= (mk_app round [b])) @| a@=b in
  let f a b c d = 
    mk_and [mk_or [oper(d) @= ac_get; oper(d) @= pr_get;oper(d) @= lr_get]; 
            so(a,b); vis(b,c); so(c,d)(*); sameobj(a,d)*)] @=> vis(a,d) in
  let f1 a b =
    mk_and [oper(a) @= propose; 
            mk_or [oper(b) @= ac_get; oper(b) @= pr_get; oper(b) @= lr_get];
            txn(b) @= proposal_txn;
            (*sameobj(a,b)*)] @=> (sametxn(a,b) @| vis(a,b)) in
  let i a b =
    mk_and [oper(a) @= propose;
            notsametxn(a,b);
            currtxn(b)] @=> vis(a, b) in
  let asns = List.map expr_of_quantifier [forallE4 f] in
  let h_assertions = List.map forallE1 [h_prev_v;h_v; h_round;h_prev_r] in
  let asns = List.map expr_of_quantifier @@ 
                          List.concat [h_assertions;
                                      [forallE2 prop_uniq;
                                       forallE4 f;
                                       forallE2 i;
                                       forallE2 f1]] in
  _assert_all asns

let assert_contracts () = assert_tpcc_contracts ()

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
      | App (id,[v1]) when (Ident.name id = "not") -> mk_not (f v1)
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

let assert_consts names = 
  let s_preds = List.map (Hashtbl.find cmap) names in
  let conj = mk_and s_preds in
  _assert conj

let assert_prog prog = 
  _assert_all @@ List.map doIt_pred prog

let assert_neg_const name = 
  let s_pred = Hashtbl.find cmap name in
  _assert (mk_not s_pred)

exception VerificationFailure

let discharge vc = 
  let open VC in
  let txn_id = vc.txn in
  let vc_name = "VC_"^(Ident.name txn_id) in
  let out_chan = open_out @@ vc_name^".z3" in
  let pres = List.mapi (fun i _ -> 
                    Printf.sprintf "pre_%d" i) vc.pre in
  let posts = List.mapi (fun i _ -> 
                    Printf.sprintf "post_%d" i) vc.post in
    begin
      declare_types (vc.kbinds, vc.tbinds);
      declare_vars vc.tbinds;
      assert_axioms vc.kbinds;
      assert_contracts ();
      assert_prog vc.exec;
      (* declare_pred "pre" (List.hd vc.pre); *)
      List.iter2 declare_pred pres vc.pre;
      assert_consts pres;
      List.iter2 declare_pred posts vc.post;
      output_string out_chan @@ Solver.to_string !solver;
        printf "SMT VCs printed in %s.z3\n" vc_name;
      (*
       * Discharge post conditions one at a time.
       *)
      List.iteri (fun i post -> 
        (*
         * First print what's being done
         *)
        printf "\tChecking postcondition #%d... " i;
        output_string out_chan "(push)\n";
        output_string out_chan @@
                               "  (assert (not "^post^"))\n";
        output_string out_chan "  (check-sat)\n";
        output_string out_chan "  (get-model)\n";
        output_string out_chan "(pop)\n";
        flush_all();
        (*
         * Then do that
         *)
        push();
        assert_neg_const post;
        match check_sat () with
          | UNSATISFIABLE ->  printf "Passed\n"
          | SATISFIABLE -> (printf "Failed!\n"; 
                            raise VerificationFailure)
          | UNKNOWN -> failwith "Z3 timed out. Please increase \
                                 the timeout!"
        pop();) posts;
    end

let doIt vcs = 
  if not (Log.open_ "z3.log") then
    failwith "Log couldn't be opened."
  else
    let t1 = Sys.time () in
    List.iter (fun vc ->
      try
        printf "Verifying %s... \n" 
          (let open VC in Ident.name vc.txn);
        discharge vc;
        printf "%s Verified!\n" 
                (Ident.name vc.txn);
        (*Printf.printf "Resetting...\n";*)
        reset ();
        Gc.full_major ();
      with VerificationFailure -> 
        failwith "Verification failed!") vcs;
    let t2 = Sys.time () in
    printf "Verification took %fs\n" (t2-.t1);
