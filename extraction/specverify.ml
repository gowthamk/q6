open Utils
open Types
open Typedtree
open Rdtspec
open Specelab (* hiding doIt *)
open Speclang
module SV = SymbolicVal

type env = {ke:KE.t; te:TE.t; pe: Predicate.t list; ve:VE.t}

type vc_t = TE.t * Predicate.t * Predicate.t

(* type lhd = {new_te:TE.t; new_pe: Predicate.t list;  new_vcs: vc_t list} *)

let ppf = Format.std_formatter

(*
let lhd0 = {new_te = TE.empty; new_pe = []; new_vcs = []}

let (<+>) env res = {env with te=TE.merge env.te res.new_te;
                              pe = env.pe @ res.new_pe}
*)

(* 
 * OMGWTFBMC bound
 *)
let k =ref 2 (* will be overridden in doIt *)

let rec type_of_tyd ke tyd = 
  let open Path in
  let open Types in
  let f = type_of_tyd ke in
    match tyd with
      | Tarrow (_,te1,te2,_) -> Type.Arrow (f te1.desc, f te2.desc)
      | Ttuple [te1;te2] -> Type.Pair (f te1.desc, f te2.desc)
      | Tconstr (Pdot (Pident id,"t",_),[te],_) 
        when (Ident.name id = "List") -> Type.List (f te.desc)
      | Tconstr (Pident id,[te],_) 
        when (Ident.name id = "list") -> Type.List (f te.desc)
      | Tconstr (Pident id,[te],_) 
        when (Ident.name id = "option") -> Type.Option (f te.desc)
      | Tconstr (Pident id,[],_) 
        when (Ident.name id = "string") -> Type.String
      | Tconstr (Pident id,[],_) 
        when (Ident.name id = "int") -> Type.Int
      | Tconstr (Pident id,[],_) 
        when (Ident.name id = "bool") -> Type.Bool
      | Tconstr (Pident id,[],_) 
        when (Ident.name id = "unit") -> Type.Unit
      | Tconstr (Pdot (Pident id,"t",_),[],_) 
        when (Ident.name id = "Uuid") -> Type.uuid
      | Tconstr (Pdot (Pident id,t,_),[],_)  ->
          let alias = (Ident.name id)^"."^t in
          let Kind.Alias typ = try KE.find_name alias ke 
                    with Not_found -> 
                      failwith @@ "Type "^alias^" unknown\n" in
            typ
      | Tlink te -> f te.desc
      | Tconstr (Pdot (Pident id,s,_),[],_)  ->
          let _ = Printf.printf "Unknown Tconstr %s.%s\n" 
                    (Ident.name id) s in
          let _ = Printtyp.type_expr ppf {desc=tyd; level=0; id=0} in
            failwith "Unimpl."
      | _ -> 
          let _ = Printf.printf "Unknown type\n" in
          let _ = Printtyp.type_expr ppf {desc=tyd; level=0; id=0} in
            failwith "Unimpl."

let map_snd_opts = List.map (function (_,Some x) -> x
                               | _ -> failwith "Unexpected")
let gen_name name_base = 
  let count = ref 0 in
    fun () -> 
      let x = name_base^(string_of_int !count) in
        (count := !count + 1; x)

let fresh_eff_name = gen_name "!e"
let fresh_name = gen_name "!v"

module L = 
struct
  let objid = Ident.create "objid"
  let oper = Ident.create "oper"
  let vis = Ident.create "vis"
  let so = Ident.create "so"
  let mkkey_string = Ident.create "mkkey_string"
  let mkkey_UUID = Ident.create "mkkey_UUID"
  let mkkey = function "string" -> mkkey_string
    | "UUID" -> mkkey_UUID
    | _ -> failwith "mkkey not available"
end

module P = Predicate

let mk_new_effect (sv1,ty1) sv2 =
  let y = Ident.create @@ fresh_eff_name () in
  let sv_y = SV.Var y in
  let (Cons.T cons_t,args) = let open SV in match sv2 with 
    | NewEff (cons_t,Some (Record args)) -> (cons_t,args)
    | NewEff (cons_t,None) -> (cons_t,[])
    | _ -> failwith "doIt_append: unexpected sv2" in
  let mkkey_ty1 = L.mkkey (Type.to_string ty1) in
  let phi_1 = SV.Eq (SV.App (L.objid, [sv_y]),
                     SV.App (mkkey_ty1, [sv1])) in
  let phi_2 = SV.Eq (SV.App (L.oper, [sv_y]), 
                     SV.Var (cons_t.name)) in
  let doIt_arg (arg_id,arg_sv) = SV.Eq (SV.App (arg_id, [sv_y]), 
                                        arg_sv) in
  let phis_3 = List.map doIt_arg args in
  let conj = P.of_sv @@ SV.And (phi_1::phi_2::phis_3) in
  let _ = Printf.printf "New pred:\n%s\n" (P.to_string conj) in
    (y,conj)

let doIt_append env typed_sv1 sv2 =
  let (y,conj) = mk_new_effect typed_sv1 sv2 in
  let te' = TE.add y Type.eff env.te in
  let pe' = env.pe @ [conj] in
    {env with te=te'; pe=pe'}

let doIt_get env typed_sv1 sv2 = 
  let (y,conj_y) = mk_new_effect typed_sv1 sv2 in
  let ys = List.tabulate !k 
             (fun _ -> Ident.create @@ fresh_eff_name ()) in
  let vis (id1,id2) = SV.App (L.vis, [SV.Var id1;
                                      SV.Var id2]) in
  let vis_preds = List.map (fun yi -> vis(yi,y)) ys in
  let conj_ys = P.of_sv @@ SV.And vis_preds in
  let _ = Printf.printf "New pred(y):\n%s\n" (P.to_string conj_y) in
  let _ = Printf.printf "New pred(ys):\n%s\n" (P.to_string conj_ys) in
  let te' = List.fold_left (fun te y -> TE.add y Type.eff te)
              env.te (y::ys) in
  (* 
   * ys is the manifest prefix. We also need to create a list 
   * variable to serve as the unmanifest suffix.
   *)
  let l = Ident.create @@ fresh_name () in
  let te'' = TE.add l (Type.List Type.eff) te' in
  let pe' = env.pe @ [conj_y; conj_ys] in
  let env' = {env with te=te''; pe=pe'} in
  let ret_sv = SV.List (List.map (fun yi -> SV.Var yi) ys, 
                        Some (SV.Var l)) in
    (ret_sv,env')

let rec doIt_expr env (expr:Typedtree.expression) 
      : SV.t * env * vc_t list = 
  let open Path in
  let ret sv = (sv, env, []) in
  let doIt_exprs env exprs = 
    let (svs, (env',vcs)) = List.map_fold_left 
                              (fun (env,vcs) e -> 
                                let (sv,env',new_vcs) = doIt_expr env e in
                                  (sv, (env', vcs @ new_vcs))) 
                              (env,[]) exprs in
      (svs,env',vcs) in
  let is_table_mod id = 
    let tokens = Str.split (Str.regexp "_") (Ident.name id) in
      (List.length tokens >= 2) && (List.hd (List.rev tokens) = "table") in
  match expr.exp_desc with
    (* id *)
    | Texp_ident (Pident id,_,_) -> 
        let name = Ident.name id in
          begin
            try ret (VE.find_name name env.ve)
            with Not_found -> 
              try let _ = TE.find_name name env.te in 
                ret (SV.Var id)
              with Not_found -> failwith @@ name^" not found\n"
          end
    (* constant *)
    | Texp_constant const ->
        let open Asttypes in 
          (match const with 
             | Const_int i -> ret (SV.ConstInt i)
             | Const_string (s, None) -> ret (SV.ConstString s)
             | Const_string (s, Some s') -> ret (SV.ConstString (s^s'))
             | _ -> failwith "Texp_constant Unimpl.")
    (* e1::e2 *)
    | Texp_construct (_,cons_desc, [arge1; arge2]) 
      when (cons_desc.cstr_name = "::") -> 
        let (arg_sv1, env', vcs1) = doIt_expr env arge1 in
        let (arg_sv2, env'', vcs2) = doIt_expr env' arge2 in
        let sv = SV.cons (arg_sv1,arg_sv2) in
          (sv,env'',vcs1@vcs2)
        (* let (arg_svs, (env',vcs')) = 
          List.map_fold_left 
            (fun (env,vcs) arge -> 
               let (arg_sv,env',new_vcs) = doIt_expr env arge in
                  (arg_sv, (env', vcs @ new_vcs)))
            (env,[]) arg_exprs in *)
    (* [] *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "[]") -> ret (SV.nil)
    (* None *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "None") -> ret (SV.none)
    (* Some e *)
    | Texp_construct (_,cons_desc, [arge])
      when (cons_desc.cstr_name = "Some") -> 
        let (arg_v, env', vcs) = doIt_expr env arge in
          (SV.some arg_v, env', vcs)
    (* EffCons e  *)
    | Texp_construct (li_loc,cons_desc,arg_exprs) -> 
        let li = let open Asttypes in li_loc.txt in
        let cstr_name = String.concat "." @@ Longident.flatten li in
        let _ = Printf.printf "EffCons(%s)\n" cstr_name in
        let cstr_sv = try VE.find_name cstr_name env.ve 
                      with Not_found -> failwith @@ 
                              "Unknown constructor: "^cstr_name in
        let cons_t = match cstr_sv with 
          | SV.EffCons x -> x 
          | _ -> failwith "Texp_construct: Unexpected" in
        let (arg_svs,env',arg_vcs) = doIt_exprs env arg_exprs in
        let arg_sv_op = match arg_svs with
          | [] -> None | [arg_sv] -> Some arg_sv
          | _ -> failwith @@ cstr_name^" has more than 1 arg" in
        let sv = SV.NewEff (cons_t, arg_sv_op) in
          (sv,env',arg_vcs)
    (* {id1=e1; id2=e2; ..}*)
    | Texp_record (flds,None) -> 
        let fld_exprs = List.map (fun (_,_,z) -> z) flds in
        let (fld_svs,env',vcs) = doIt_exprs env fld_exprs in
        let id_of_ld ld = 
          let _ = Printf.printf "label name: %s\n" ld.lbl_name in
            Ident.create @@ ld.lbl_name in
        let fld_ids = List.map (fun (_,ld,_) -> id_of_ld ld) flds in
        let sv = SV.Record (List.combine fld_ids fld_svs) in
          (sv,env',vcs)
    | Texp_record (flds,Some e) -> failwith "Texp_record: Unimpl."
    (* Obj_table.append e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"append",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let _ = Printf.printf "processing append...\n" in
        let ([sv1;sv2],env',vcs) = doIt_exprs env [e1;e2] in
        let typ1 = type_of_tyd env.ke e1.exp_type.desc in
        let env'' = doIt_append env' (sv1,typ1) sv2 in
          (SV.ConstUnit, env'', vcs)
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let _ = Printf.printf "processing get...\n" in
        let ([sv1;sv2],env',vcs) = doIt_exprs env [e1;e2] in
        let typ1 = type_of_tyd env.ke e1.exp_type.desc in
        let (effs_sv, env'') = doIt_get env' (sv1,typ1) sv2 in
          (effs_sv, env'', vcs)
    (* let id = e1 in e2 *)
    | Texp_let (Asttypes.Nonrecursive, 
                [{vb_pat={pat_desc=Tpat_var (lhs_id,_)};vb_expr=e1}], e2) -> 
        let (sv1,env',vcs1) = doIt_expr env e1 in
        let ve' = VE.add lhs_id sv1 env'.ve in
        let (sv2,env'',vcs2) = doIt_expr {env' with ve=ve'} e2 in
          (sv2,env'',vcs1 @ vcs2)
    | _ -> failwith "Unimpl. expr"

(*
 * doIt_fun : env -> 
 *)
let doIt_fun (env: env) (Fun.T {args_t;body}) =
  let args_tys = 
    List.map (fun (id,tyd) -> (id, type_of_tyd env.ke tyd)) 
      args_t in
  let te' = List.fold_left (fun te (id,ty) -> TE.add id ty te)
              env.te args_tys in
  let (body_sv,env',vcs) = doIt_expr {env with te=te'} body in
    begin
      Printf.printf "body_sv:\n %s\n" (SV.to_string body_sv);
      failwith "Unimpl. fun"
    end

let doIt env rdt_spec k' = 
  let _ = k := k' in
  let Rdtspec.T {schemas; reads; writes; aux} = rdt_spec in
  let my_fun = List.find (fun (Fun.T x) -> 
                            Ident.name x.name = "do_test1")
                 writes in
  let _ = doIt_fun env my_fun in
    failwith "Unimpl. Specverify.doIt"
