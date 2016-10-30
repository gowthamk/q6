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

let rec type_of_tye ke (tye : type_expr) = 
  let open Path in
  let open Types in
  let f = type_of_tye ke in
    match tye.desc with
      | Tvar aop -> 
        let a_name = Misc.mk_tvar_name aop tye.id in
        let not_found () =
          begin
            Printf.printf "Kind of %s not found" a_name; 
            raise Not_found
          end in
        let knd = try KE.find_name a_name ke 
                  with Not_found -> not_found () in
          (match knd with | Kind.Alias typ -> typ
            | _ -> failwith "type_of_tye: Unexpected")
      | Tarrow (_,te1,te2,_) -> Type.Arrow (f te1, f te2)
      | Ttuple [te1;te2] -> Type.Pair (f te1, f te2)
      | Tconstr (Pdot (Pident id,"t",_),[te],_) 
        when (Ident.name id = "List") -> Type.List (f te)
      | Tconstr (Pident id,[te],_) 
        when (Ident.name id = "list") -> Type.List (f te)
      | Tconstr (Pident id,[te],_) 
        when (Ident.name id = "option") -> Type.Option (f te)
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
      | Tconstr (Pdot (Pident id,"eff",l),[],s) ->
          (* If there exists an id type for this module, 
           * then this must be a TABLE_TYPE module.  *)
          begin
            try f {desc=Tconstr (Pdot (Pident id,"id",l),[],s);
                   id=tye.id; level=tye.level} 
            with Not_found -> failwith "Unknown eff type";
            Type.oper
          end
      | Tconstr (Pdot (Pident id,t,_),[],_)  ->
          let alias = (Ident.name id)^"."^t in
          let Kind.Alias typ = try KE.find_name alias ke 
                    with Not_found -> 
                      begin
                        print_string ("Type "^alias^" unknown\n");
                        raise Not_found
                      end in
            typ
      | Tlink te -> f te
      | Tconstr (Pdot (Pident id,s,_),[],_)  ->
          let _ = Printf.printf "Unknown Tconstr %s.%s\n" 
                    (Ident.name id) s in
          let _ = Printtyp.type_expr ppf tye  in
            failwith "Unimpl."
      | _ -> 
          let _ = Printf.printf "Unknown type\n" in
          let _ = Printtyp.type_expr ppf tye in
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

let rec doIt_fun_app env (Fun.T fun_t) tydbinds arg_svs =
  let _ = if List.length fun_t.args_t = List.length arg_svs then ()
          else failwith "Partial application unimpl."  in
  (*
   * (KE['a -> T], TE, PE, VE[x -> v2] | e --> v <| (TE',PE',C)
   * --------------------------------------------------------
   *    (KE, TE, PE, VE) |- (\x.e) T v2 --> v <| (TE',PE',C)
   *
   * The nature of symbolic execution guarantees that T is always a 
   * concrete type, and v2 and v are symbolic values.
   *)
  let typbinds = List.map (fun (a,tyd) -> 
                             (Ident.create a, 
                              Kind.Alias (type_of_tye env.ke @@ 
                                          Misc.to_tye tyd)))
                   tydbinds in
  let bind_typs ke = List.fold_left 
                       (fun ke (a,typ) -> KE.add a typ ke)
                       ke typbinds in
  let argbinds = List.map2 (fun (arg,_) sv -> (arg,sv)) 
                   fun_t.args_t arg_svs in
  let bind_args ve = List.fold_left 
                       (fun ve (arg,sv) -> VE.add arg sv ve) 
                       ve argbinds in
  let bind_self ve =
    (* Rec function M.f is referred as f in its body *)
    let qualif_name = Ident.name fun_t.name in
    let unqualif_name = List.last @@ 
                          Str.split (Str.regexp ".") qualif_name in
      VE.add (Ident.create unqualif_name) (SV.Fun (Fun.T fun_t)) ve in
  let xke = List.fold_left (fun ke f -> f ke) env.ke
              [bind_typs] in
  let xve = List.fold_left (fun ve f -> f ve) env.ve
              [bind_args; if fun_t.rec_flag then bind_self 
                          else (fun ve -> ve)] in
  let xenv = {env with ke=xke; ve=xve} in
  let (body_sv,xenv',vcs) = doIt_expr xenv fun_t.body in 
  (* restore original KE and VE *)
  let env' = {xenv' with ke=env.ke; ve=env.ve} in
    (body_sv, env', vcs)

and doIt_expr env (expr:Typedtree.expression) 
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
    | Texp_ident (path,_,_) -> 
        let names = Path.all_names path in
        let name = String.concat "." names in
          begin
            try ret (VE.find_name name env.ve)
            with Not_found -> 
              try let _ = TE.find_name name env.te in 
                ret (SV.Var (Ident.create name))
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
        let typ1 = type_of_tye env.ke e1.exp_type in
        let env'' = doIt_append env' (sv1,typ1) sv2 in
          (SV.ConstUnit, env'', vcs)
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let _ = Printf.printf "processing get...\n" in
        let ([sv1;sv2],env',vcs) = doIt_exprs env [e1;e2] in
        let typ1 = type_of_tye env.ke e1.exp_type in
        let (effs_sv, env'') = doIt_get env' (sv1,typ1) sv2 in
          (effs_sv, env'', vcs)
    (* f e *) (* (\x.e) e *)
    | Texp_apply (e1, largs) -> 
        let strf = Format.str_formatter in
        let _ = Format.fprintf strf "The type of fn being applied:\n" in
        let _  = Printtyp.type_expr strf e1.exp_type in
        let _ = Printf.printf "%s\n" @@ Format.flush_str_formatter () in
        let (sv1,env',vcs1) = doIt_expr env e1 in
        let e2s = map_snd_opts largs in
        let (sv2s,env'',vcs2) = doIt_exprs env' e2s in
        let (res_sv, res_env, res_vcs) = match sv1 with
          | SV.Var id -> (SV.App (id,sv2s), env'', vcs1 @ vcs2)
          | SV.Fun (Fun.T fun_t) -> 
              (*
               * OCaml has no explicit type applications. We reconstruct
               * type arguments by unifying function type with function
               * expression type.
               *)
              let arrow_tye = Misc.to_tye @@ 
                              Misc.curry (List.map snd fun_t.args_t)
                                 fun_t.res_t in
              let tyd_binds = Misc.unify_tyes arrow_tye e1.exp_type in
              let (res_sv, res_env, vcs3) = 
                    doIt_fun_app env'' (Fun.T fun_t) tyd_binds sv2s in
                (res_sv, res_env, vcs1 @ vcs2 @ vcs3)
          | _ -> failwith "Texp_apply: Unexpected" in
          (res_sv, res_env, res_vcs)
    (* let id = e1 in e2 *)
    | Texp_let (Asttypes.Nonrecursive, 
                [{vb_pat={pat_desc=Tpat_var (lhs_id,_)};vb_expr=e1}], e2) -> 
        let (sv1,env',vcs1) = doIt_expr env e1 in
        let ve' = VE.add lhs_id sv1 env'.ve in
        let (sv2,env'',vcs2) = doIt_expr {env' with ve=ve'} e2 in
          (sv2,env'',vcs1 @ vcs2)
    (* \x.e *)
    | Texp_function (_,[case],_) -> 
        let (args,body) = Misc.extract_lambda case in
        let open Types in
        let arrow_t = expr.exp_type.desc in
        (*let _ = Printtyp.type_expr Format.std_formatter 
                      expr.exp_type in *)
        let (arg_ts,res_t) = Misc.uncurry_arrow arrow_t in
        let (fun_t:Fun.t) = Fun.make ~rec_flag: false
                            ~args_t: (List.zip args arg_ts) 
                            ~res_t: res_t ~body: body 
                            (* This is default, yet doesn't 
                             * compile if removed. Fixit. *)
                            ~name: Fun.anonymous in
          ret @@ SV.Fun fun_t
    | Texp_function (_,cases,_) -> 
        failwith "Lambdas with multiple cases Unimpl."
    | Texp_match (scrutinee,cases,[],_) ->
        let (scru_sv, env', vcs1) = doIt_expr env scrutinee in
        let exptyp = type_of_tye env.ke expr.exp_type in
        let _ = Printf.printf "Type of the match expression:\n" in
        let _ = Printf.printf "%s\n" @@ Type.to_string exptyp in
        let (sv,env'',vcs2)  = let open SV in match scru_sv with
          | List ([],Some l) -> 
              (* create a fresh var of expr type and return *)
              failwith "Unimpl."
          | List (conc,abs) -> doIt_list_cases env' (conc,abs) cases
          | _ -> failwith "Texp_match Unimpl." in
          (sv,env'',vcs1 @ vcs2)
    | Texp_match (_,_,ex_cases,_) -> 
        failwith "Match expressions with exception cases Unimpl."
    | _ -> failwith "Unimpl. expr"

and doIt_list_cases env (conc,abs) cases = 
  failwith "doIt_list_cases: Unimpl."

let doIt_fun (env: env) (Fun.T {args_t;body}) =
  let (args_tys : (Ident.t * Type.t) list)= 
    List.map (fun (id,tyd) -> 
                (id, type_of_tye env.ke (Misc.to_tye tyd))) 
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
