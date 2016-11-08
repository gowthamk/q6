open Utils
open Types
open Typedtree
open Rdtspec
open Specelab
open Speclang
module SV = SymbolicVal
module P = Predicate
module VC = Vc

exception Inconsistency

type env_t = (KE.t * TE.t * Predicate.t list * VE.t)
type env = {ssn: Ident.t; seqno:int; ke:KE.t; 
            te:TE.t; pe: Predicate.t list; ve:VE.t}

(* Symbolic Trace *)
type st_t = TE.t * Predicate.t list

let ppf = Format.std_formatter

let pervasives = [("Pervasives.@@", "@@"); 
                  ("Pervasives.raise", "raise"); 
                  ("Uuid.create", "Uuid.create");
                  ("Pervasives.+", "+"); 
                  ("Pervasives.-", "-");
                  ("Pervasives.>", ">");
                  ("Pervasives.>=", ">=");
                  ("Pervasives.<", "<");
                  ("Pervasives.<=", "<=");]

let printf = Printf.printf

(* 
 * OMGWTFBMC bound
 *)
let k =ref 2 (* will be overridden in doIt *)

let not_found msg = (Printf.printf "%s\n" msg; raise Not_found)

let is_none_pat = function
    (Tpat_construct (_,{cstr_name},[])) -> cstr_name = "None"
  | _ -> false

let is_some_pat = function
    (Tpat_construct (_,{cstr_name},_)) -> cstr_name = "Some"
  | _ -> false

let find_none_case cases = try List.find (fun case -> 
                            is_none_pat case.c_lhs.pat_desc) cases
                           with Not_found -> not_found "None case not found"

let find_some_case cases = try List.find (fun case -> 
                            is_some_pat case.c_lhs.pat_desc) cases
                           with Not_found -> not_found "Some case not found"
           

let (--) te1 te2 = 
  TE.fold_name 
      (fun id typ diff_te -> 
         try (ignore @@ TE.find_name (Ident.name id) te2; 
              diff_te) 
         with Not_found -> 
           TE.add id typ diff_te)
      te1 TE.empty

let doIt_under_grd env grd doIt = 
  let xpe = (P.of_sv grd)::env.pe in
  let xenv = {env with pe=xpe} in
  let (v,xenv',vcs) = doIt xenv in
  let new_ps = List.take ((List.length xenv'.pe) - 
                          (List.length xpe)) xenv'.pe in
  (*
   * Condition new predicates in PE and restore original VE.
   *)
  let pe' = (List.map (fun new_p -> 
                         P._if (P.of_sv grd, new_p)) new_ps)
            @ env.pe in
  let env' = {xenv' with pe=pe'; ve=env.ve}  in
    (v, env', vcs)

let mk_vc env grd = 
  let assumps = (List.concat @@ List.map 
                           (function P.BoolExpr v -> [v]
                              | _ -> []) env.pe) in
  (*let _ = printf "-- Assumps are: %s --\n" 
    (String.concat ", " @@ List.map SV.to_string assumps) in*)
  let conseqP = 
    P.of_sv @@ SV.simplify assumps grd in
  let new_vc = (env.te, env.pe, conseqP) in
  (* 
   * Assume that VC is valid for further analyis.
   *)
  let pe' = conseqP::env.pe in
    ({env with pe=pe'}, new_vc)

let rec type_of_tye ke (tye : type_expr) = 
  let open Path in
  let open Types in
  let f = type_of_tye ke in
    match tye.desc with
      | Tvar aop -> 
        let a_name = Misc.mk_tvar_name aop tye.id in
        let msg = "Kind of %s not found" in
        let knd = try KE.find_name a_name ke 
                  with Not_found -> not_found msg in
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
                      not_found ("Type "^alias^" unknown\n") in
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
let fresh_uuid_name = gen_name "!uuid"

let mk_new_effect env (sv1,ty1) sv2 =
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
  let objtyp = Ident.create @@ 
               match Str.split (Str.regexp "_") 
                       (Ident.name cons_t.name) with
                 | x::y::xs -> x
                 | _ -> failwith "Unexpected form of EffCons name" in
  let phi_3 = SV.Eq (SV.App (L.objtyp, [sv_y]), 
                     SV.Var objtyp) in
  let phi_4 = SV.Eq (SV.App (L.ssn, [sv_y]), 
                     SV.Var env.ssn) in
  let phi_5 = SV.Eq (SV.App (L.seqno, [sv_y]), 
                     SV.ConstInt env.seqno) in
  let doIt_arg (arg_id,arg_sv) = SV.Eq (SV.App (arg_id, [sv_y]), 
                                        arg_sv) in
  let phis_6 = List.map doIt_arg args in
  let conj = P.of_sv @@ SV.And (phi_1::phi_2::phi_3::phi_4
                                ::phi_5::phis_6) in
  let _ = Printf.printf "New pred:\n%s\n" (P.to_string conj) in
    (y,conj)

let doIt_append env typed_sv1 sv2 =
  let (y,conj) = mk_new_effect env typed_sv1 sv2 in
  let te' = TE.add y Type.eff env.te in
  let pe' = conj::env.pe in
  let seqno' = env.seqno + 1 in
    {env with seqno=seqno';te=te'; pe=pe'}

let doIt_get env typed_sv1 sv2 = 
  let (y,conj_y) = mk_new_effect env typed_sv1 sv2 in
  let ys = List.tabulate !k 
             (fun _ -> Ident.create @@ fresh_eff_name ()) in
  let vis (id1,id2) = SV.App (L.vis, [SV.Var id1;
                                      SV.Var id2]) in
  let vis_preds = List.map (fun yi -> vis(yi,y)) ys in
  let conj_ys = P.of_sv @@ SV.And vis_preds in
  (* Since vis(a,b) => samobj(a,b) => objid(a) = objid(b), we 
   * don't have to assert it separately. *)
  let te' = List.fold_left (fun te y -> TE.add y Type.eff te)
              env.te (y::ys) in
  (* 
   * ys is the manifest prefix. We also need to create a list 
   * variable to serve as the unmanifest suffix.
   *)
  let l = Ident.create @@ fresh_name () in
  let te'' = TE.add l (Type.List Type.eff) te' in
  let pe' = conj_y::conj_ys::env.pe  in
  let seqno' = env.seqno + 1 in
  let env' = {env with seqno=seqno'; te=te''; pe=pe'} in
  let ret_sv = SV.List (List.map (fun yi -> SV.Var yi) ys, 
                        Some (SV.Var l)) in
    (ret_sv,env')

let rec doIt_fun_app env (Fun.T fun_t) tyebinds arg_svs =
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
  let typbinds = List.map (fun (a,tye) -> 
                             (Ident.create a, 
                              Kind.Alias (type_of_tye env.ke tye)))
                   tyebinds in
  (* Special casing for symbolic lists *)
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
                          Str.split (Str.regexp "\.") qualif_name in
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
      : SV.t * env * VC.t list = 
  let open Path in
  (* let _ = Printtyped.expression 0 (Format.std_formatter) expr in*)
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
              with Not_found -> 
                try ret @@ SV.Var (Ident.create @@ 
                                   List.assoc name pervasives) 
                with Not_found -> 
                  failwith @@ name^" not found\n"
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
    (* () *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "()") -> ret (SV.ConstUnit)
    (* EffCons e  *)
    | Texp_construct (li_loc,cons_desc,arg_exprs) -> 
        let li = let open Asttypes in li_loc.txt in
        let cstr_name = String.concat "." @@ Longident.flatten li in
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
        let id_of_ld ld = Ident.create @@ ld.lbl_name in
        let fld_ids = List.map (fun (_,ld,_) -> id_of_ld ld) flds in
        let sv = SV.Record (List.combine fld_ids fld_svs) in
          (sv,env',vcs)
    | Texp_record (flds,Some e) -> failwith "Texp_record: Unimpl."
    (* Obj_table.append e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"append",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let ([sv1;sv2],env',vcs) = doIt_exprs env [e1;e2] in
        let typ1 = type_of_tye env.ke e1.exp_type in
        let env'' = doIt_append env' (sv1,typ1) sv2 in
          (SV.ConstUnit, env'', vcs)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"append",_),_,_)},
                  args) when (List.length args <> 2) ->
        failwith @@ (Ident.name id)^".append needs 2 arguments"
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
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
          (* UUID.create () *)
          | SV.Var id when (Ident.name id = "Uuid.create") -> 
              let new_uuid = Ident.create @@ fresh_uuid_name () in
              let te' = TE.add new_uuid Type.uuid env.te in
              let uuids = match KE.find_name "UUID" env.ke with
                | Kind.Extendible prev -> !prev
                | _ -> failwith "UUID Unexpected" in
              let ke' = KE.add (Ident.create "UUID")
                          (Kind.Extendible (ref @@ new_uuid::uuids))
                          env.ke in
                (SV.Var new_uuid, {env with ke=ke';te=te'}, vcs1 @ vcs2)
          | SV.Var id when (Ident.name id = "raise") -> 
              let _ = match sv2s with 
                | [SV.NewEff (Cons.T {name}, None)]
                    when (Ident.name name = "Inconsistency") -> ()
                | _ -> failwith "Not an Inconsistency exception. Unimpl." in
              let _ = print_string "raising inconsistency\n" in
                raise Inconsistency
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
              let tye_binds = Misc.unify_tyes arrow_tye e1.exp_type in
              let (res_sv, res_env, vcs3) = 
                    doIt_fun_app env'' (Fun.T fun_t) tye_binds sv2s in
                (res_sv, res_env, vcs1 @ vcs2 @ vcs3)
          | _ -> failwith "Texp_apply: Unexpected" in
          (res_sv, res_env, res_vcs)
    (* let id = e1 in e2 *)
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_var (lhs_id,_)};
                           vb_expr=e1}], e2) -> 
        let (sv1,env',vcs1) = doIt_expr env e1 in
        let sv1 = match (ast_rec, sv1) with 
          | (Asttypes.Recursive, SV.Fun (Fun.T fun_t)) -> 
              SV.Fun (Fun.T {fun_t with rec_flag=true})
          | _ -> sv1 in
        let ve' = VE.add lhs_id sv1 env'.ve in
        let (sv2,env'',vcs2) = doIt_expr {env' with ve=ve'} e2 in
          (sv2,env'',vcs1 @ vcs2)
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_any};
                           vb_expr=e1}], e2) -> 
        let (sv1,env',vcs1) = doIt_expr env e1 in
        let (sv2,env'',vcs2) = doIt_expr env' e2 in
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
        let scrutyp = type_of_tye env.ke scrutinee.exp_type in
        (*let _ = Printf.printf "Type of the match expression:\n" in
        let _ = Printf.printf "%s\n" @@ Type.to_string exptyp in*)
        let (sv,env'',vcs2)  = let open SV in match scru_sv with
          | List ([],Some l) -> 
              let _ = print_string "unmanifest during match\n" in
              let x = Ident.create @@ fresh_name () in
              let xte = TE.add x exptyp env'.te in
                (SV.Var x, {env' with te=xte}, [])
          | List (conc,abs) -> doIt_list_cases env' (conc,abs) cases
          | NewEff (Cons.T cons_t, argop) -> 
              failwith "Texp_match NewEff Unimpl."
          | Var id -> 
              let name = Ident.name id in
              let typ = TE.find_name name env.te in
              let _ = if Type.is_eff typ then ()
                      else failwith "Scrutinee is non-eff var" in
                doIt_eff_cases env id cases
          | Option op -> doIt_option_cases env' op cases 
          | Record fields -> 
              failwith "Texp_match Record Unimpl."
          | _ -> doIt_sv_cases env' scru_sv scrutyp cases in
          (sv,env'',vcs1 @ vcs2)
    | Texp_match (_,_,ex_cases,_) -> 
        failwith "Match expressions with exception cases Unimpl."
    | Texp_sequence (e1,e2) -> 
        let (svs,env',vcs) = doIt_exprs env [e1;e2] in
          (List.last svs, env', vcs)
    | Texp_ifthenelse (grde,e1,Some e2) -> 
        let (true_grd, env1, vcs1) = doIt_expr env grde in
        let false_grd = SV.Not true_grd in
        let doIt expr env = doIt_expr env expr in
        let (v1_op, env2, vcs2) = 
          try
            let (v1, env2, vcs2) = doIt_under_grd env1 true_grd 
                                     (doIt e1) in
              (Some v1, env2, vcs2)
          with Inconsistency ->
            let (env2,new_vc) = mk_vc env1 false_grd in
              (None, env2, [new_vc]) in
        let (v2_op, env3, vcs3) = 
          try
            let (v2, env3, vcs3) = doIt_under_grd env2 false_grd 
                                     (doIt e2) in
              (Some v2, env3, vcs3)
          with Inconsistency ->
            let (env3,new_vc) = mk_vc env2 true_grd in
              (None, env3, [new_vc]) in
        let sv = match (v1_op, v2_op) with
          | (Some v1, Some v2) -> 
              SV.ite (true_grd, v1, v2) 
          | (Some v1, None) -> v1 
          | (None, Some v2) -> v2
          | (None, None) -> (* over to the parent branch*) 
               raise Inconsistency in
          (sv, env3, vcs1 @ vcs2 @ vcs3)
    | _ -> failwith "Unimpl. expr"

and doIt_sv_cases env scru typ cases = 
  let open Type in match typ with
    | Option _ -> 
        (* 1. Some case *)
        let some_grd = SV.app (L.isSome,[scru]) in
        let none_grd = SV.Not some_grd in
        let some_val = SV.app (L.fromJust, [scru]) in
        let (some_sv_op,env',vcs1) = 
          try 
            let doIt env = doIt_option_cases env 
                             (Some some_val) cases in
            let (some_sv,env',vcs1) = doIt_under_grd env some_grd doIt in
              (Some some_sv, env', vcs1)
          with Inconsistency ->
            (*
             * Make a new vc that preempts this branch.
             *)
            let (env',new_vc) = mk_vc env none_grd in
              (None, env', [new_vc]) in
        (* 2. None case *)
        let (none_sv_op,env'',vcs2) = 
          try 
            let doIt env = doIt_option_cases env None cases in
            let (none_sv, env'', vcs2) = doIt_under_grd env' 
                                           none_grd doIt in
              (Some none_sv, env'', vcs2)
          with Inconsistency -> 
            let (env'',new_vc) = mk_vc env' some_grd in
              (None, env'', [new_vc]) in
        let sv = match (some_sv_op, none_sv_op) with
          | (Some some_sv, Some none_sv) -> 
              SV.ite (some_grd, some_sv, none_sv) 
          | (Some some_sv, None) -> some_sv 
          | (None, Some none_sv) -> none_sv
          | (None, None) -> (* over to the parent branch*) 
               raise Inconsistency in
          (sv, env'', vcs1 @ vcs2)
    | _ -> failwith @@ "doIt_sv_cases Unimpl. for "
              ^(SV.to_string scru)

and doIt_option_cases env op cases = 
  let _ = if List.length cases = 2 then ()
          else failwith "Option pattern match needs 2 cases" in
  let none_case = find_none_case cases in
  let none_expr = none_case.c_rhs in
  let some_case = find_some_case cases in
  let x_var = match some_case.c_lhs.pat_desc with
      (Tpat_construct (_,_,[{pat_desc = Tpat_var (id,_)}])) -> Some id
    | (Tpat_construct (_,_,[{pat_desc = Tpat_any}])) -> None
    | _ -> failwith "Some patterns other than Some x and Some _ Unimpl." in
  let some_expr = some_case.c_rhs in
  let doIt_some x_sv = 
    let xve = match x_var with 
      | None -> env.ve | Some x_var -> VE.add x_var x_sv env.ve in
    let xenv = {env with ve=xve} in
    let (some_sv,env',vcs) = doIt_expr xenv some_expr in
      (some_sv, {env' with ve=env.ve}, vcs) in
    match op with
      | None -> doIt_expr env none_expr
      | Some x_sv -> doIt_some x_sv 

and doIt_eff_case env eff = 
  function {c_lhs = {pat_desc = Tpat_construct (li_loc,cstr_desc,pats)}; 
            c_rhs = case_expr} ->
    let li = let open Asttypes in li_loc.txt in
    let cstr_name = String.concat "." @@ Longident.flatten li in
    let cons_sv = try VE.find_name cstr_name env.ve
                  with Not_found -> not_found "cstr not found" in
    let Cons.T cons_t = match cons_sv with | SV.EffCons c -> c
              | _ -> failwith "doIt_eff_case: Unexpected." in
    let eff_var = SV.Var eff in
    let grd = 
      (* e.g: isUserName_Add(oper(!e2)) *)
      SV.app (cons_t.recognizer,[SV.app (L.oper,[eff_var])]) in
    let xve_fld_pat ve fld_id fld_pat = match fld_pat.pat_desc with
      | Tpat_var (id,_) -> 
          let sv = SV.App (fld_id,[eff_var]) in
            VE.add id sv ve
      | _ -> failwith "Unexpected record fld match" in
    let xve_fld_pats ve fld_pats = 
      List.fold_left 
        (fun ve (_,ld,pat) -> 
           xve_fld_pat ve (Ident.create ld.lbl_name) pat) 
        ve fld_pats in
    let xve = match pats with | [] -> env.ve
      | [{pat_desc = Tpat_record (fld_pats,_)}] -> 
            xve_fld_pats env.ve fld_pats 
      | _ -> failwith "Unexpected EffCons arg match" in
    let xpe = (P.of_sv grd)::env.pe in
    let xenv = {env with pe=xpe; ve=xve} in
    let (case_sv, xenv', vcs) = doIt_expr xenv case_expr in
    (*
     * Condition new predicates in PE and restore original VE.
     *)
    let new_ps = List.take ((List.length xenv'.pe) - 
                            (List.length xpe)) xenv'.pe in
    let pe' = (List.map (fun new_p -> 
                           P._if (P.of_sv grd, new_p)) new_ps)
              @ env.pe in
    let env' = {xenv' with pe=pe'; ve=env.ve}  in
      ((Some grd,case_sv), env', vcs)
  | {c_lhs = {pat_desc = Tpat_any}; c_rhs = case_expr} ->
      let (case_sv, env', vcs) = doIt_expr env case_expr in
        ((None,case_sv), {env' with ve=env.ve}, vcs)
  | _ -> failwith "doIt_eff_case: pat-match Unimpl."

and doIt_eff_cases env eff cases = 
   let (gsvs, (env',vcs)) = List.map_fold_left 
             (fun (env,vcs) case -> 
                let (gsv,env',new_vcs) = doIt_eff_case env eff case in 
                  (gsv,(env',vcs @ new_vcs))) 
             (env,[]) cases in
   let (ifes,elsee) = match List.partition 
                              (function (Some _,_) -> true
                                 | (None,_) -> false) gsvs with
     | (ifopes,[(None, elsee)]) -> (List.map 
                            (fun (xop,y) -> (from_just xop,y)) 
                            ifopes, 
                          elsee) 
     | _ -> failwith "doIt_eff_cases: Unexpected" in
   let grded_sv = List.fold_right 
                    (fun (grd,ifee) elsee -> SV.ite (grd,ifee,elsee))
                    (ifes : (SV.t*SV.t) list) elsee in
     (grded_sv, env', vcs)

and doIt_list_cases env (conc,abs) cases = 
  let _ = if List.length cases = 2 then ()
          else failwith "List pattern match needs 2 cases" in
  let is_nil_pat = function
      (Tpat_construct (_,{cstr_name},[])) -> cstr_name = "[]"
    | _ -> false in 
  let is_cons_pat = function
      (Tpat_construct (_,{cstr_name},_)) -> cstr_name = "::"
    | _ -> false in 
  let nil_case = try List.find (fun case -> 
                              is_nil_pat case.c_lhs.pat_desc) cases
                 with Not_found -> not_found "Nil case not found" in
  let nil_expr = nil_case.c_rhs in
  let cons_case = try List.find (fun case -> 
                              is_cons_pat case.c_lhs.pat_desc) cases
                 with Not_found -> not_found "Cons case not found" in
  let (x_var,xs_var) = match cons_case.c_lhs.pat_desc with
      (Tpat_construct (_,_,[{pat_desc = Tpat_var (id1,_)};
                            {pat_desc = Tpat_var (id2,_)}])) ->
        (id1, id2)
    | _ -> failwith ":: patterns other than x::xs not supported." in
  let cons_expr = cons_case.c_rhs in
  let doIt_cons x_sv xs_sv = 
    let xve = VE.add  xs_var xs_sv (VE.add x_var x_sv env.ve) in
    let xenv = {env with ve=xve} in
    let (cons_sv,env',vcs) = doIt_expr xenv cons_expr in
      (cons_sv, {env' with ve=env.ve}, vcs) in
    match (conc,abs) with
      | ([],None) -> doIt_expr env nil_expr
      | ([],Some l) -> failwith "doIt_list_cases: Unexpected"
      | (x_sv::conc', _) -> doIt_cons x_sv (SV.List (conc',abs)) 

let doIt_fun (env: env) (Fun.T {args_t;body}) =
  let (args_tys : (Ident.t * Type.t) list)= 
    List.map (fun (id,tyd) -> 
                (id, type_of_tye env.ke (Misc.to_tye tyd))) 
      args_t in
  let te' = List.fold_left (fun te (id,ty) -> TE.add id ty te)
              env.te args_tys in
  let (body_sv,env',vcs) = doIt_expr {env with te=te'} body in
  let diff_te = env'.te -- env.te in
  let st = (diff_te, List.rev env'.pe) in
  let vcs = List.map (fun (te',p1,p2) -> 
                        (te' -- env.te, List.rev p1, p2)) vcs in
    begin
      Printf.printf "------- Symbolic Trace -----\n";
      VC.print (fst st, snd st, P.of_sv @@ SV.ConstBool true);
      Printf.printf "---- VCs ----\n";
      VC.print_all vcs;
      Printf.printf "body_sv:\n %s\n" (SV.to_string body_sv);
    end

let doIt (ke,te,pe,ve) rdt_spec k' = 
  let _ = k := 2 (* k'*) in
  let Rdtspec.T {schemas; reads; writes; aux} = rdt_spec in
  let tmp_name =  "get_userline" in
  let my_fun = try List.find (fun (Fun.T x) -> 
                            Ident.name x.name = tmp_name)
                     (writes@reads)
               with Not_found -> not_found @@ tmp_name
                    ^" function not found" in
  let env = {ssn=Fun.name my_fun; seqno=0; 
             ke=ke; te=te; pe=pe; ve=ve} in
  let _ = doIt_fun env my_fun in
    failwith "Unimpl. Specverify.doIt"
