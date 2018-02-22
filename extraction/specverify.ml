open Utils
open Types
open Typedtree
open Rdtspec
open Specelab
open Speclang
module S = SymbolicVal
module P = Predicate
module VC = Vc

exception Inconsistency
let unmanifest_list = Ident.create @@ "!L";;
type env_t = (KE.t * TE.t * Predicate.t list * VE.t)
type env = {txn: Ident.t; 
            ssn: Ident.t;
            seqno:int; 
            show: Ident.t -> S.t; (* Additional conditions 
                  that an effect must satisfy to be visible.*)
            ke:KE.t; 
            is_inv: bool;
            te:TE.t; 
            pe: Predicate.t list; (* constraints that are true on all 
                                     paths*)
            path: S.t list; (* constraints that are true on the
                               current path *)
            effs: Ident.t list; (* Effects generated *)
            curr_fun: Ident.t * S.t list;
            ve:VE.t}

(* Symbolic Trace *)
type st_t = TE.t * Predicate.t list

let ppf = Format.std_formatter

let pervasives = [("Pervasives.@@", "@@"); ("Pervasives.=", "="); 
                  ("Pervasives.raise", "raise"); 
                  ("Uuid.create", "Uuid.create");
                  ("Pervasives.&&", "&&"); 
                  ("Pervasives.||", "||"); 
                  ("Pervasives.+", "+"); 
                  ("Pervasives.*", "*"); 
                  ("Pervasives.-", "-");
                  ("Pervasives.<>", "<>");
                  ("Pervasives.>", ">");
                  ("Pervasives.>=", ">=");
                  ("Pervasives.<", "<");
                  ("Pervasives.<=", "<=");]

let s_pervasives = [("=", fun x y -> S.Eq (x,y)); 
                    ("&&", fun x y -> S.And [x;y]); 
                    ("||", fun x y -> S.Or [x;y]);
                    ("<>", fun x y -> S.Not (S.Eq (x,y)));
                    (">", fun x y -> S.Gt (x,y));
                    ("<", fun x y -> S.Lt (x,y));
                    (">=", fun x y -> S.Or [S.Gt (x,y); S.Eq(x,y)]);
                    ("<=", fun x y -> S.Or [S.Lt (x,y); S.Eq(x,y)]);]

let is_pervasive id = List.mem_assoc (Ident.name id) s_pervasives 

let pervasive_app id args = match args with
  | [x;y] -> (List.assoc (Ident.name id) s_pervasives) x y 
  | _ -> failwith "Non-binary pervasive apps Unimpl."

let printf = Printf.printf

(* 
 * BMC bound
 *)
let k =ref 2 (* will be overridden in doIt *)
let eff_consts = ref [] (* will be overridden in doIt *)

let not_found msg = (Printf.printf "%s\n" msg; raise Not_found)

let is_none_pat = function
    (Tpat_construct (_,{cstr_name},[])) -> cstr_name = "None"
  | _ -> false

let is_some_pat = function
    (Tpat_construct (_,{cstr_name},_)) -> cstr_name = "Some"
  | _ -> false

let is_wild_pat = function Tpat_any -> true | _ -> false

let find_none_case cases = try List.find (fun case -> 
                            is_none_pat case.c_lhs.pat_desc) cases
                           with Not_found -> 
                             try List.find (fun case -> 
                                  is_wild_pat case.c_lhs.pat_desc) cases 
                             with Not_found -> not_found "None case not found"

let find_some_case cases = try List.find (fun case -> 
                            is_some_pat case.c_lhs.pat_desc) cases
                           with Not_found -> not_found "Some case not found"

let (--) te1 te2 = 
  TE.fold_name 
      (fun id typ diff_te -> 
         try (ignore @@ TE.find_name (Ident.name id) te2; 
              diff_te) 
         with Not_found -> TE.add id typ diff_te)
      te1 TE.empty

let (++) te1 te2 = TE.fold_name TE.add te2 te1

let doIt_under_grd env grd doIt = 
  let grdp = P.of_sv grd in
  let xpath =  env.path @ [grd] in
  let xenv = {env with path=xpath} in
  let (v,xenv') = doIt xenv in
  (* Restore path and ve *)
  let env' = {xenv' with path=env.path; ve=env.ve}  in
    (v, env')

let rec type_of_tye ke (tye : type_expr) = 
  let open Path in
  let open Types in
  (*let strf = Format.str_formatter in
  let _ = Printtyp.type_expr strf tye in
  let _ = printf "type_of_tye(%s)\n" @@ 
            Format.flush_str_formatter () in*)
  let f = type_of_tye ke in match tye.desc with
    | Tvar aop -> 
      let a_name = Misc.mk_tvar_name aop tye.id in
      (*let _ = printf "type_of_tye(%s)\n" aop in*)
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
          (try ignore @@ 
               f {desc=Tconstr (Pdot (Pident id,"id",l),[],s);
                  id=tye.id; level=tye.level} 
           with Not_found -> failwith "Unknown eff type");
          Type.eff
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
let fresh_eff_name = gen_name "!e"
let fresh_name = gen_name "!v"
let fresh_uuid_name = gen_name "!uuid"
let fresh_ssn_name = gen_name "!ssn_"
let fresh_ssn () = Ident.create @@ fresh_ssn_name ()

let mk_new_effect env (sv1(* eff id *),ty1(* eff id ty *)) sv2 =
  let y = Ident.create @@ fresh_eff_name () in
  let sv_y = S.Var y in
  let (Cons.T cons_t,args) = let open S in match sv2 with 
    | NewEff (cons_t,Some (Record args)) -> (cons_t,args)
    | NewEff (cons_t,None) -> (cons_t,[])
    | _ -> failwith "doIt_append: unexpected sv2" in
  let mkkey_ty1 = L.mkkey (Type.to_string ty1) in
  let phi_1 = S.Eq (S.App (L.objid, [sv_y]),
                     S.App (mkkey_ty1, [sv1])) in
  (* let phi_2 = S.App (cons_t.recognizer,[S.App (L.oper, [sv_y])]) in *)

  let phi_2 = S.Eq (S.App (L.oper, [sv_y]), 
                    S.Var (cons_t.name)) in
  let objtyp = Ident.create @@ 
               match Str.split (Str.regexp "_") 
                       (Ident.name cons_t.name) with
                 | x::y::xs -> x
                 | _ -> failwith "Unexpected form of EffCons name" in
  let phi_3 = S.Eq (S.App (L.objtyp, [sv_y]), 
                     S.Var objtyp) in
  let doIt_arg (arg_id,arg_sv) = S.Eq (S.App (arg_id, [sv_y]), 
                                        arg_sv) in
  let phis_4 = List.map doIt_arg args in
  let phi_5 = S.Eq (S.App (L.txn, [sv_y]), 
                     S.Var env.txn) in
  let phi_6 = S.Eq (S.App (L.ssn, [sv_y]), 
                     S.Var env.ssn) in
  let phi_7 = S.Eq (S.App (L.seqno, [sv_y]), 
                     S.ConstInt env.seqno) in
  let is_currtxn = not env.is_inv in
  let phi_8 = S.Eq (S.App (L.currtxn, [sv_y]), 
                     S.ConstBool is_currtxn) in
  (* For the new effect, phi_1 to phi_8 are true only under 
  * the current branch *)
  let tcond = P.of_svs env.path in
  let tconj = P.of_sv @@ S.And 
                ([phi_1; phi_2; phi_3] @ phis_4 @ 
                     [phi_5; phi_6; phi_7; phi_8]) in
  let tcondp = P._if (tcond, tconj) in
  let phi_2' = S.Eq (S.App (L.oper, [sv_y]),
                     S.Var (Cons.name Cons.nop))  in
  let phi_3' = S.Eq (S.App (L.txn, [sv_y]), 
                     S.Var L.txn_nop) in
  let phi_4' = S.Eq (S.App (L.ssn, [sv_y]), 
                     S.Var L.ssn_nop) in
  (* phi_2' and phi_3' are true anywhere outside the current branch *)
  let fcond = P.of_sv @@ S.Not (S.And env.path) in
  let fcondp = P._if (fcond, P.of_sv @@ S.And [phi_2'; phi_3'; phi_4']) in
  let ps = [tcondp; fcondp(*; uncondp*)] in
  (* let _ = Printf.printf "New pred:\n%s\n" (P.to_string conj) in*)
    (y,ps)

let doIt_append env typed_sv1 sv2 =
  let (y,ps) = mk_new_effect env typed_sv1 sv2 in
  let te' = TE.add y Type.eff env.te in
  let pe' = env.pe @ ps in
  let seqno' = env.seqno + 1 in
  let effs' = y::(env.effs) in
    {env with seqno=seqno';te=te'; pe=pe'; effs=effs'}

let doIt_get env typed_sv1 sv2 = 
  let (y,y_ps) = mk_new_effect env typed_sv1 sv2 in
  let vis (id1,id2) = S.App (L.vis, [S.Var id1;
                                     S.Var id2]) in
  let grded_eff (id1,id2) = 
      S.ite (S.And [vis (id1,id2); (env.show id1)], 
             S.Option (Some (S.Var id1)), 
             S.Option None) in
  (*
   * E.g: [vis(E0,!e0)? Some E0 : None; vis(E1,!e0)? Some E1 : None]
   *)
  let ys = List.map (fun eff -> grded_eff (eff,y)) !eff_consts in
  (* Since vis(a,b) => samobj(a,b) => objid(a) = objid(b), we 
   * don't have to assert it separately. *)
  (* 
   * ys is the manifest prefix. We also need to create a list 
   * variable to serve as the unmanifest suffix.
   *)
  let l = unmanifest_list in
  let te' = TE.add l (Type.List Type.eff) (TE.add y Type.eff env.te) in
  let pe' = env.pe @ y_ps in
  let seqno' = env.seqno + 1 in
  let effs' = y::(env.effs) in
  let env' = {env with seqno=seqno'; te=te'; pe=pe'; effs=effs'} in
  let ret_sv = S.List (ys, Some (S.Var l)) in
    (ret_sv,env')

let (unmanifest_list_map : (string*S.t list, Ident.t) Hashtbl.t) = Hashtbl.create 217

let gen_rand_string length =
    let gen() = match Random.int(26+26+10) with
        n when n < 26 -> int_of_char 'a' + n
      | n when n < 26 + 26 -> int_of_char 'A' + n - 26
      | n -> int_of_char '0' + n - 26 - 26 in
    let gen _ = String.make 1 (char_of_int(gen())) in
    String.concat "" (Array.to_list (Array.init length gen))

let get_after_n l n = 
  let rec get_after_n_rec cnt l =
    if cnt >= List.length l then [] 
    else
      if cnt >= n then 
        (List.nth l cnt) :: (get_after_n_rec (cnt+1) l) 
      else get_after_n_rec (cnt+1) l in
  get_after_n_rec 0 l

let rec doIt_fun_app env (Fun.T fun_t) tyebinds arg_svs =
  (*
   * (KE['a -> T], TE, PE, VE[x -> v2] | e --> v <| (TE',PE',C)
   * --------------------------------------------------------
   *    (KE, TE, PE, VE) |- (\x.e) T v2 --> v <| (TE',PE',C)
   *
   * The nature of symbolic execution guarantees that T is always a 
   * concrete type, and v2 and v are symbolic values.
   *)
  let xve' = match fun_t.fun_ve with
             | Some ve -> VE.fold_name VE.add ve env.ve
             | _ -> env.ve in
  let env1 = {env with curr_fun=(fun_t.name, arg_svs);ve=xve'} in
  let typbinds = List.map (fun (a,tye) -> 
                           (Ident.create a, 
                            Kind.Alias (type_of_tye env1.ke tye)))
                 tyebinds in
  (* Special casing for symbolic lists *)
  let bind_typs ke = List.fold_left 
                       (fun ke (a,typ) -> KE.add a typ ke)
                       ke typbinds in
  (*Only bind args till (List.length arg_svs) number of arguments, to generalize for 
    partial application case.*)
  let min_length = List.length arg_svs in
  let rec bind_args_min_list cnt = 
     if cnt < min_length then 
       let (arg,_) = List.nth fun_t.args_t cnt in
       let r1 = (arg, List.nth arg_svs cnt) in
       r1::bind_args_min_list (cnt+1)
     else [] in
  let argbinds = bind_args_min_list 0 in
  let bind_args ve = List.fold_left 
                       (fun ve (arg,sv) -> match sv with
                          | S.Fun (Fun.T fun_t) -> 
                              let sv' = S.Fun (Fun.T {fun_t with name=arg}) in 
                                VE.add arg sv(*'*) ve
                          | _ -> VE.add arg sv ve) 
                       ve argbinds in
  let bind_self ve =
    (* Rec function M.f is referred as f in its body *)
    let qualif_name = Ident.name fun_t.name in
    let unqualif_name = List.last @@ 
                          Str.split (Str.regexp "\.") qualif_name in
      VE.add (Ident.create unqualif_name) (S.Fun (Fun.T fun_t)) ve in
  let xke = List.fold_left (fun ke f -> f ke) env1.ke
              [bind_typs] in
  let xve = List.fold_left (fun ve f -> f ve) env1.ve
              [bind_args; if fun_t.rec_flag then bind_self 
                          else (fun ve -> ve)] in
  let xenv = {env1 with ke=xke; ve=xve} in
  if List.length fun_t.args_t = List.length arg_svs then
      let (body_sv,xenv') = doIt_expr xenv fun_t.body in 
      let (pe',body_sv') = P.simplify xenv'.pe body_sv in
      let env' = {xenv' with ke=env.ke; ve=env.ve; pe=pe'} in
        (body_sv', env')
  else 
      (*Partial Application Case: Generate a new curried function*)
      let new_args_t = get_after_n fun_t.args_t (List.length arg_svs) in
      (*Generate a new function name by appending arg_svs as a string to function name*)
      let arg_string = List.fold_right (fun sv acc -> acc^(S.to_string sv)) arg_svs "" in
      let new_name = (Ident.name fun_t.name) ^ arg_string in
      let new_fun = Fun.T {fun_t with name=(Ident.create new_name);
                            args_t=new_args_t; fun_ve=Some xve} in
      (S.Fun new_fun, env)

and doIt_expr env (expr:Typedtree.expression) : S.t * env = 
  let open Path in
  (*let v1 = expr.exp_loc.loc_start.pos_lnum in
  let v2 = expr.exp_loc.loc_start.pos_cnum - 
            expr.exp_loc.loc_start.pos_bol in
  let v3 = expr.exp_loc.loc_end.pos_lnum in
  let v4 = expr.exp_loc.loc_end.pos_cnum - 
            expr.exp_loc.loc_end.pos_bol in
  let randString = gen_rand_string 3 in
  let _ = printf "%s Starting (%d,%d,%d,%d)\n" randString v1 v2 v3 v4 in*)
  let ret sv = (sv, env) in
  let doIt_exprs = List.map_fold_left doIt_expr in
  let is_table_mod id = 
    let tokens = Str.split (Str.regexp "_") (Ident.name id) in
      (List.length tokens >= 2) && (List.hd (List.rev tokens) = "table") in
  let (res : S.t * env) = match expr.exp_desc with
    (* id *)
    | Texp_ident (path,_,_) -> 
        let names = Path.all_names path in
        let name = String.concat "." names in
        (*let _ = printf "Looking for id: %s\n" (name) in*)
          begin
            try ret (VE.find_name name env.ve)
            with Not_found -> 
              try let _ = TE.find_name name env.te in 
                ret (S.Var (Ident.create name))
              with Not_found -> 
                try ret @@ S.Var (Ident.create @@ 
                                   List.assoc name pervasives) 
                with Not_found -> 
                  failwith @@ name^" not found\n"
          end
    (* constant *)
    | Texp_constant const ->
        let open Asttypes in 
          (match const with 
             | Const_int i -> ret (S.ConstInt i)
             | Const_string (s, None) -> ret (S.ConstString s)
             | Const_string (s, Some s') -> ret (S.ConstString (s^s'))
             | _ -> failwith "Texp_constant Unimpl.")
    (* e1::e2 *)
    | Texp_construct (_,cons_desc, [arge1; arge2]) 
      when (cons_desc.cstr_name = "::") -> 
        let (arg_sv1, env') = doIt_expr env arge1 in
        let (arg_sv2, env'') = doIt_expr env' arge2 in
        let sv = S.cons (arg_sv1,arg_sv2) in
          (sv,env'')
    (* true *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "true") -> ret (S.ConstBool true)
    (* false *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "false") -> ret (S.ConstBool false)
    (* [] *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "[]") -> ret (S.nil)
    (* None *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "None") -> ret (S.none)
    (* Some e *)
    | Texp_construct (_,cons_desc, [arge])
      when (cons_desc.cstr_name = "Some") -> 
        let (arg_v, env') = doIt_expr env arge in
          (S.some arg_v, env')
    (* () *)
    | Texp_construct (_,cons_desc, [])
      when (cons_desc.cstr_name = "()") -> ret (S.ConstUnit)
    (* EffCons e  *)
    | Texp_construct (li_loc,cons_desc,arg_exprs) -> 
        let li = let open Asttypes in li_loc.txt in
        let cstr_name = String.concat "." @@ Longident.flatten li in
        let cstr_sv = try VE.find_name cstr_name env.ve 
                      with Not_found -> failwith @@ 
                              "Unknown constructor: "^cstr_name in
        let cons_t = match cstr_sv with 
          | S.EffCons x -> x 
          | _ -> failwith "Texp_construct: Unexpected" in
        let (arg_svs,env') = doIt_exprs env arg_exprs in
        let arg_sv_op = match arg_svs with
          | [] -> None | [arg_sv] -> Some arg_sv
          | _ -> failwith @@ cstr_name^" has more than 1 arg" in
        let sv = S.NewEff (cons_t, arg_sv_op) in
          (sv,env')
    (* {id1=e1; id2=e2; ..}*)
    | Texp_record (flds,None) -> 
        let fld_exprs = List.map (fun (_,_,z) -> z) flds in
        let (fld_svs,env') = doIt_exprs env fld_exprs in
        let id_of_ld ld = Ident.create @@ ld.lbl_name in
        let fld_ids = List.map (fun (_,ld,_) -> id_of_ld ld) flds in
        let sv = S.Record (List.combine fld_ids fld_svs) in
          (sv,env')
    | Texp_record (flds,Some e) -> failwith "Texp_record: Unimpl."
    (* Obj_table.append e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"append",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let ([sv1;sv2],env') = doIt_exprs env [e1;e2] in
        let S.NewEff (cons_t, _) = sv2 in
        let typ1 = type_of_tye env.ke e1.exp_type in
        let env'' = doIt_append env' (sv1,typ1) sv2 in
          (S.ConstUnit, env'')
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"append",_),_,_)},
                  args) when (List.length args <> 2) ->
        failwith @@ (Ident.name id)^".append needs 2 arguments"
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},
                  [(Asttypes.Nolabel,Some e1); 
                   (Asttypes.Nolabel,Some e2)]) when (is_table_mod id) -> 
        let ([sv1;sv2],env') = doIt_exprs env [e1;e2] in
        let typ1 = type_of_tye env.ke e1.exp_type in
        let (effs_sv, env'') = doIt_get env' (sv1,typ1) sv2 in
          (effs_sv, env'')
    (* f e *) (* (\x.e) e *)
    | Texp_apply (e1, largs) -> 
        let (sv1,env') = doIt_expr env e1 in
        (*let _ = printf "???%s\n" (S.to_string sv1) in*)
        let e2s = map_snd_opts largs in
        let (sv2s,env'') = doIt_exprs env' e2s in
        let (res_sv, res_env) = match sv1 with
          (* UUID.create () *)
          | S.Var id when (Ident.name id = "Uuid.create") -> 
              let new_uuid = Ident.create @@ fresh_uuid_name () in
              let uuids = match KE.find_name "UUID" env.ke with
                | Kind.Extendible prev -> !prev
                | _ -> failwith "UUID Unexpected" in
              let ke' = KE.add (Ident.create "UUID")
                          (Kind.Extendible (ref @@ new_uuid::uuids))
                          env.ke in
                (S.Var new_uuid, {env with ke=ke'})
          | S.Var id when (is_pervasive id) -> 
              (pervasive_app id sv2s, env'')
          | S.Var id -> (S.App (id,sv2s), env'')
          | S.Fun (Fun.T fun_t) -> 
              (*
               * OCaml has no explicit type applications. We reconstruct
               * type arguments by unifying function type with function
               * expression type.
               *)
              (*let _ = printf "--- %s %d\n" (Ident.name fun_t.name) (List.length fun_t.args_t) in*)
              let arrow_tye = Misc.to_tye @@ 
                              Misc.curry (List.map snd fun_t.args_t)
                                 fun_t.res_t in
              (*let strf = Format.str_formatter  in
              let _ = List.map (fun (x, y) -> printf "%s\n" (Ident.name x)) fun_t.args_t in
              let _ = Printtyp.raw_type_expr strf arrow_tye in
              let _ = Format.fprintf strf "\n" in
              let _ = Printtyp.raw_type_expr strf e1.exp_type in
              let _ = Format.fprintf strf "\n" in*)
              let tye_binds = Misc.unify_tyes arrow_tye e1.exp_type in
              let (res_sv, res_env) = 
                    doIt_fun_app env'' (Fun.T fun_t) tye_binds sv2s in
              let _ = if Ident.name @@ Fun.name (Fun.T fun_t) = "g" 
                      then printf "--- %s \n" @@ S.to_string res_sv
                      else () in
                (res_sv, res_env)
          | _ -> failwith "Texp_apply: Unexpected" in
          (res_sv, res_env)
          (*else (ConstBool true, env, [])*)
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_var (lhs_id,_)};
                           vb_expr=e1}], e2) -> 
        let (sv1,env') = doIt_expr env e1 in
        let sv1 = match (ast_rec, sv1) with 
          | (Asttypes.Recursive, S.Fun (Fun.T fun_t)) -> 
              S.Fun (Fun.T {fun_t with rec_flag=true})
          | _ -> sv1 in
        let ve' = VE.add lhs_id sv1 env'.ve in
        let (sv2,env'') = doIt_expr {env' with ve=ve'} e2 in
          (sv2,env'')
    | Texp_let (ast_rec, [{vb_pat={pat_desc=Tpat_any};
                           vb_expr=e1}], e2) -> 
        let (sv1,env') = doIt_expr env e1 in
        let (sv2,env'') = doIt_expr env' e2 in
          (sv2,env'')
    (* \x.e *)
    | Texp_function (_,[case],_) ->
        let (args,body) = Misc.extract_lambda case in
        let open Types in
        let arrow_t = expr.exp_type.desc in
        let (arg_ts,res_t) = Misc.uncurry_arrow arrow_t in
        let (fun_t:Fun.t) = Fun.make ~rec_flag: false
                            ~args_t: (List.zip args arg_ts) 
                            ~res_t: res_t ~body: body 
                            ~name: Fun.anonymous in
          ret @@ S.Fun fun_t
    | Texp_function (_,cases,_) -> 
        failwith "Lambdas with multiple cases Unimpl."
    | Texp_match (scrutinee,cases,[],_) ->
        let (scru_sv, env') = doIt_expr env scrutinee in
        let exptyp = type_of_tye env.ke expr.exp_type in
        let scrutyp = type_of_tye env.ke scrutinee.exp_type in
        (*let strf = Format.str_formatter in
        let _ = Printtyp.type_expr strf expr.exp_type in
        let _ = Printf.printf "Type of the match expression:%s = %s\n" 
                  (Format.flush_str_formatter ()) (Type.to_string exptyp) in
        let _ = Printtyp.type_expr strf scrutinee.exp_type in
        let _ = Printf.printf "Type of scrutinee: %s = %s\n" 
                  (Format.flush_str_formatter ()) (Type.to_string scrutyp) in*)
        let (sv,env'')  = let open S in match scru_sv with
          (* List and Option are special cases where the interpreter 
           * does some of the reasoning. *)
          | List ([],Some l) -> 
              let x = (*Use the same unmanifest list while evaluating 
                        expressions at the same program location *) 
                      (let (fname, args) = env.curr_fun in
                      let _ = printf "Processing unmanifest list\n" in
                      let _ = printf "Function: %s\n" (Ident.name fname) in
                      let _ = printf "Args:\n" in
                      let _ = List.map (fun sv1 -> printf "%s\n" (S.to_string sv1)) args in
                      if Hashtbl.mem unmanifest_list_map (Ident.name fname, args) then
                         let res = Hashtbl.find unmanifest_list_map (Ident.name fname, args) in
                         let _ = printf "Reused umlist variable: %s --> %s\n"
                         (Ident.name fname) (Ident.name res) in
                         res
                      else
                         let res = Ident.create @@ fresh_name () in 
                         let _ = printf "%s --> %s\n" (Ident.name fname) (Ident.name res) in
                         let _ = Hashtbl.add unmanifest_list_map (Ident.name fname, args) res in
                          res) in
              let xte = TE.add x exptyp env'.te in
                (S.Var x, {env' with te=xte})
          | List (conc,abs) -> doIt_list_cases env' (conc,abs) cases
          | Option op -> doIt_option_cases env' op cases 
          | NewEff (Cons.T cons_t, argop) -> 
              failwith "Texp_match NewEff Unimpl."
          | Record fields -> 
              failwith "Texp_match Record Unimpl."
          (* In other cases, we let the solver do the reasoning *)
          | _ -> doIt_sv_cases env' scru_sv scrutyp cases in
          (sv,env'')
    | Texp_match (_,_,ex_cases,_) -> 
        failwith "Match expressions with exception cases Unimpl."
    | Texp_sequence (e1,e2) -> 
        let (svs,env') = doIt_exprs env [e1;e2] in
          (List.last svs, env')
    | Texp_ifthenelse (grde,e1,Some e2) -> 
        let (true_grd, env1) = doIt_expr env grde in
        let false_grd = S.Not true_grd in
        let doIt expr env = doIt_expr env expr in
        let (v1, env2) = doIt_under_grd env1 true_grd 
                                     (doIt e1) in
        let (v2, env3) = doIt_under_grd env2 false_grd 
                                 (doIt e2) in
        let sv =  S.ite (true_grd, v1, v2) in
          (sv, env3)
    | _ -> failwith "Unimpl. expr" in 
    res
  (*let (sv, env) = res in
  let assumps = (List.concat @@ List.map 
                     (function P.BoolExpr v -> [v]
                        | _ -> []) env.pe) in
  let simplified_sv = P.simplify assumps sv in
    (simplified_sv, env)*)

and doIt_sv_cases env scru_sv typ cases =
  match typ with
  | Type.Option _ -> 
      (* 1. Some case *)
      let some_grd = S.app (L.isSome,[scru_sv]) in
      let none_grd = S.Not some_grd in
      let some_val = S.app (L.fromJust, [scru_sv]) in
      let (some_sv,env') = 
        let doIt env = doIt_option_cases env 
                           (Some some_val) cases in
          doIt_under_grd env some_grd doIt in
      (* 2. None case *)
      let (none_sv,env'') = 
          let doIt env = doIt_option_cases env None cases in
            doIt_under_grd env' none_grd doIt in
      let sv =  S.ite (some_grd, some_sv, none_sv) in
        (sv, env'')
  | typ when (Type.is_eff typ) -> doIt_eff_cases env scru_sv cases
  (*| Type.List _ -> doIt_list_cases env scru_sv cases*)
  | _ -> (*doIt_list_cases env scru_sv cases*) failwith @@ "doIt_sv_cases Unimpl. for "
            ^(S.to_string scru_sv)^" : "^(Type.to_string typ)

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
    let (some_sv,env') = doIt_expr xenv some_expr in
      (some_sv, {env' with ve=env.ve}) in
    match op with
      | None -> doIt_expr env none_expr
      | Some x_sv -> doIt_some x_sv 

and doIt_eff_case env eff_sv = 
  function {c_lhs = {pat_desc = Tpat_construct (li_loc,cstr_desc,pats)}; 
            c_rhs = case_expr} ->
    let li = let open Asttypes in li_loc.txt in
    let cstr_name = String.concat "." @@ Longident.flatten li in
    let cons_sv = try VE.find_name cstr_name env.ve
                  with Not_found -> 
                    not_found @@ cstr_name^" cstr not found" in
    let Cons.T cons_t = match cons_sv with | S.EffCons c -> c
              | _ -> failwith "doIt_eff_case: Unexpected." in
    let grd = 
      (* e.g: isUserName_Add(oper(!e2)) *)
      S.Eq (S.App (L.oper,[eff_sv]), 
            S.Var (cons_t.name)) in
    let xve_fld_pat ve fld_id fld_pat = match fld_pat.pat_desc with
      | Tpat_var (id,_) -> 
          let fld_name = Ident.name fld_id in
          let sv1 = try VE.find_name fld_name env.ve 
                             with Not_found ->
                               not_found @@ fld_name^" fld_name not found" in
          (*let fld_fn = match sv1 with
                       | ConstInt i -> sv1
                       | S.Var x -> x in*)
          let S.Var fld_fn = sv1 in                 
          let sv = S.App (fld_fn,[eff_sv]) in
            VE.add id sv ve
      | _ -> failwith "Unexpected record fld match" in
    let xve_fld_pats ve fld_pats = 
      List.fold_left 
        (fun ve (_,ld,pat) -> 
           xve_fld_pat ve (Ident.create ld.lbl_name) pat) 
        ve fld_pats in
    let xve = match pats with 
      | [] | [{pat_desc = Tpat_any}] -> env.ve
      | [{pat_desc = Tpat_record (fld_pats,_)}] -> 
            xve_fld_pats env.ve fld_pats 
      | _ -> failwith "Unexpected EffCons arg match" in
    let xenv = {env with ve=xve} in
    let doIt env = doIt_expr env case_expr in
    let (case_sv, xenv') = doIt_under_grd xenv grd doIt in
    (* Restore original VE.  *)
    let env' = {xenv' with ve=env.ve}  in
      ((Some grd,case_sv), env')
  | {c_lhs = {pat_desc = Tpat_any}; c_rhs = case_expr} ->
      let (case_sv, env') = doIt_expr env case_expr in
        ((None,case_sv), {env' with ve=env.ve})
  | _ -> failwith "doIt_eff_case: pat-match Unimpl."

and doIt_eff_cases env eff_sv cases = 
   let (gsvs, env') = List.map_fold_left 
                       (fun env case -> 
                          doIt_eff_case env eff_sv case) 
                       env cases in
   let (ifes,elsee) = match List.partition 
                              (function (Some _,_) -> true
                                 | (None,_) -> false) gsvs with
     | (ifopes,[(None, elsee)]) -> (List.map 
                            (fun (xop,y) -> (from_just xop,y)) 
                            ifopes, 
                          elsee) 
     | _ -> failwith "doIt_eff_cases: Unexpected" in
   (*let assumps = (List.concat @@ List.map 
                         (function P.BoolExpr v -> [v]
                            | _ -> []) env.pe) in*)
   let grded_sv = List.fold_right 
                    (fun (grd,ifee) elsee -> S.ite (grd,ifee,elsee))
                    (ifes : (S.t*S.t) list) elsee in
     (grded_sv, env')

and doIt_list_cases env (conc,abs) cases = 
  (*let _ = Printf.printf "Conc, abs\n" in*)
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
    let (cons_sv,env') = doIt_expr xenv cons_expr in
      (cons_sv, {env' with ve=env.ve}) in
    match (conc,abs) with
      | ([],None) -> doIt_expr env nil_expr
      | ([],Some l) -> failwith "doIt_list_cases: Unexpected"
      | (x_sv::conc', _) -> doIt_cons x_sv (S.List (conc',abs))

let doIt_fun (env: env) (Fun.T {name;args_t;body}) =
  let (args_tys : (Ident.t * Type.t) list)= 
    List.map (fun (id,tyd) -> 
                (id, type_of_tye env.ke (Misc.to_tye tyd))) 
      args_t in
  let te' = List.fold_left (fun te (id,ty) -> TE.add id ty te)
              env.te args_tys in
  let (body_sv,env') = doIt_expr {env with te=te'} body in
  let (pe',body_sv') = P.simplify env'.pe body_sv in
  let diff_te = env'.te -- env.te in
  let st = (diff_te, pe', P.of_sv @@ S.ConstBool true) in
    begin
      (*Printf.printf "------- Symbolic Trace (%s) -----\n" 
        (Ident.name name);
      VC.print_seq st;*)
      (body_sv', {env' with pe=pe'}, [st])
    end

let doIt_inv (env: env) (Fun.T {name;args_t;body}) =
  let (args_tys : (Ident.t * Type.t) list)= 
    List.map (fun (id,tyd) -> 
                (id, type_of_tye env.ke (Misc.to_tye tyd))) 
      args_t in
  let te' = List.fold_left (fun te (id,ty) -> TE.add id ty te)
              env.te args_tys in
  let (body_sv,env') = doIt_expr {env with te=te'; is_inv=true} body in
  let (pe',body_sv') = P.simplify env'.pe body_sv in
  let diff_te = env'.te -- env.te in
  let vc = (diff_te, pe', P.of_sv body_sv') in
    begin
      (*Printf.printf "---- VC (%s) ----\n" (Ident.name name);
      VC.print_seq vc;*)
      (body_sv', {env' with pe=pe'}, [vc])
    end

let get_arg_condition (oper) (eff1) (eff2) (schemas) : S.t list = 
  let doIt_schema (oper) (eff1) (eff2) (tname,ts) =
    let Tableschema.T {eff_cons} = ts in
    let doIt_eff_cons (S.Var y) (eff1) (eff2) (Effcons.T x) = 
      let prefix = Ident.name tname in
      let suffix = Ident.name x.name in
      if (Ident.name y) = prefix^"_"^suffix then
        let args = List.map 
                 (fun (id,colty) -> (id, type_of_coltype colty schemas))
                 x.args_t in
        List.map (fun (id,typ) -> 
            let mkkey_ty = L.mkkey (Type.to_string typ) in
            let sv1 = S.app (mkkey_ty, [S.App (id, [S.Var eff1])]) in
            let sv2 = S.app (mkkey_ty, [S.App (id, [S.Var eff2])]) in
            S.app (L.hbid, [sv1;sv2])) args
      else [] in
    List.map (doIt_eff_cons oper eff1 eff2) eff_cons in
  let all_cons = List.concat @@ List.concat @@
              List.map (doIt_schema oper eff1 eff2) schemas in
  all_cons 

let extract_oper_cons (schemas) : S.t list = 
  let doIt_schema (tname,ts) =
    let Tableschema.T {eff_cons} = ts in
    let doIt_eff_cons (Effcons.T x) = 
      let prefix = Ident.name tname in
      let suffix = Ident.name x.name in
      let args = List.map 
               (fun (id,colty) -> (id, type_of_coltype colty schemas))
               x.args_t in
      S.Var (Ident.create @@ prefix^"_"^suffix) in
    List.map doIt_eff_cons eff_cons in
  let all_cons = List.concat @@ 
              List.map doIt_schema schemas in
  all_cons 

let doIt (ke,te,pe,ve) rdt_spec k' = 
  let _ = k := 25 (* k'*) in
  let _ = Gc.set {(Gc.get()) with Gc.minor_heap_size = 2048000; 
                                  Gc.space_overhead = 200} in
  let _ = eff_consts := 
          List.tabulate !k (fun i -> 
                              Ident.create @@ "E"^(string_of_int i)) in
  let Rdtspec.T {schemas; reads; writes; invs; aux} = rdt_spec in
  let oper_cons = extract_oper_cons schemas in
  let _ = Printf.printf "Number of transactions: %d\n" (List.length writes) in
  List.map (fun my_fun1 ->
    let (ssn2,ssn1) = (fresh_ssn (), fresh_ssn ()) in
    let ke = KE.add (Ident.create "Eff") 
                    (* An additional NOP effect for technical reasons *)
                    (Kind.Enum (!eff_consts@[L.e_nop])) ke in
    let te = TE.add ssn2 Type.ssn (TE.add ssn1 Type.ssn te) in
    let env1 = {txn=Fun.name my_fun1; seqno=0; 
                curr_fun=(Fun.name my_fun1, []);
              ssn=ssn1; ke=ke; te=te;
              pe=pe; path=[]; ve=ve; 
              is_inv = false;
              show=(fun eff -> S.ConstBool true);
              effs=[]; 
              (*te=TE.add ssn1 Type.ssn te List.fold_left 
                    (fun te eff_const -> 
                       TE.add eff_const Type.eff te) te !eff_consts*)} in
    let (_, env1', vcs1) = doIt_fun env1 my_fun1 in
    let is_pre = ref false in
    let exp_inv_name = "inv_" ^ (String.sub (Ident.name @@ Fun.name my_fun1) 3 
                        @@ (String.length (Ident.name @@ Fun.name my_fun1))-3) in
    let _ = printf "Exp invariant: %s\n" (exp_inv_name) in
    let my_fun2 = try List.find (fun (Fun.T x) -> 
                            Ident.name x.name = exp_inv_name)
                     (invs)
               with Not_found -> not_found @@ exp_inv_name
                    ^" function not found" in
    let env2 = 
        {env1 with txn=Fun.name my_fun2; ke=env1'.ke; 
                   ssn=ssn2;
                   curr_fun=(Fun.name my_fun2, []);
                   show=(fun e -> 
                           DelayedITE(is_pre, 
                                      S.Not (S.Eq (S.App (L.ssn, [S.Var e]),
                                                   S.Var ssn1)),
                                      S.ConstBool true))} in
    let (_, env2', vcs2) = doIt_inv env2 my_fun2 in
    let (_, env2', vcs2) = doIt_inv env2 my_fun2 in
    let ((te1,wr_prog,_),(te2,inv_prog,inv)) = 
      match (vcs1,vcs2) with | ([st],[inv_vc]) -> (st,inv_vc)
        | _ -> failwith "Specverify.doIt: Unexpected" in
    let (effs1, effs2) = (env1'.effs, env2'.effs) in
    let wr_prog_list = List.map (fun (_,wr_prog,_) -> wr_prog) vcs1 in
    (* Printing program preds *)
    let _ = List.iteri 
              (fun i p -> Printf.printf "%d.\n" i; P.print p) @@
              List.concat wr_prog_list in
    let (_, env2', vcs2) = doIt_inv env2 my_fun2 in
    let wr_inv_list = List.map (fun (_,wr_prog,_) -> wr_prog) vcs2 in
    (* Printing inv preds *)
    let _ = List.iteri 
              (fun i p -> Printf.printf "%d.\n" i; P.print p) @@
              List.concat wr_inv_list in
    let [(te2,inv_prog,inv)] = vcs2 in
    let te_list = List.map (fun (te1, _, _) -> te1) vcs1 in
    (*let ((te1,wr_prog,_),(te2,inv_prog,inv)) = 
      match (vcs1,vcs2) with | ([st1;st2],[inv_vc]) -> (st1,inv_vc)
        | _ -> failwith "Specverify.doIt: Unexpected" in*)
    let (effs1, effs2) = (env1'.effs, env2'.effs) in
    let in_set e s = S.Or (List.map (fun e' -> S.Eq (S.Var e', S.Var e)) s) in
    let gen_or_list_successor opers eff1 eff2 = 
        let (op::ops) = opers in 
        let cond_for_op = get_arg_condition op eff1 eff2 schemas in
        let eq_cond = S.Eq (S.App (L.oper, [S.Var eff2]), op) in
        let same_op_cond = S.And (eq_cond :: cond_for_op) in
        let or_list = List.map (fun op -> S.Eq (S.App (L.oper, [S.Var eff2]), op)) ops in
        P.of_sv (S.Or (same_op_cond::or_list)) in
    let rec comm_assertion eff1 eff2 opers = 
      match opers with
      | x::xs -> if (List.length xs) > 0 
          then (P._if (P.of_sv @@ S.Eq (S.App (L.oper, [S.Var eff1]), x), 
                       gen_or_list_successor (x::xs) eff1 eff2)) 
                  :: (comm_assertion eff1 eff2 xs) 
          else [P._if (P.of_sv @@ S.Eq (S.App (L.oper, [S.Var eff1]), x), 
                       P.of_sv @@ S.Eq (S.App (L.oper, [S.Var eff2]), x))]
      | _ -> [] in
    let comm_assertions = List.flatten @@ List.mapi 
        (fun i eff -> if i<(!k-1) 
          then comm_assertion eff 
                  (List.nth !eff_consts (i+1)) oper_cons 
          else []) !eff_consts in
    let mk_ssn_cstr ssn_id effs = 
      P.forall Type.eff 
        (fun v -> 
           P._if (P.of_sv @@ S.Eq (S.App (L.ssn, [S.Var v]), 
                                   S.Var ssn_id), 
                  P.of_sv @@ in_set v @@ List.rev effs)) in
    let pre = 
      begin
        is_pre := true;
        P.ground inv
      end in
    let prog = 
      begin
        is_pre := false;
        List.map P.ground @@ List.concat @@ 
          wr_prog_list @ [inv_prog; 
                          comm_assertions; 
                          [mk_ssn_cstr ssn1 effs1; 
                           mk_ssn_cstr ssn2 effs2]]
      end in
    let post = 
      begin
        is_pre := false;
        P.ground inv
      end in
    let new_te = TE.fold_name 
                   (fun id ty te -> 
                      try (ignore @@ TE.find_name (Ident.name id) te; 
                            raise Not_found)
                           (*failwith @@ (Ident.name id)^" variable \
                                    duplicate found. Please rename.")*)
                      with Not_found -> TE.add id ty te) te2 te1 in
    let conc_vc = let open VC in {kbinds=env2'.ke; tbinds=te++new_te; 
                                  pre=pre; prog=prog; post=post} in
    (*let _ = VC.print conc_vc in*)
      (Fun.name my_fun1, conc_vc)) writes
