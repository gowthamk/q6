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
    (* Cons {id1=sv1; id2=sv2; ..}  *)
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},largs) 
      when (is_table_mod id) -> 
        let args = map_snd_opts largs in
        let (svs,env',vcs) = doIt_exprs env args in
        let _ = Printf.printf "# of args: %s\n" 
                  (string_of_int @@ List.length args) in
          failwith "Unimpl. apply"
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

let doIt env rdt_spec effs = 
  let Rdtspec.T {schemas; reads; writes; aux} = rdt_spec in
  let my_fun = List.find (fun (Fun.T x) -> 
                            Ident.name x.name = "do_test1")
                 writes in
  let _ = doIt_fun env my_fun in
    failwith "Unimpl. Specverify.doIt"
