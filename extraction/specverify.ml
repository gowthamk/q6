open Typedtree
open Rdtspec
open Specelab (* hiding doIt *)
open Speclang
module Fun = Rdtspec.Fun
module Id = Rdtspec.Id
module RefTy = RefinementType

type env = {ke:KE.t; te:TE.t; ve:VE.t}

let ident_of_id id = Ident.create @@ Id.to_string id

let ppf = Format.std_formatter

let rec type_of_tyd schemas tyd = 
  let open Path in
  let open Types in
  let f = type_of_tyd schemas in
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
      | Tconstr (Pdot (Pident id,"t",_),[],_) 
        when (Ident.name id = "Uuid") -> Type.uuid
      | Tconstr (Pdot (Pident id,"id",_),[],_)  ->
          let tt = Tabletype.from_string @@ Ident.name id in
            Specelab.type_of_coltype (Coltype.Fkey tt) schemas
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
let rec doIt_expr env (expr:Typedtree.expression) = 
  let open Path in
  let is_table_mod id = 
    let tokens = Str.split (Str.regexp "_") (Ident.name id) in
      (List.length tokens >= 2) && (List.hd (List.rev tokens) = "table") in
  match expr.exp_desc with
    (* id *)
    | Texp_ident (Pident id,_,_) -> 
        let name = Ident.name id in
          begin
            try (VE.find_name name env.ve, env)
            with Not_found -> 
              try let _ = TE.find_name name env.te in 
                (SymbolicVal.Id id, env)
              with Not_found -> failwith @@ name^" not found\n"
          end
    (* EffCons {id1=sv1; id2=sv2; ..}  *)
    | Texp_construct (_,cons_desc, pats) ->
        failwith "Texp_construct Unimpl."
    (* Obj_table.get e1 e2 *)
    | Texp_apply ({exp_desc=Texp_ident (Pdot (Pident id,"get",_),_,_)},largs) 
      when (is_table_mod id) -> 
        let args = map_snd_opts largs in
        let (svs,env') = 
          List.map_fold_left 
            (fun env arg -> doIt_expr env arg) env args in
        let _ = Printf.printf "# of args: %s\n" 
                  (string_of_int @@ List.length args) in
          failwith "Unimpl."
    (* let id = e1 in e2 *)
    | Texp_let (Asttypes.Nonrecursive, 
                [{vb_pat={pat_desc=Tpat_var (id,_)};vb_expr=e1}], e2) -> 
        let (sv1,env1) = doIt_expr env e1 in
        let env' = {env1 with ve = VE.add id sv1 env1.ve} in
          doIt_expr env' e2
    | _ -> failwith "Unimpl."

(*
 * doIt_fun : env -> 
 *)
let doIt_fun env rdt_spec (Fun.T {args_t;body}) =
  let Rdtspec.T {schemas} = rdt_spec in
  let args_reftys = 
    List.map (fun (id,tyd) -> (ident_of_id id, 
                               RefTy.trivial @@ type_of_tyd schemas tyd)) 
      args_t in
  let te' = List.fold_left (fun te (id,refty) -> TE.add id refty te)
              env.te args_reftys in
  let _ = doIt_expr {env with te=te'} body in
  failwith "Unimpl."

let doIt env rdt_spec effs = 
  let Rdtspec.T {schemas; reads; writes; aux} = rdt_spec in
  let my_fun = List.find (fun (Fun.T x) -> 
                            Id.to_string x.name = "do_new_tweet")
                 writes in
  let _ = doIt_fun env rdt_spec my_fun in
    failwith "Unimpl."
