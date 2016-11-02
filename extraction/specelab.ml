(*
 * How do we define a type? One way is to define it as a disjoing union of
 * well-known types:
 *    type t = Int | Bool | String | Eff | Oper | List of t | Pair of t*t
 * But Oper has constructors. Where do we record them? Also, might encounter an
 * ML type during the execution that we would like to treat uninterpreted.
 * Where do we record it? Moreover, then we can have other types like ObjType
 * which also have constructors. Where do we record it? We thefore need a kind
 * environment.
 *    type kind_t = Uninterpreted 
 *      | Variant of Cons.t list (* Cons.t includes a recognizer *)
        | Extendible of Ident.t list ref
 * Now define type as:
 *    type t = Int | Bool | String | Other of Ident.t 
 *      Arrow of t * t | List of t | Pair of t*T
 *)
(*
 * Our aim while performing symbolic evaluation is to execute normal ML code on
 * symbolic values. The result of the execution is also a symbolic value. If the
 * code generates side effects, then those effects must also be part of the
 * result. A Quelea application contains multiple of side-effecting functions,
 * whose symbolic evaluation must return a symbolic value, an updated TE.t that
 * includes bindings for new effects and new uuids. Since each new uuid is
 * itself a constant, the function must also return an update KE.t with UUID
 * type updated to include the new constant. 
 *)
(*
 * Effect Ids can have various types, e.g, UUID or string. 
 * But we need id types of various effects to match in order
 * to define sameobj as equality of ids. We overcome the problem 
 * by defining one uninterpreted Id type, and then defining a 
 * seperate mkKey function for each type to convert to Id type. 
 * For instance, mkKey_string converts strings to Ids. All mkKey 
 * functions come with an axiom that if x!=y, then mkKey(x)!=mkKey(y).
 *)
open Rdtspec
open Speclang
module SV = SymbolicVal

module KE = Light_env.Make(struct include Kind end)
module TE = Light_env.Make(struct include Type end)
module VE = Light_env.Make(struct include SymbolicVal end)

let (<<) f g x = f(g x)

let rec type_of_coltype coltype schemas = 
  let coltype_of_id tt = 
    let (_,Tableschema.T {id_t}) = 
      try List.find (fun (tt',ts) -> Ident.equal tt tt') schemas 
      with Not_found -> failwith @@ (Ident.name tt)
                          ^" not found in schemas"
    in id_t in
  let f x = type_of_coltype x schemas in
    match coltype with 
      | Coltype.Int -> Type.Int
      | Coltype.String -> Type.String
      | Coltype.Bool -> Type.Bool
      | Coltype.UUID -> Type.uuid
      | Coltype.Fkey tt -> f @@ coltype_of_id tt

let mk_cons (Effcons.T {name; args_t}) schemas : Cons.t = 
  let recognizer = Ident.create @@ "is"^(Ident.name name) in
  let args = List.map 
               (fun (id,colty) -> (id, type_of_coltype colty schemas))
               args_t in
    Cons.T {name=name; recognizer=recognizer; args=args}

let extract_oper_cons (schemas) : (Ident.t * Cons.t) list = 
  let doIt_schema (tname,ts) =
    let Tableschema.T {eff_cons} = ts in
    let doIt_eff_cons (Effcons.T x) = 
      let prefix = Ident.name tname in
      let suffix = Ident.name x.name in
      let alias = Ident.create @@ prefix^"."^suffix in
      let new_name = Ident.create @@ prefix^"_"^suffix in
      let new_cons = Effcons.T {x with name = new_name} in
        (alias, mk_cons new_cons schemas) in
      List.map doIt_eff_cons eff_cons in
  let all_cons = List.concat @@ 
                  List.map doIt_schema schemas in
    all_cons

let bootstrap (Rdtspec.T {schemas; reads; writes; aux}) = 
  (* 1. ObjType typedef to KE *)
  let table_names = List.map fst schemas in
  let add_ObjType = 
    let all_cons = List.map 
                     (fun table_name -> mk_cons 
                              (Effcons.T {name=table_name;
                                          args_t=[]}) schemas) 
                     table_names in
      KE.add (Ident.create "ObjType") (Kind.Variant all_cons) in
  (* 2. Id typedef to KE *)
  let add_Id = KE.add (Ident.create "Id") Kind.Uninterpreted in
  let _ = Printf.printf "Id type...\n" in
  (* 3. Oper typedef to KE *)
  let aliased_oper_cons = extract_oper_cons schemas in
  let _ = Printf.printf "aliased_oper_cons ...\n" in
  let (_,oper_cons) = List.split aliased_oper_cons in
  let add_Oper = KE.add (Ident.create "Oper") 
                   (Kind.Variant oper_cons) in
  (* 4. Qualified effcons aliases to VE *)
  (* eg: "User.Add" :-> SV.EffCons (Cons.T {name="User_Add", ...}) *)
  let add_effcons_aliases ve = List.fold_left 
             (fun ve (alias,cons) -> 
                VE.add alias (SV.EffCons cons) ve) 
             ve aliased_oper_cons in
  let _ = Printf.printf "Effcons aliases ...\n" in
  (* 5. Oper constructor recognizers to TE *)
  (* eg: "isUser_Add" :-> Type.oper -> Type.Bool *)
  let add_Oper_recognizers te = 
    List.fold_left 
      (fun te (Cons.T {recognizer}) -> 
         let typ = Type.Arrow (Type.oper,Type.Bool) in 
           TE.add recognizer typ te) 
      te oper_cons in
  (* 6. Eff attribute accessors to TE *)
  (* eg: "user_name" :-> Type.eff -> Type.String *)
  let typed_accessors_of (Cons.T {args}) = 
    List.map (fun (id,typ) -> 
                (id, Type.Arrow (Type.eff,typ))) args in
  let accessors = List.concat @@ List.map 
                                   typed_accessors_of oper_cons in
  let add_Eff_accessors te = List.fold_left 
                           (fun te (id,refty) -> TE.add id refty te)
                           te accessors in
  (* 7. Qualified id type aliases to KE *)
  (* eg: User.id :-> Type.UUID *)
  (* TODO: Qualified eff type aliases to KE *)
  let aliased_id_types = List.map 
                   (fun (tname,Tableschema.T {id_t}) -> 
                      let alias = Ident.create @@ 
                                    (Ident.name tname)^".id" in
                      let id_typ = type_of_coltype id_t schemas in
                        (alias,id_typ)) schemas in
  let add_Id_aliases te = List.fold_left 
                               (fun te (alias,typ) -> 
                                  KE.add alias (Kind.Alias typ) te)
                               te aliased_id_types in
  (* 8. mkKey functions to TE *)
  let (_,id_types) = List.split aliased_id_types in
  let add_mkKey_for_type te typ = 
    let refTy = Type.Arrow (typ, Type.id) in
    let id = Ident.create @@ "mkKey_"^(Type.to_string typ) in
      TE.add id refTy te in
  let add_mkKeys te = List.fold_left add_mkKey_for_type te id_types in
  (* 9. Add all funs to VE *)
  let add_funs ve = List.fold_left 
                      (fun ve (Fun.T {name} as fun_t) -> 
                        VE.add name (SV.Fun fun_t) ve) 
                      ve (reads @ writes @ aux) in
  (* 10. UUID type def to KE *)
  let add_UUID ke = 
    KE.add (Ident.create "UUID") (Kind.Extendible (ref [])) ke in
  (*
  (* 11. Uuid.create to TE *)
  let add_Uuid_create te = 
    let typ = Type.Arrow (Type.Unit,Type.uuid) in
    let id = Ident.create "Uuid.create" in
      TE.add id typ te in
  (* 12. Pervasives.@@ to TE *)
  let add_Pervasives_atat te = 
    let typ = Type.Any in
    let id = Ident.create "Pervasives.@@" in
      TE.add id typ te in
  (* 13. Pervasives.raise to TE *)
  let add_Pervasives_raise te = 
    let typ = Type.Any in
    let id = Ident.create "Pervasives.raise" in
      TE.add id typ te in
   *)
  (* 14. Inconsistency to VE *)
  let add_Inconsistency ve = 
    let id = Ident.create "Inconsistency" in
    let sv = SV.EffCons (Cons.T {name=id; 
                                 recognizer=id (*dummy*);
                                 args=[]}) in
      VE.add id sv ve in

  (* bootstrap KE *)
  let ke = List.fold_left (fun ke f -> f ke) KE.empty
      [add_ObjType; add_Id; add_Id_aliases; add_Oper; add_UUID] in
  (* bootstrap TE *)
  let te = List.fold_left (fun te f -> f te) TE.empty
      [add_Oper_recognizers; add_Eff_accessors; add_mkKeys] in
  (* bootstrap VE *)
  let ve = List.fold_left (fun ve f -> f ve) VE.empty
      [add_effcons_aliases; add_funs; add_Inconsistency] in
    (ke,te,ve)

let doIt rdt_spec = 
  let (ke,te,ve) = bootstrap rdt_spec in
    (ke,te,ve)
