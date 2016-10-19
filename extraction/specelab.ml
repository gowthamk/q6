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
open Rdtspec
open Speclang
module RefTy = RefinementType

module KE = Light_env.Make(struct type t = Kind.t end)
module TE = Light_env.Make(struct type t = RefinementType.t end)
module VE = Light_env.Make(struct type t = SymbolicVal.t end)

let (<<) f g x = f(g x)

let rec type_of_coltype coltype schemas = 
  let coltype_of_id tt = 
    let Tableschema.T {id_t} = List.assoc tt schemas in
      id_t in
  let f x = type_of_coltype x schemas in
    match coltype with 
      | Coltype.Int -> Type.Int
      | Coltype.String -> Type.String
      | Coltype.Bool -> Type.Bool
      | Coltype.UUID -> Type.uuid
      | Coltype.Fkey tt -> f @@ coltype_of_id tt

let mk_cons (Effcons.T {name; args_t}) schemas : Cons.t = 
  let str = Id.to_string name in
  let name = Ident.create str  in
  let recognizer = Ident.create @@ "is"^str in
  let args = List.map 
               (fun (id,colty) -> (Ident.create @@ Id.to_string id,
                                   type_of_coltype colty schemas))
               args_t in
    Cons.T {name=name; recognizer=recognizer; args=args}

let extract_oper_kind schemas = 
  let eff_cons_in_ts (ts) : Cons.t list =
    let Tableschema.T {eff_t=Efftyp.T conss} = ts in
      List.map (fun cons -> mk_cons cons schemas) conss in
  let all_cons = List.concat @@ 
                  List.map (eff_cons_in_ts << snd) schemas in
    Kind.Variant all_cons

let bootstrap_KE schemas = 
  let table_types = List.map fst schemas in
  let id_of_tt tt = Id.from_string @@ Tabletype.to_string tt in
  let add_ObjType = 
    let all_cons = List.map 
                  (fun tt -> mk_cons 
                              (Effcons.T {name=id_of_tt tt;
                                          args_t=[]}) schemas) table_types in
      KE.add (Ident.create "ObjType") (Kind.Variant all_cons) in
  (*
   * Effect Ids can have various types, e.g, UUID or string. 
   * But we need id types of various effects to match in order
   * to define sameobj as equality of ids. We overcome the problem 
   * by defining one uninterpreted Id type, and then defining a 
   * seperate mkKey function for each type to convert to Id type. 
   * For instance, mkKey_string converts strings to Ids. All mkKey 
   * functions come with an axiom that if x!=y, then mkKey(x)!=mkKey(y).
   *)
  let add_Id = KE.add (Ident.create "Id") Kind.Uninterpreted in
  let add_Oper = KE.add (Ident.create "Oper") @@
                  extract_oper_kind schemas in
    List.fold_left (fun ke f -> f ke) KE.empty
      (* 
       * Type Eff is special; it will be defined when K is set.
       *)
      [add_ObjType; add_Id; add_Oper]

let bootstrap_TE schemas = 
  (*
   * All standard functions and relations will be defined in 
   * z3encode. We will only define application-specific ones here.
   *)
  (* 1. mkKey functions*)
  let id_types = List.map 
                   (fun (_,Tableschema.T {id_t}) -> 
                      type_of_coltype id_t schemas) schemas in
  let add_mkKey_for_type te typ = 
    let refTy = RefTy.trivial_arrow (typ, Type.id) in
    let id = Ident.create @@ "mkKey_"^(Type.to_string typ) in
      TE.add id refTy te in
  let add_mkKeys te = List.fold_left add_mkKey_for_type te id_types in
  (* 2. Effect argument accessors *)
  let all_eff_cons = match extract_oper_kind schemas with 
    | Kind.Variant c -> c | _ -> failwith "Impossible" in
  let doIt_eff_cons (Cons.T {args}) = 
    List.map (fun (id,typ) -> 
                (id,RefTy.trivial_arrow (Type.eff,typ))) args in
  let accessors = List.concat @@ List.map doIt_eff_cons all_eff_cons in
  let add_accessors te = List.fold_left 
                           (fun te (id,refty) -> TE.add id refty te)
                           te accessors in
    List.fold_left (fun te f -> f te) TE.empty
      [add_mkKeys; add_accessors]

let doIt (Rdtspec.T {schemas}) = 
  let ke = bootstrap_KE schemas in
  let te = bootstrap_TE schemas in
  let ve = VE.empty in
    (ke,te,ve)
