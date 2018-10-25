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
 * seperate mkkey function for each type to convert to Id type. 
 * For instance, mkkey_string converts strings to Ids. All mkkey 
 * functions come with an axiom that if x!=y, then mkkey(x)!=mkkey(y).
 *)
open Rdtspec
open Speclang
module SV = SymbolicVal

module TE = Light_env.Make(struct include Type end)

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

let bootstrap (Rdtspec.T {schemas; reads; writes; invs; aux}) = 
  (* 1. ObjType typedef to KE *)
  let table_names = List.map fst schemas in
  let add_ObjType ke = 
    (* ObjType constructors are tablenames *)
    KE.add (Ident.create "ObjType") (Kind.Enum table_names) ke in
  (* 2. Id typedef to KE *)
  let add_Id ke = KE.add (Ident.create "Id") Kind.Uninterpreted ke in
  (* 2.5 ReplId typedef to KE. Hardcoding to 3 replicas currently. *)
  let add_ReplId ke = 
      KE.add (Type.other_id Type.replid) 
             (Kind.Enum L.replids) ke in
  (* 3. Oper typedef to KE *)
  let aliased_oper_cons = extract_oper_cons schemas in
  let (_,oper_cons) = List.split aliased_oper_cons in
  (* Nop is also an Oper cons *)
  let oper_cons = oper_cons@[Cons.nop] in
  (* Oper type is an enum type *)
  let oper_names = List.map Cons.name oper_cons in
  let add_Oper = KE.add (Type.other_id Type.oper) 
                   (Kind.Enum oper_names) in
  (* 4. Qualified effcons aliases to VE *)
  (* eg: "User.Add" :-> SV.EffCons (Cons.T {name="User_Add", ...}) *)
  let add_effcons_aliases ve = List.fold_left 
             (fun ve (alias,cons) -> 
                VE.add alias (SV.EffCons cons) ve) 
             ve aliased_oper_cons in
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
  (* eg: VE[user_id :-> user_id]; to user the same ident for many
   * applications of user_id accessor *)
  let add_accessor_svs ve = List.fold_left 
                           (fun ve (id,_) ->VE.add id (SV.Var id) ve)
                           ve accessors in
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
  (* 8. mkkey functions to TE *)
  let (_,id_types) = List.split aliased_id_types in
  let add_mkkey_for_type te typ = 
    let refTy = Type.Arrow (typ, Type.id) in
    let id = Ident.create @@ "mkkey_"^(Type.to_string typ) in
      TE.add id refTy te in
  let add_mkkeys te = List.fold_left add_mkkey_for_type te id_types in
  (* Added as a hack to make the first version of commutativity
   * implementation work for the Microblog application *)
	let add_mkkey_int te = 
    TE.add (Ident.create @@ "mkkey_int") (Type.Arrow (Type.Int, Type.id)) te in
  (* 9. Add reads, writes and aux funs to VE *)
  let add_funs ve = List.fold_left 
                      (fun ve (Fun.T {name} as fun_t) -> 
                        VE.add name (SV.Fun fun_t) ve) 
                      ve (reads @ writes @ aux) in
  (* 10. UUID type def to KE *)
  let add_UUID ke = 
    KE.add (Ident.create "UUID") (Kind.Extendible (ref [])) ke in
  (* 11. Txn type def to KE *)
  let add_Txn ke = 
    let enums = List.map Fun.name (invs @ writes) in 
      (* We also add a nop txn for NOP effects *)
      KE.add  (Type.other_id Type.txn)
        (Kind.Enum (enums@[L.txn_nop(*; L.generic_inv*)])) ke in
  (* 12. txn function to TE *)
  let add_txn te = 
    let typ = Type.Arrow (Type.eff,Type.txn) in
      TE.add L.txn typ te in
  (* 13. seqno function to TE *)
  let add_seqno te = 
    let typ = Type.Arrow (Type.eff,Type.Int) in
    let id = Ident.create "seqno" in
      TE.add id typ te in
  (*13a. currtxn function to TE *)
  let add_currtxn te = 
    let typ = Type.Arrow (Type.eff,Type.Bool) in
    let id = Ident.create "currtxn" in
      TE.add id typ te in
  (* 14. Inconsistency to VE *)
  let add_Inconsistency ve = 
    let id = Ident.create "Inconsistency" in
    let sv = SV.EffCons (Cons.T {name=id; 
                                 recognizer=id (*dummy*);
                                 args=[]}) in
      VE.add id sv ve in
  (* 15. objid, obtype and oper functions to TE *)
  let add_objid te = 
    let typ = Type.Arrow (Type.eff,Type.id) in
      TE.add (L.objid) typ te in
  let add_objtyp te = 
    let typ = Type.Arrow (Type.eff,Type.objtyp) in
      TE.add (L.objtyp) typ te in
  let add_oper te = 
    let typ = Type.Arrow (Type.eff,Type.oper) in
      TE.add (L.oper) typ te in
  (* 15.5. replid function to TE *)
  let add_replid te = 
    let typ = Type.Arrow (Type.eff,Type.replid) in
      TE.add (L.replid) typ te in
  (* 16. vis, so, hb, sameobj, and ar* relations to TE *)
  let add_rels te = 
    let typ = Type.Arrow (Type.eff,Type.Arrow (Type.eff, Type.Bool)) in
    let typ2 = Type.Arrow (Type.oper,Type.Arrow (Type.oper, Type.Bool)) in
    let typ3 = Type.Arrow (Type.id,Type.Arrow (Type.id, Type.Bool)) in
      TE.add (L.vis) typ @@ 
      TE.add (L.so) typ @@
      TE.add (L.hb) typ @@
      TE.add (L.sameobj) typ @@
      TE.add (L.ar) typ @@ 
      TE.add (L.ar_oper) typ2 @@ 
      TE.add (L.ar_id) typ3 te in
  (*16a. happens before relation for ids*)
  let add_hbid te =  
    let typ = Type.Arrow (Type.id,Type.Arrow (Type.id, Type.Bool)) in
      TE.add (L.hbid) typ te in
  (* 17. add show to TE *)
  let add_show te = 
    let typ = Type.Arrow (Type.eff, Type.Bool) in
      TE.add L.show typ te in
  (* 18. add Ssn type to KE *)
  let add_Ssn ke = 
    KE.add (Ident.create @@ Type.to_string Type.ssn) Kind.Uninterpreted ke in
  (* 19. ssn function to TE *)
  let add_ssn te = 
    let typ = Type.Arrow (Type.eff,Type.ssn) in
    let id = Ident.create "ssn" in
      TE.add id typ te in
  (* 20. add ssn_nop to TE *)
  let add_ssn_nop te = TE.add L.ssn_nop Type.ssn te in
  (* bootstrap KE *)
  let ke = List.fold_left (fun ke f -> f ke) KE.empty
      [add_ObjType; add_Id; add_Id_aliases; add_ReplId; 
       add_Oper; add_UUID; add_Txn; add_Ssn] in
  (* bootstrap TE *)
  let te = List.fold_left (fun te f -> f te) TE.empty
      [(*add_Oper_recognizers;*) add_Eff_accessors; add_mkkeys; 
       (* add_mkkey_int; *)add_ssn; add_ssn_nop; add_txn; 
       add_seqno; add_currtxn; add_objid; add_replid;
       add_objtyp; add_oper; add_rels; add_hbid; add_show] in
  (* bootstrap VE *)
  let ve = List.fold_left (fun ve f -> f ve) VE.empty
      [add_effcons_aliases; add_accessor_svs; add_funs; add_Inconsistency] in
    (ke,te,ve)

let doIt rdt_spec = 
  let (ke,te,ve) = bootstrap rdt_spec in
    (ke,te,ve)
