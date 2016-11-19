open Types
open Typedtree

module Type = 
struct
  type t = Any | Int | Bool | String | Other of Ident.t
    | Arrow of t*t | List of t | Pair of t*t
    | Option of t | Unit

  let rec to_string = function Any -> "any"
    | Int -> "int" | Bool -> "bool" 
    | String -> "string" | Unit -> "unit"
    | Other id -> Ident.name id
    | Arrow (t1,t2) -> (to_string t1)^" -> "^(to_string t2)
    | List t -> (to_string t)^" list"
    | Pair (t1,t2) -> "("^(to_string t1)^","^(to_string t2)^")"
    | Option t -> (to_string t)^" option"

  let other s = Other (Ident.create s)
  let oper = other "Oper"
  let id = other "Id"
  let uuid = other "UUID"
  let eff = other "Eff"
  let ssn = other "Ssn"
  let objtyp = other "ObjType"
  let is_oper t = (t = oper)
  let is_eff t = 
    let _ = Printf.printf "is_eff(%s)\n" (to_string t) in 
      (t = eff)
  let _of str = match str with
    |"Oper" -> oper | "id" -> id | "Eff" -> eff | "Ssn" -> ssn
    | "UUID" -> uuid | "ObjType" -> objtyp | "unit" -> Unit
    | _ -> failwith "Type._of: Unexpected"
end

module Cons = 
struct
  type t = T of {name: Ident.t; 
                 recognizer: Ident.t; 
                 args: (Ident.t * Type.t) list}
  let isNop = Ident.create "isNOP"
  let nop = T {name = Ident.create "NOP";
               recognizer = isNop; 
               args = []}
  let name (T {name}) = name
end

module Fun = 
struct
  type t = T of {name: Ident.t; 
                 rec_flag: bool;
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression}

  let name (T {name}) = name

  let anonymous = Ident.create "<anon>"

  let make ?(name=anonymous) ~rec_flag ~args_t ~res_t ~body = 
    T {name=name; rec_flag=rec_flag; args_t=args_t; 
       res_t=res_t; body=body}
end

module Kind = 
struct
 type t = Uninterpreted 
        | Variant of Cons.t list (* Cons.t includes a recognizer *)
        | Enum of Ident.t list
        | Extendible of Ident.t list ref
        | Alias of Type.t

  let to_string = function Uninterpreted -> "Uninterpreted type"
    | Variant cons_list -> 
        let cons_names = List.map 
                           (fun (Cons.T {name}) -> Ident.name name)
                           cons_list in
          "Variant ["^(String.concat "," cons_names)^"]"
    | Enum ids -> 
        let id_names = List.map
                         (fun id -> Ident.name id) ids in
          "Enum ["^(String.concat "," id_names)^"]"
    | Extendible ids -> 
        let id_names = List.map
                         (fun id -> Ident.name id) !ids in
          "Extendible ["^(String.concat "," id_names)^"]"
    | Alias typ -> "Alias of "^(Type.to_string typ)
end

module L = 
struct
  let objid = Ident.create "objid"
  let objtyp = Ident.create "objtyp"
  let oper = Ident.create "oper"
  let vis = Ident.create "vis"
  let so = Ident.create "so"
  let hb = Ident.create "hb"
  let sameobj = Ident.create "sameobj"
  let ssn = Ident.create "ssn"
  let seqno = Ident.create "seqno"
  let mkkey_string = Ident.create "mkkey_string"
  let mkkey_UUID = Ident.create "mkkey_UUID"
  let mkkey = function "string" -> mkkey_string
    | "UUID" -> mkkey_UUID
    | _ -> failwith "mkkey not available"
  let isSome = Ident.create "isSome"
  let isNone = Ident.create "isNone"
  let fromJust = Ident.create "fromJust"
  let nop = Ident.create "Nop"
  let show = Ident.create "show"
end

module SymbolicVal = 
struct
  type t = Bot
    | Var of Ident.t
    | App of Ident.t * t list
    | Eq of t * t
    | Gt of t * t
    | Lt of t * t
    | Not of t
    | And of t list
    | Or of t list
    | ConstInt of int
    | ConstBool of bool
    | ConstString of string
    | ConstUnit
    | List of t list (* manifest prefix *) * 
              t option (* unmanifest suffix *)
    | Option of t option
    | ITE of t * t * t
    | Fun of Fun.t (* No closures. Only functions. *)
    | Record of (Ident.t * t) list
    | EffCons of Cons.t
    | NewEff of Cons.t * t option

  let rec to_string x =
    let f = to_string in
    let g x = "("^(f x)^")" in
      match x with
        | Var id -> Ident.name id
        | App (id,svs) -> (Ident.name id)^"("
            ^(String.concat "," @@ List.map f svs)^")"
        | Eq (sv1,sv2) -> (f sv1)^" = "^(f sv2)
        | Gt (sv1,sv2) -> (f sv1)^" > "^(f sv2)
        | Lt (sv1,sv2) -> (f sv1)^" < "^(f sv2)
        | Not sv -> "~("^(f sv)^")"
        | And svs -> "("^(String.concat " && " @@ List.map f svs)^")"
        | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
        | ConstInt i -> string_of_int i
        | ConstBool b -> string_of_bool b
        | ConstString s -> s
        | ConstUnit -> "()"
        | List (svs,s) -> (String.concat "::" @@ List.map f svs)
            ^(if List.length svs = 0 then "" else "::")
            ^(match s with | None -> "[]" | Some sv -> f sv)
        | Option None -> "None" 
        | Option (Some sv) -> "Some "^(g sv)
        | ITE (grd,sv1,sv2) -> (g grd)^"?"^(g sv1)^":"^(g sv2)
        | Fun (Fun.T {name}) -> "Fun "^(Ident.name name)
        | Record flds -> "{"^(String.concat "; " @@ 
                List.map 
                  (fun (id,sv) -> (Ident.name id)^" = "^(f sv)) flds)^"}"
        | EffCons (Cons.T {name}) -> "Cons "^(Ident.name name)
        | NewEff (Cons.T {name},None) -> Ident.name name 
        | NewEff (Cons.T {name},Some sv) -> (Ident.name name)^(g sv)


  let nil = List ([],None)

  let cons = function (x, List (xs,s)) -> List (x::xs,s)
    | (x, s) -> List ([x],Some s)

  let none = Option None

  let some x = Option (Some x)

  (*
   * Does a follow from assumps?
   *)
  let rec (|=) assumps a = 
    let assumps = List.concat @@ List.map 
                                   (function (And x) -> x 
                                      | x -> [x]) assumps in
      match a with 
        | _ when (List.mem (ConstBool false) assumps || 
                  List.mem a assumps) -> true
        | ConstBool true -> true
        | And vs -> List.for_all (fun v -> assumps |= v) vs
        | Or vs -> List.exists (fun v -> assumps |= v) vs
        | _ -> false
  (*
   * Simplifies gv by applying algebraic rules until fixpoint.
   * Returns a gv' s.t., (assumps |- gv' <=> gv) and 
   * size(gv') ≤ size(gv). 
   *)
  let rec simplify assumps gv = 
    let ret str v = v in
    match gv with
      (* (isSome (a? Some b : None))? d : e ---> a? d : e *)
      | App (_isSome, [ITE (a, 
                            Option (Some b), 
                            Option None)])
        when (_isSome = L.isSome) -> simplify assumps a
      | App (_fromJust, [Option (Some a)])
        when (_fromJust = L.fromJust) -> simplify assumps a
      | App (f,v2s) -> 
          let v2s' = List.map (simplify assumps) v2s in
          let same = List.map2 (=) v2s v2s' in
          let all_same = List.fold_left (&&) true same in 
            if all_same then gv 
            else simplify assumps (App (f, v2s'))
      | ITE (a,b,c) when (assumps |= a) -> simplify assumps b
      | ITE (a,b,c) when (assumps |= (Not a)) -> simplify assumps c
      | ITE (a, ITE (b,c,d), e) when (d = e) -> 
          simplify assumps @@ ITE (And [a;b], c, d)
      | ITE (a,b,c) -> 
          let a' = simplify assumps a in
          let b' = simplify (a::assumps) b in 
          let c' = simplify ((Not a)::assumps) c in
            if a'=a && b'=b && c'=c then gv
            else simplify assumps @@ ITE (a',b',c')
      | Option (Some a) -> 
          let a' = simplify assumps a in
            if a'= a then gv else simplify assumps @@ Option (Some a')
      | And [] -> ret "1" @@ ConstBool true
      | And [sv] -> ret "2" @@ simplify assumps sv
      | And svs when (List.exists (fun sv -> assumps |= sv) svs) -> 
          ret "3" @@ simplify assumps @@ 
              And (List.filter (fun sv -> not (assumps |= sv)) svs)
      | And svs when (List.exists (function (And _) -> true
                                     | _ -> false) svs) ->
          ret "4" @@ simplify assumps @@ 
              And (List.concat @@ List.map (function (And svs') -> svs'
                                              | sv -> [sv]) svs)
      | And svs -> 
          let do_simplify sv = 
            simplify ((List.filter (fun sv' -> sv' <> sv) svs)@assumps) sv in
          let svs' = List.map do_simplify svs in
          let same = List.map2 (=) svs svs' in
          let all_same = List.fold_left (&&) true same in 
            if all_same then ret "5" gv 
            else simplify assumps @@ And svs'
      | Or [] -> ConstBool true
      | Or [sv] -> simplify assumps sv
      | Or svs when (List.exists (fun sv -> assumps |= sv) svs) -> 
          ConstBool true
      | Or svs when (List.exists (function (Or _) -> true
                                     | _ -> false) svs) ->
          simplify assumps @@ 
            Or (List.concat @@ List.map (function (Or svs') -> svs'
                                          | sv -> [sv]) svs)
      | Or svs -> 
          let do_simplify sv = simplify assumps sv in
          let svs' = List.map do_simplify svs in
          let same = List.map2 (=) svs svs' in
          let all_same = List.fold_left (&&) true same in 
            if all_same then gv 
            else simplify assumps @@ Or svs'
      | Eq (v1,v2) when (v1 = v2) -> ConstBool true
      | Eq (v1,v2) -> 
          let (v1',v2') = (simplify assumps v1, simplify assumps v2) in
            if v1'=v1 && v2'=v2 then gv 
            else simplify assumps @@ Eq (v1',v2') 
      | Not (ConstBool true) -> ConstBool false
      | Not (ConstBool false) -> ConstBool true
      | Not v -> let v' = simplify assumps v in 
          if v'=v then gv else simplify assumps @@ Not v'
      | _ -> gv

  let ite (v1,v2,v3) = simplify [] @@ ITE (v1,v2,v3)
  let app ((v1:Ident.t),(v2s : t list)) = simplify [] @@ App (v1,v2s)
end

module Predicate =
struct
  type t = BoolExpr of SymbolicVal.t
    | If of t * t 
    | Iff of t * t 
    | Forall of (Ident.t * Type.t) list * t
    | Exists of (Ident.t * Type.t) list * t

  module S = SymbolicVal

  let of_sv sv = BoolExpr (S.simplify [] sv)

  let of_svs svs = match svs with
    | [] -> BoolExpr (S.ConstBool true)
    | _ -> BoolExpr (S.simplify [] @@ S.And svs)

  let rec to_string = function BoolExpr sv -> S.to_string sv
    | If (v1,v2) -> (to_string v1)^" => "^(to_string v2)
    | Iff (v1,v2) -> (to_string v1)^" <=> "^(to_string v2)
    | Forall (bvs, t) -> 
        "∀("^(String.concat "," @@ 
                List.map (fun (id,ty) -> 
                            (Ident.name id)^":"^(Type.to_string ty)) bvs)
        ^"). "^(to_string t)
    | Forall (bvs, t) -> 
        "∃("^(String.concat "," @@ 
                List.map (fun (id,ty) -> 
                            (Ident.name id)^":"^(Type.to_string ty)) bvs)
    | _ -> failwith "P.to_string Unimpl."

  let _if (t1,t2) = match (t1,t2) with
    | (BoolExpr (S.ConstBool true), _) -> t2
    | (BoolExpr v1, BoolExpr v2)  -> 
        let v1' = S.simplify [] v1 in
          if v1' = S.ConstBool false 
          then BoolExpr (S.ConstBool true)
          else let v2' = S.simplify [v1'] v2 in
                  If (BoolExpr v1', BoolExpr v2')
    | _ -> If (t1,t2)

  let _iff (t1,t2) = Iff (t1,t2)
end

module Misc =
struct

  let rec uncurry_arrow = function 
    (Tarrow (_,typ_expr1,typ_expr2,_)) ->
      let (ty1,ty2) = (typ_expr1.desc, typ_expr2.desc) in 
        begin
          match ty2 with 
              Tarrow _ -> (fun (x,y) -> (ty1::x,y)) (uncurry_arrow ty2)
            | _ -> ([ty1],ty2)
        end
  | Tlink typ_expr -> uncurry_arrow @@ typ_expr.desc
  | _ -> failwith "uncurry_arrow called on non-arrow type"

  let to_tye tyd = let open Types in
    {desc=tyd; level=0; id=0}

  let rec extract_lambda ({c_lhs; c_rhs}) : (Ident.t list * expression)= 
    let open Asttypes in
    match (c_lhs.pat_desc, c_rhs.exp_desc) with
      | (Tpat_var (id,loc), Texp_function (_,[case],_)) -> 
          let (args,body) = extract_lambda case in
            (id::args,body)
      | (Tpat_var (id,loc), _) -> ([id], c_rhs)
      | (Tpat_alias (_,id,_), Texp_function (_,[case],_) ) -> 
          let (args,body) = extract_lambda case in
            (id::args,body)
      | (Tpat_alias (_,id,loc), _) -> ([id], c_rhs)
      | _ -> failwith "Unimpl. Specverify.extract_lambda"

  let curry arg_tyds (res_tyd : Types.type_desc) =  
    let open Types in let open Asttypes in
    let f tyd = {desc=tyd; level=0; id=0} in
      List.fold_right (fun arg_tyd arr -> 
                         Tarrow (Nolabel, f arg_tyd, f arr, Cunknown))
        arg_tyds res_tyd 

  let mk_tvar_name name_op id = match name_op with
    | Some a -> a^(string_of_int id)
    | None -> "tvar("^(string_of_int id)^")"

  let rec unify_tyes binds tye1 tye2 = 
    let open Types in
    let (tyd1,tyd2) = (tye1.desc, tye2.desc) in
    let doIt_list = List.fold_left2 unify_tyes binds in
    let fail () = 
      let strf =Format.str_formatter  in
      begin
        Format.fprintf strf "Following types cannot be unified:\n";
        Printtyp.raw_type_expr strf tye1;
        Format.fprintf strf "\n";
        Printtyp.raw_type_expr strf tye2;
        Printf.printf "%s\n" @@ Format.flush_str_formatter ();
        failwith "Unification failure"
      end in
    let assrt b = if b then () else failwith "not unifiable" in
      match (tyd1,tyd2) with
        (* 
         * One of tye1 and tye2 is a concrete type, but we don't
         * know which one.
         *)
        | (Tvar aop, _) | (Tunivar aop, _) 
        | (_, Tvar aop) | (_, Tunivar aop) -> 
            let a = mk_tvar_name aop tye1.id in
              if List.mem_assoc a binds then binds 
              else (a,tye2)::binds
        | (Ttuple [tye1],_) -> unify_tyes binds tye1 tye2
        | (Tarrow (_,tye11,tye12,_), Tarrow (_,tye21,tye22,_)) ->
            unify_tyes (unify_tyes binds tye11 tye21) tye12 tye22
        | (Ttuple tyes1, Ttuple tyes2) -> 
            let _ = assrt (List.length tyes1 = List.length tyes2) in
              doIt_list tyes1 tyes2
        | (Tconstr (path1,tyes1,_), Tconstr (path2,tyes2,_)) ->
            let _ = assrt (Path.same path1 path2) in
              doIt_list tyes1 tyes2
        | (Tlink tye1,_) -> unify_tyes binds tye1 tye2
        | (_, Tlink tye2) -> unify_tyes binds tye1 tye2
        | (Tarrow _,_) | (_, Tarrow _) | (Ttuple _,_) | (_,Ttuple _)
        | (Tconstr _,_) | (_,Tconstr _) -> fail ()
        | _ -> failwith "unify_tyes: Unimpl."

  let unify_tyes tye1 tye2 = 
    let tyebinds = unify_tyes [] tye1 tye2 in
    (*let strf = Format.str_formatter in
    let print_bind (a,tye) = 
      begin
        Format.fprintf strf "%s :-> " a;
        Printtyp.type_expr strf tye;
        Printf.printf "%s\n" @@ Format.flush_str_formatter ()
      end in
    let _ = List.iter print_bind tyebinds in*)
      tyebinds

end
