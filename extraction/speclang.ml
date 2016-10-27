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
end

module Cons = 
struct
  type t = T of {name: Ident.t; 
                 recognizer: Ident.t; 
                 args: (Ident.t * Type.t) list}
end

module Fun = 
struct
  type t = T of {name: Ident.t; 
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression}
  let make ~name ~args_t ~res_t ~body = 
    T {name=name; args_t=args_t; res_t=res_t; body=body}
end

module Kind = 
struct
 type t = Uninterpreted 
        | Variant of Cons.t list (* Cons.t includes a recognizer *)
        | Extendible of Ident.t list ref
        | Alias of Type.t

  let to_string = function Uninterpreted -> "Uninterpreted type"
    | Variant cons_list -> 
        let cons_names = List.map 
                           (fun (Cons.T {name}) -> Ident.name name)
                           cons_list in
          "Variant ["^(String.concat "," cons_names)^"]"
    | Extendible ids -> 
        let id_names = List.map
                         (fun id -> Ident.name id) !ids in
          "Extendible ["^(String.concat "," id_names)^"]"
    | Alias typ -> "Alias of "^(Type.to_string typ)
end

module SymbolicVal = 
struct
  type t = Bot
    | Var of Ident.t
    | App of Ident.t * t list
    | Eq of t * t
    | GT of t * t
    | LT of t * t
    | Not of t
    | And of t list
    | Or of t list
    | ConstInt of int
    | ConstBool of bool
    | ConstString of string
    | List of t list (* manifest prefix *) * 
              t option (* unmanifest suffix *)
    | Option of t option
    | ITE of t * t * t
    | Fun of Fun.t
    | EffCons of Cons.t
    | NewEff of Cons.t * (Ident.t * t) list

  let rec to_string x =
    let f = to_string in
    let g x = "("^(f x)^")" in
      match x with
        | Var id -> Ident.name id
        | App (id,svs) -> (Ident.name id)^"("
            ^(String.concat "," @@ List.map f svs)^")"
        | Eq (sv1,sv2) -> (f sv1)^" = "^(f sv2)
        | GT (sv1,sv2) -> (f sv1)^" > "^(f sv2)
        | LT (sv1,sv2) -> (f sv1)^" < "^(f sv2)
        | Not sv -> "~("^(f sv)^")"
        | And svs -> "("^(String.concat " && " @@ List.map f svs)^")"
        | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
        | ConstInt i -> string_of_int i
        | ConstBool b -> string_of_bool b
        | List (svs,s) -> (String.concat "::" @@ List.map f svs)
            ^(match s with | None -> "" | Some sv -> "::"^(f sv))
        | Option None -> "None" 
        | Option (Some sv) -> "Some "^(g sv)
        | ITE (grd,sv1,sv2) -> (g grd)^"?"^(g sv1)^":"^(g sv2)
        | Fun (Fun.T {name}) -> "Fun "^(Ident.name name)
        | EffCons (Cons.T {name}) -> "Cons "^(Ident.name name)
        | NewEff _ -> "new eff"


  let nil = List ([],None)

  let cons = function (x, List (xs,s)) -> List (x::xs,s)
    | (x, s) -> List ([x],Some s)
end

module Predicate =
struct
  type t = BoolExpr of SymbolicVal.t
    | If of t * t 
    | Forall of ((Ident.t * Type.t) list -> t)
end
