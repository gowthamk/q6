open Typedtree

module Type = 
struct
  type t = Any | Int | Bool | String | Other of Ident.t
    | Arrow of t*t | List of t | Pair of t*t
    | Option of t

  let rec to_string = function Any -> "any"
    | Int -> "int" | Bool -> "bool" | String -> "string"
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

module Kind = 
struct
 type t = Uninterpreted 
        | Variant of Cons.t list (* Cons.t includes a recognizer *)
        | Extendible of Ident.t list ref
end

module SymbolicVal = 
struct
  type t = Bot
    | Id of Ident.t
    | App of Ident.t * typed list
    | Eq of typed * typed
    | GEq of typed * typed
    | LEq of typed * typed
    | Not of typed
    | And of typed list
    | ConstInt of int
    | ConstBool of bool
    | ConstString of string
    | List of typed list (* manifest prefix *) * 
              typed option (* unmanifest suffix *)
    | ITE of typed * typed * typed
    | Closure of ((Ident.t * Type.t) -> typed)
    | Construct of (Ident.t * typed) list
 and typed = t * Type.t
end

module Refinement =
struct
  type t = BoolExpr of SymbolicVal.t
    | Forall of ((Ident.t * Type.t) list -> t)
end

module RefinementType = 
struct
  type t = Base of Ident.t * Type.t * Refinement.t
    | Arrow of (Ident.t * t) * t
    | Trivial of Type.t

  let trivial_arrow (ty1,ty2) = Trivial (Type.Arrow (ty1,ty2))

  let trivial t = Trivial t
end
