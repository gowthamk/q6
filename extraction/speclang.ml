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
                 rec_flag: bool;
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression}

  let anonymous = Ident.create ""

  let make ?(name=anonymous) ~rec_flag ~args_t ~res_t ~body = 
    T {name=name; rec_flag=rec_flag; args_t=args_t; 
       res_t=res_t; body=body}
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
        | GT (sv1,sv2) -> (f sv1)^" > "^(f sv2)
        | LT (sv1,sv2) -> (f sv1)^" < "^(f sv2)
        | Not sv -> "~("^(f sv)^")"
        | And svs -> "("^(String.concat " && " @@ List.map f svs)^")"
        | Or svs -> "("^(String.concat " || " @@ List.map f svs)^")"
        | ConstInt i -> string_of_int i
        | ConstBool b -> string_of_bool b
        | ConstString s -> s
        | ConstUnit -> "()"
        | List (svs,s) -> (String.concat "::" @@ List.map f svs)
            ^(match s with | None -> "" | Some sv -> "::"^(f sv))
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
end

module Predicate =
struct
  type t = BoolExpr of SymbolicVal.t
    | If of SymbolicVal.t * SymbolicVal.t 
    | Forall of ((Ident.t * Type.t) list -> t)

  let of_sv sv = BoolExpr sv

  module SV = SymbolicVal

  let to_string = function BoolExpr sv -> SV.to_string sv
    | If (sv1,sv2) -> (SV.to_string sv1)^" => "^(SV.to_string sv2)
    | _ -> failwith "P.to_string Unimpl."
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
end
