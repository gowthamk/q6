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
  let is_oper t = (t = oper)
  let is_eff t = (t = eff)
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
  let objtyp = Ident.create "obtyp"
  let oper = Ident.create "oper"
  let vis = Ident.create "vis"
  let so = Ident.create "so"
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

  let rec simplify assumps gv = 
    (* (isSome (a? Some b : None))? d : e ---> a? d : e *)
    match gv with
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
            if not all_same then simplify assumps (App (f, v2s'))
            else App (f,v2s)
      | ITE (a,b,c) -> if List.mem a assumps 
                       then simplify assumps b 
                       else if List.mem (Not a) assumps 
                       then simplify assumps b
                       else ITE (simplify assumps a, 
                                 simplify (a::assumps) b, 
                                 simplify ((Not a)::assumps) c)
      | _ -> gv

  let ite (v1,v2,v3) = simplify [] @@ ITE (v1,v2,v3)
  let app ((v1:Ident.t),(v2s : t list)) = simplify [] @@ App (v1,v2s)
end

module Predicate =
struct
  type t = BoolExpr of SymbolicVal.t
    | If of t * t 
    | Forall of ((Ident.t * Type.t) list -> t)

  module SV = SymbolicVal

  let of_sv sv = match sv with
    | SV.And [v] -> BoolExpr v
    | SV.Not (SV.And [v]) -> BoolExpr (SV.Not v) 
    | SV.Not (SV.And []) -> BoolExpr (SV.ConstBool false)
    | SV.Not (SV.ConstBool true) -> BoolExpr (SV.ConstBool false)
    | SV.Not (SV.ConstBool false) -> BoolExpr (SV.ConstBool true)
    | _ -> BoolExpr sv

  let of_svs svs = match svs with
    | [] -> BoolExpr (SV.ConstBool true)
    | [v] -> BoolExpr v
    | _ -> BoolExpr (SV.And svs)

  let rec to_string = function BoolExpr sv -> SV.to_string sv
    | If (v1,v2) -> (to_string v1)^" => "^(to_string v2)
    | _ -> failwith "P.to_string Unimpl."

  let _if (t1,t2) = match (t1,t2) with
    | (BoolExpr (SV.ConstBool true), BoolExpr v2) -> 
         BoolExpr (SV.simplify [] v2)
    | (BoolExpr (SV.ConstBool false), BoolExpr v2) -> 
         BoolExpr (SV.ConstBool true)
    | (BoolExpr v1, BoolExpr v2)  -> 
        let (v1',v2') = (SV.simplify [] v1, SV.simplify [v1] v2) in
          If (BoolExpr v1', BoolExpr v2')
    | _ -> If (t1,t2)
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
    (* let strf = Format.str_formatter in
    let print_bind (a,tye) = 
      begin
        Format.fprintf strf "%s :-> " a;
        Printtyp.type_expr strf tye.desc;
        Printf.printf "%s\n" @@ Format.flush_str_formatter ()
      end in
    let _ = List.iter print_bind tyebinds in *)
      tyebinds

end
