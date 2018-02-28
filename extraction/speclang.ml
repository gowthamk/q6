open Types
open Typedtree
open Printf
open Utils
open Light_env

let dprintf = function 
  | true -> Printf.printf
  | false -> (Printf.ifprintf stdout)
(* Debug print flags *)
let _dsimpl = ref false;;
let _dsimpl_asn = ref false;;

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
  let txn = other "Txn"
  let objtyp = other "ObjType"
  let is_oper t = (t = oper)
  let is_eff t = 
    (*let _ = Printf.printf "is_eff(%s)\n" (to_string t) in*) 
      (t = eff)
  let _of str = match str with
    |"Oper" -> oper | "id" -> id | "Eff" -> eff | "Ssn" -> ssn
    | "UUID" -> uuid | "ObjType" -> objtyp | "unit" -> Unit
    | "Txn" -> txn | _ -> failwith "Type._of: Unexpected"
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

module Kind = struct
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

module KE : (LIGHT_ENV with type elem = Kind.t) = 
  Light_env.Make(struct include Kind end)

module L = 
struct
  let objid = Ident.create "objid"
  let objtyp = Ident.create "objtyp"
  let oper = Ident.create "oper"
  let vis = Ident.create "vis"
  let so = Ident.create "so"
  let hb = Ident.create "hb"
  let sameobj = Ident.create "sameobj"
  let ar = Ident.create "ar"
  let ar_oper = Ident.create "ar_oper"
  let ar_id = Ident.create "ar_id"
  let ssn = Ident.create "ssn"
  let txn = Ident.create "txn"
  (* KE's addition *)
  let currtxn = Ident.create "currtxn"
  let hbid = Ident.create "hbid"
  (* KE's addition *)
  let seqno = Ident.create "seqno"
  let mkkey_string = Ident.create "mkkey_string"
  let mkkey_UUID = Ident.create "mkkey_UUID"
  let mkkey_int = Ident.create "mkkey_int"
  let mkkey = function "string" -> mkkey_string
    | "UUID" -> mkkey_UUID
    | "int" -> mkkey_int
    | _ -> failwith "mkkey not available"
  let isSome = Ident.create "isSome"
  let isNone = Ident.create "isNone"
  let fromJust = Ident.create "fromJust"
  let show = Ident.create "show"
  let e_nop = Ident.create "_ENOP"
  let ssn_nop = Ident.create "ssn_nop"
  let txn_nop = Ident.create "txn_nop"
end

module rec Fun : sig
  type t = T of {name: Ident.t; 
                 rec_flag: bool;
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression;
                 clos_ke: KE.t option;
                 clos_ve: VE.t option; 
                 clos_args : SymbolicVal.t list}
  val make : ?name:Ident.t ->
           rec_flag:bool ->
           args_t:(Ident.t * Types.type_desc) list ->
           res_t:Types.type_desc -> body:Typedtree.expression -> t
  val name : t -> Ident.t
  val anonymous : Ident.t
end = struct
  type t = T of {name: Ident.t; 
                 rec_flag: bool;
                 args_t: (Ident.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression;
                 clos_ke: KE.t option;
                 clos_ve: VE.t option;
                 clos_args : SymbolicVal.t list}

  let name (T {name}) = name

  let anonymous = Ident.create "<anon>"

  let make ?(name=anonymous) ~rec_flag ~args_t ~res_t ~body = 
    T {name=name; rec_flag=rec_flag; args_t=args_t; 
       clos_ve=None; clos_args=[]; clos_ke=None; 
       res_t=res_t; body=body}
end

and SymbolicVal : sig
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
    | EffCons of Cons.t (* Effect Constructor; to store in TE *)
    | NewEff of Cons.t * t option
    | DelayedITE of bool ref * t * t (* resolved only when necesary. *)
  val to_string : t -> string 
  val print : (< get : unit -> string; inc : unit -> 'a; .. > as 'a) ->
              t -> unit
  val simplify : t list -> t -> t
  val simplify_all : t list -> t list
  val ground : t -> t
  val ite : t * t * t -> t
  val cons : t * t -> t
  val nil : t
  val none : t
  val some : t -> t
  val app : Ident.t * t list -> t
end = struct
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
    | EffCons of Cons.t (* Effect Constructor; to store in TE *)
    | NewEff of Cons.t * t option
    | DelayedITE of bool ref * t * t (* resolved only when necesary. *)

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
        | Not sv -> "¬("^(f sv)^")"
        | And svs -> (String.concat " ∧ " @@ List.map f svs)
        | Or [Gt (s11,s12); Eq (s21,s22)] 
            when s11 = s21 && s12 = s22 -> (f s11)^" >= "^(f s12)
        | Or [Lt (s11,s12); Eq (s21,s22)] 
            when s11 = s21 && s12 = s22 -> (f s11)^" <= "^(f s12)
        | Or svs -> (String.concat " ∨ " @@ List.map f svs)
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
        | DelayedITE (x,v1,v2) -> "DelayedITE ("^(string_of_bool !x)
              ^","^(to_string v1)^","^(to_string v2)^")"
        
  let rec print ind x : unit =
    let f = to_string in
    let slen = String.length in
    let ind' = ind#inc ()  in
    let ind'' = ind'#inc () in
    let ind = ind#get () in
    let prints s = print_string (ind^s^"\n") in
    let print_bin rel (sv1,sv2) = 
      let (str1, str2) = (f sv1, f sv2) in
      let inline_s = Printf.sprintf "%s%s %s %s" 
                      ind str1 rel str2 in
        if slen inline_s <= 100 then
          printf "%s\n" inline_s
        else begin
          printf "%s(%s\n" ind rel;
          print ind' sv1;
          print ind' sv2;
          printf "%s)\n" ind;
        end in
    let print_un rel sv = 
      let str1 = f sv in
      let inline_s = Printf.sprintf "%s %s(%s)" 
                      ind rel str1 in
        if slen inline_s <= 100 then
          printf "%s\n" inline_s
        else begin
          printf "%s(%s\n" ind rel;
          print ind' sv;
          printf "%s)\n" ind
        end in
    let print_mult rel svs = 
      let sep = " "^rel^" " in
      let str = String.concat sep @@ List.map f svs in
      let inline_s = Printf.sprintf "%s%s" ind str in
        if slen inline_s <= 100 then
          printf "%s\n" inline_s
        else  begin
          printf "%s(%s\n" ind rel;
          List.iter (fun sv -> print ind'' sv) svs;
          printf "%s)\n" ind
        end in
      match x with 
        | Var id -> prints @@ Ident.name id
        | App (id,svs) ->  prints @@ (Ident.name id)^"("
            ^(String.concat "," @@ List.map f svs)^")"
        | Eq (sv1,sv2) -> print_bin "=" (sv1,sv2)
        | Gt (sv1,sv2) -> print_bin ">" (sv1,sv2)
        | Lt (sv1,sv2) -> print_bin "<" (sv1,sv2)
        | Not sv -> print_un "¬" sv
        | And svs -> print_mult "∧" svs
        | Or svs -> print_mult "∨" svs
        | ConstInt i -> prints @@ string_of_int i
        | ConstBool b -> prints @@ string_of_bool b
        | ConstString s -> prints s
        | ConstUnit -> prints "()"
        | List ([],None) -> prints "[]"
        | List (svs,None) -> print_mult "::" svs
        | List (svs,Some l) -> print_mult "::" (svs@[l])
        | Option None -> prints "None" 
        | Option (Some sv) -> print_un "Some" sv
        | ITE (grd,sv1,sv2) -> 
            let inline_s = Printf.sprintf "%s(if (%s) {" 
                            ind (f grd) in
            begin
              if slen inline_s <= 100 then  
                printf "%s\n" inline_s
              else begin
                printf "%s(if\n" ind;
                print (ind') grd;
                printf "%s{\n" ind;
              end; 
              print (ind') sv1;
              printf "%s} else {\n" ind;
              print (ind') sv2;
              printf "%s})\n" ind;
            end
        | sv -> prints @@ f sv

  let nil = List ([],None)

  let cons = function (x, List (xs,s)) -> List (x::xs,s)
    | (x, s) -> List ([x],Some s)

  let none = Option None

  let some x = Option (Some x)

  (*
   * Does a follow from assumps?
   *)
  let rec (|=) assumps a = 
    (* 
     * This is needed because new assumps may be added since the last
     * simplification.
     *)
    let assumps = List.concat @@ List.map 
                                   (function (And x) -> x 
                                      | x -> [x]) assumps in
      match a with 
        | ConstBool true -> true
        | And vs -> List.for_all (fun v -> assumps |= v) vs
        | Or vs -> List.exists (fun v -> assumps |= v) vs
        | _ when (List.mem a assumps) -> true
        | _ -> false
  (*
   * Simplifies gv by applying algebraic rules until fixpoint.
   * Returns a gv' s.t., (assumps |- gv' <=> gv) and 
   * size(gv') ≤ size(gv). 
   *)

  let (*rec*) simplify assumps gv =  
    let rec simplify_rec assumps gv = 
      let ret str v = v in
      let res = match gv with
        (* (isSome (a? Some b : None))? d : e ---> a? d : e *)
        | App (_isSome, [ITE (a, 
                              Option (Some b), 
                              Option None)]) when (_isSome = L.isSome) -> 
            simplify_rec assumps a
        | App (_fromJust, [Option (Some a)]) when (_fromJust = L.fromJust) ->
           simplify_rec assumps a
        | App (f,v2s) -> 
          let v2s' = List.map (simplify_rec assumps) v2s in
          let same = List.map2 (=) v2s' v2s in
          let all_same = List.fold_left (&&) true same in
          let res = if all_same then gv else simplify_rec assumps (App (f, v2s')) in
          res
        | ITE (a,b,c) when (assumps |= a) ->
            simplify_rec assumps b
        | ITE (a,b,c) when (assumps |= (Not a)) -> 
            simplify_rec assumps c
        | ITE (a, ConstBool true, ConstBool false) -> 
            simplify_rec assumps a
        | ITE (a, b, ConstBool false) -> 
            simplify_rec assumps @@ And [a;b]
        | ITE (a, ConstBool true, c) -> 
            simplify_rec assumps @@ Or [a;c]
        | ITE (a, ITE (b,c,d), e) when (d = e) ->
            simplify_rec assumps (ITE (And [a;b], c, d))
        | ITE (ITE(a,b,c),d,e) -> 
            simplify_rec assumps @@ 
            ITE (Or [And [a;b]; And [Not a;c]], d, e)
        | ITE (a,b,c) -> 
            let a' = simplify_rec assumps a in
            let b' = simplify_rec (a'::assumps) b in
            let c' = simplify_rec ((Not a')::assumps) c in
            if (a' = a) && (b' = b) && (c' = c) then gv
                       else simplify_rec assumps @@ ITE (a', b', c')
        | Option (Some a) -> 
            let a' = simplify_rec assumps a in
            if a' = a then gv else simplify_rec assumps @@ Option (Some a')
        | And [] -> ConstBool true
        | And [sv] -> simplify_rec assumps sv
        (*| And [ITE (a1,b1,c1); ITE (a2,b2,c2)] -> 
            simplify_rec assumps @@ *)
        (* Conversion to DNF *)
        | And svs when (List.exists (function (And _) -> true
                                       | _ -> false) svs) ->
                simplify_rec assumps @@ 
                  And (List.concat @@ List.map (function (And svs') -> svs'
                                                  | sv -> [sv]) svs)
        | And svs when (List.exists (function (Or _) -> true 
                                            | _ -> false) svs) ->
            let conjuncts = List.fold_left 
                (fun conjs sv -> match sv with
                   | Or or_svs -> 
                       List.map (fun (conj,or_sv) -> conj@[or_sv]) 
                        @@ List.cross_product conjs or_svs
                   | _ -> List.map (fun conj -> conj @ [sv]) conjs)
                [[]] svs in
            let disjuncts = List.map (fun c -> And c) conjuncts in
            simplify_rec assumps @@ Or disjuncts
        | And svs when (List.exists (fun sv -> assumps |= sv) svs) -> 
            simplify_rec assumps @@ 
              And (List.filter (fun sv -> not (assumps |= sv)) svs)
        | And svs -> 
            let do_simplify sv = 
              simplify_rec ((List.filter (fun sv' -> sv' <> sv) svs)@assumps) sv in
            let svs' = List.map do_simplify svs in
            let same = List.map2 (=) svs' svs in
            let all_same = List.fold_left (&&) true same in 
            if all_same then ret "5" gv else simplify_rec assumps @@ And svs'
        | Or [] -> ConstBool true
        | Or [sv] -> simplify_rec assumps sv
        | Or svs when (List.exists (fun sv -> assumps |= sv) svs) -> 
            ConstBool true
        | Or svs when (List.exists (function (Or _) -> true
                                       | _ -> false) svs) ->
            simplify_rec assumps @@ 
              Or (List.concat @@ List.map (function (Or svs') -> svs'
                                            | sv -> [sv]) svs)
        | Or svs -> 
            let do_simplify sv = simplify_rec assumps sv in
            let svs' = List.map do_simplify svs in
            let same = List.map2 (=) svs' svs in
            let all_same = List.fold_left (&&) true same in 
            if all_same then gv else simplify_rec assumps @@ Or svs'
        | Eq (v1,v2) when (v1 = v2) -> ConstBool true
        | Eq (v1,v2) -> 
            let (v1',v2') = (simplify_rec assumps v1, simplify_rec assumps v2) in
              if v1' = v1 && v2' = v2 
              then gv
              else simplify_rec assumps @@ Eq (v1',v2')
        | Gt (v1, v2) -> 
            let (v1',v2') = (simplify_rec assumps v1, simplify_rec assumps v2) in
              if v1' = v1 && v2' = v2 
              then gv
              else simplify_rec assumps @@ Gt (v1',v2')
        | Lt (v1, v2) -> 
            let (v1',v2') = (simplify_rec assumps v1, simplify_rec assumps v2) in
              if v1' = v1 && v2' = v2 
              then gv
              else simplify_rec assumps @@ Lt (v1',v2')
        | Not (ConstBool true) -> ConstBool false
        | Not (ConstBool false) -> ConstBool true
        | Not v -> 
            let v' = simplify_rec assumps v in 
            if v' = v then gv else simplify_rec assumps @@ Not v'
        | _ -> match to_string gv with
               | "true" -> ConstBool true
               | "false" -> ConstBool false
               | _ -> gv in
        res in
    let res1 = simplify_rec assumps gv in
    res1

  let rec simplify_all xs = 
    let simplify_one x = simplify (List.filter (fun x' -> x' <> x)
                                         xs) x in
    let xs' = List.map simplify_one xs in
    if xs' = xs then xs else simplify_all xs'

  let rec ground v = 
    let f = ground in
    let g = List.map f in 
      match v with 
        | App (id,svs) -> App (id,g svs)
        | Eq (v1,v2) -> Eq (f v1, f v2)
        | Gt (v1,v2) -> Gt (f v1, f v2)
        | Lt (v1,v2) -> Lt (f v1, f v2)
        | Not v -> Not (f v)
        | And svs -> And (g svs)
        | Or svs -> Or (g svs)
        | List (svs,s) -> List (g svs,s)
        | ITE (v1,v2,v3) -> ITE (f v1, f v2, f v3)
        | Record flds -> Record (List.map (fun (id,v) -> (id,f v)) flds)
        | DelayedITE (x,v1,v2) -> if !x then v1 else v2
        | _ -> v

  (*let ground v = simplify [] @@ ground v*)
  let ite (v1,v2,v3) = ITE (v1,v2,v3)
  let app ((v1:Ident.t),(v2s : t list)) = App (v1,v2s)
end

and VE : (LIGHT_ENV with type elem = SymbolicVal.t) = 
  Light_env.Make(struct include SymbolicVal end) 

module Predicate =
struct
  type t = BoolExpr of SymbolicVal.t
    | If of t * t 
    | Iff of t * t 
    | Forall of Type.t * (Ident.t -> t)

  module S = SymbolicVal

  let of_sv sv = BoolExpr sv 

  let of_svs svs = match svs with
    | [] -> BoolExpr (S.ConstBool true)
    | _ -> BoolExpr (S.And svs)

  let rec to_string = function BoolExpr sv -> S.to_string sv
    | If (v1,v2) -> (to_string v1)^" => "^(to_string v2)
    | Iff (v1,v2) -> (to_string v1)^" <=> "^(to_string v2)
    | Forall (ty,f) -> 
        let bv = Ident.create "bv" in
        "∀(bv:"^(Type.to_string ty)^"). "^(to_string @@ f bv)
    | _ -> failwith "P.to_string Unimpl."

  let rec print ind = function BoolExpr sv -> 
      (S.print ind sv; printf "\n" )
    | If (p1, p2) -> 
        begin
          print (ind#inc()) p1; 
          printf "%s=>\n" @@ ind#get(); 
          print (ind#inc()) p2;
        end
    | p -> printf "%s\n" (to_string p)

  let empty_indent = object 
    val ind = ""
    method inc () = {<ind = ind^"  ">}
    method get () = ind
  end

  let print ?(ind=empty_indent) p = print ind p

  let _if (t1,t2) = match (t1,t2) with
    | (BoolExpr (S.ConstBool true), _) -> t2
    | (BoolExpr (S.ConstBool false), _) -> 
            BoolExpr (S.ConstBool true)
    | _ -> If (t1,t2)

  let _iff (t1,t2) = Iff (t1,t2)
  let forall ty f = Forall (ty,f)

  let simplify_if (assumps: S.t list) (p:t) = 
    match p with
      | If (BoolExpr s1, BoolExpr s2) -> 
          let s1' = S.simplify assumps s1 in
          let f x = BoolExpr (S.simplify (assumps@x) s2) in
            (match s1' with
              | S.ConstBool true -> [f []]
              | S.ConstBool false -> [BoolExpr (S.ConstBool true)]
              | S.Or disjs -> 
                  List.map (fun d -> If (BoolExpr d, f [d])) disjs
              | _ -> [If (BoolExpr s1', f [s1'])])
      | BoolExpr _ | Iff (_,_) -> 
          failwith "P.simplify_if: Unexpected!" 

  let simplify_ifs assumps ifs = 
    List.concat @@ List.map (simplify_if assumps) ifs

  let simplify (pe: t list) (sv:S.t) = 
    let (atoms,others) = List.partition 
                          (function BoolExpr _ -> true
                                  | _ -> false) pe in
    let atoms = List.concat @@ 
            List.map (function BoolExpr (S.And x) -> x 
                             | BoolExpr x -> [x]
                             | _ -> failwith "Impossible!") atoms in
    let _ = dprintf !_dsimpl_asn "ASSUMPS (BEFORE SIMPLIFICATION):\n" in
    let _ = List.iteri (fun i s -> 
              dprintf !_dsimpl_asn "%d. %s\n" i @@ S.to_string s) atoms in
    let atoms' = S.simplify_all atoms in
    let others' = simplify_ifs atoms' others in
    let _ = dprintf !_dsimpl_asn "ASSUMPS:\n" in
    let _ = List.iteri (fun i s -> 
              dprintf !_dsimpl_asn "%d. %s\n" i @@ S.to_string s) atoms' in
    let sv' = S.simplify atoms' sv in
    let _ = if !_dsimpl && sv' <> sv then begin
        printf "BEFORE:\n";
        S.print empty_indent sv;
        printf "AFTER: \n";
        S.print empty_indent sv';
      end in
    let pe' = (List.map (fun x -> BoolExpr x) atoms')@others' in
    (pe',sv')
    (*(pe,sv')*) (* TODO: change it back! *)

  let test_simplify () = 
    let open S in
    let f = Ident.create "f" in
    let g = Ident.create "g" in
    let h = Ident.create "h" in
    let a = Var (Ident.create "a") in
    let _0 = ConstInt 0 in
    let _1 = ConstInt 1 in
    let [fa;ga;ha] = List.map (fun fn -> App(fn,[a])) [f;g;h] in
    let t = ITE (Eq (fa,ga), ITE(Eq(ha,ha), a, _0), _1) in
    let t' = simplify [] t in
    let _ = printf "t' = %s\n" @@ to_string t' in
      ()

  let rec ground p = match p with
    | BoolExpr v -> BoolExpr (S.ground v)
    | If (t1,t2) -> If (ground t1, ground t2)
    | Iff (t1,t2) -> Iff (ground t1, ground t2)
    | _ -> p (* assuming no delayed thunks under quantifiers.*)

end

module Misc =
struct

  let rec rem_tlink t = 
    match t with
    | Tlink typ_expr -> rem_tlink typ_expr.desc
    | Tarrow (a,typ_expr1,typ_expr2,b) -> 
        let ty1 = typ_expr1.desc in
        let ty2 = typ_expr2.desc in
        Tarrow(a, {typ_expr1 with desc=rem_tlink ty1}, 
               {typ_expr2 with desc=rem_tlink ty2},
               b)
    | _ -> t

  let uncurry_arrow t = 
    let strf = Format.std_formatter  in
    let rec uncurry_arrow_rec = function
      | (Tarrow (_,typ_expr1,typ_expr2,_)) ->
          let (ty1,ty2) = (typ_expr1.desc, typ_expr2.desc) in
          let ty2' = rem_tlink ty2 in
          begin
            match ty2' with 
                | Tarrow _ -> (fun (x,y) -> (ty1::x,y)) (uncurry_arrow_rec ty2')
                | _ -> ([ty1], ty2')
          end
      | Tlink typ_expr -> uncurry_arrow_rec @@ typ_expr.desc
      | _ -> failwith "uncurry_arrow called on non-arrow type" in
    uncurry_arrow_rec t

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
    let assrt b = if b then () else fail ()(*failwith "not unifiable"*) in
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
            (*let strf = Format.str_formatter in
            let _ = List.map (fun tye1 -> Printtyp.raw_type_expr strf tye1) tyes1 in
            let _ = Format.fprintf strf "\n" in
            let _ = List.map (fun tye2 -> Printtyp.raw_type_expr strf tye2) tyes2 in
            Printf.printf "%s\n" @@ Format.flush_str_formatter ();*)
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
