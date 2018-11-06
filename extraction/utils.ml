module List :
sig
  include module type of List
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val map_fold_left: ('b -> 'a -> ('c*'b)) -> 'b -> 'a list -> ('c list * 'b)
  val tabulate : int -> (int -> 'a) -> 'a list 
  val last : 'a list -> 'a
  val take : int -> 'a list -> 'a list
  val linear_pairs: 'a list -> ('a*'a) list (* n-1 pairs *)
  val distinct_pairs: 'a list -> ('a*'a) list (* n(n+1)/2 pairs *)
  val cross_product : 'a list -> 'b list -> ('a*'b) list (* n^2 pairs *)
  val split2: ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
  val find_some: ('a -> 'b option) -> 'a list -> 'b
  val map_some: ('a -> 'b option) -> 'a list -> 'b list
end =
struct
  include List
  let zip l1 l2 = map2 (fun x y -> (x,y)) l1 l2 

  let map_fold_left f acc l = 
    let g (l',acc) a = 
      let (b,acc') = f acc a in
        (b::l',acc') in
    let (l',acc') = List.fold_left g ([],acc) l in
      (List.rev l',acc')

  let tabulate n f = 
    let l = Array.to_list @@ Array.make n () in
      List.mapi (fun i _ -> f i) l

  let hd = function x::xs -> x
    | [] -> (failwith "hd")

  let last l = hd @@ List.rev l

  let rec take n l = match n with
    | 0 -> []
    | _ -> (hd l)::(take (n-1) (tl l))

  let rec linear_pairs l = match l with 
    | [] -> [] | [x] -> []
    | x::y::xs -> (x,y)::(linear_pairs @@ y::xs)

  let rec distinct_pairs l = match l with
    | [] -> [] | [x] -> [] 
    | x::xs -> (List.map (fun x' -> (x,x')) xs)
                @ (distinct_pairs xs)

  let rec cross_product l1 l2 =  match (l1,l2) with
    | ([],_) | (_,[]) -> []
    | (x::xs,_) -> (map (fun y -> (x,y)) l2) @ 
                   (cross_product xs l2)

  let rec split2 l = match l with
    | [] -> ([],[],[])
    | (x,y,z)::l' -> 
        let (xs,ys,zs) = split2 l' in
        (x::xs, y::ys, z::zs)

  let rec find_some f l = match l with
    | [] -> raise Not_found
    | x::xs -> (match f x with 
        | Some y -> y
        | None -> find_some f xs)

  let rec map_some f l = match l with
    | [] -> []
    | x::xs -> (match f x with
        | Some y -> y::(map_some f xs)
        | None -> map_some f xs)
end

module Str =
struct
  include Str
  let strip_ws s = Str.global_replace (Str.regexp "[\r\n\t ]") "" s
end

let from_just = function (Some x) -> x
  | None -> failwith "Expected something. Got nothing."

let printf = Printf.printf
let sprintf = Printf.sprintf

let gen_name name_base = 
  let count = ref 0 in
    fun () -> 
      let x = name_base^(string_of_int !count) in
        (count := !count + 1; x)

(* 
 * Reducing a transitive relation by elimination of redundant pairs
 *)
module type RELNODE = sig 
  type t
  val compare: t -> t -> int
  val hash: t -> int
  val equal: t -> t -> bool
end
let reduce_transitive (type a) 
                      (module V: RELNODE with type t = a)
                      (rel: (a * a) list) : (a*a) list =
  let module G = Graph.Imperative.Graph.Concrete(V) in
  let module SCG = Graph.Components.Make(G) in
  let module DAG = Graph.Imperative.Digraph.ConcreteBidirectional(V) in
  let module T = Graph.Topological.Make(DAG) in
  let g = G.create () in
  let _ = List.iter (G.add_edge_e g) rel in
  let (n,f) = SCG.scc g in
  let dags = Array.init n (fun _ -> DAG.create ()) in
  let _ = List.iter (fun (a,b) -> 
                      begin 
                        assert (f a = f b);
                        let dag = dags.(f a) in
                        DAG.add_edge_e dag (a,b);
                      end) rel in
  let lorders = Array.map (fun dag -> 
                             T.fold (fun v acc -> acc@[v]) dag [])
                          dags in
  let lpairs = List.concat @@ List.map List.linear_pairs
                      @@ Array.to_list lorders in
  lpairs

(*
 *
 *)
module QueleaUtils = struct
open Asttypes
open Path
open Types
open Typedtree
open Printf

let nil_type_expr = {desc=Tnil; level=0; id=0}

let exp_of exp_desc = 
  {exp_desc=exp_desc;
   exp_loc=Location.none;
   exp_extra=[];
   (* -- TODO: put correct type -- *)
   exp_type=nil_type_expr;
   exp_env=Env.empty;
   exp_attributes=[]}

let longident_loc_of name = 
  let long_ident = Longident.Lident name in
  let open Location in
  {txt=long_ident; loc=none}

let cons_desc_of name = 
  {cstr_name=name;
   cstr_res=nil_type_expr;
   cstr_existentials=[];
   cstr_args=[];
   cstr_arity=1;
   cstr_tag=Cstr_constant 0;
   cstr_consts=0;
   cstr_nonconsts=0;
   cstr_normal=0;
   cstr_generalized=false;
   cstr_private=Public;
   cstr_loc=Location.none;
   cstr_attributes=[];
   cstr_inlined=None;}

let label_desc_of name = 
  {lbl_name=name;
   lbl_res=nil_type_expr;
   lbl_arg=nil_type_expr;
   lbl_mut=Immutable;
   lbl_pos=0;
   lbl_all=Array.of_list [];
   lbl_repres=Record_regular;
   lbl_private=Public;
   lbl_loc=Location.none;
   lbl_attributes=[]}
  
let exp_of_id id = 
  let name = Ident.name id in
  let loc = longident_loc_of name in
  let val_desc = {val_type=nil_type_expr; 
                  val_kind=Val_reg;
                  val_loc=Location.none;
                  val_attributes=[]} in
  exp_of @@ Texp_ident (Pident id, loc, val_desc)

let reflective_record_of ids = 
  let refl_id id = 
    let name = Ident.name id in
    let loc = longident_loc_of name in
    let ldesc = label_desc_of name in
    let expr = exp_of_id id in
    (loc, ldesc, expr) in
  let fields = List.map refl_id ids in
  exp_of @@ Texp_record (fields,None)


let pat_of pat_desc = 
  {pat_desc=pat_desc;
   pat_loc=Location.none;
   pat_extra=[];
   pat_type=nil_type_expr;
   pat_env=Env.empty;
   pat_attributes=[]}

let string_loc_of_id id = 
  let open Location in
  let iname = Ident.name id in
  {txt=iname; loc=Location.none}

let tuple_pat_of_ids id1 id2 = 
  let open Location in
  let ipat1 = pat_of @@ Tpat_var (id1, string_loc_of_id id1) in
  let ipat2 = pat_of @@ Tpat_var (id2, string_loc_of_id id2) in
  pat_of @@ Tpat_tuple [ipat1; ipat2]

let add_exp_of e1 e2 = 
  let plus_id = Ident.create "Pervasives.+" in
  let plus = exp_of_id plus_id in
    exp_of @@ Texp_apply (plus, [(Nolabel, Some e1);
                                 (Nolabel, Some e2)])

let parse_record_exp {exp_desc} = match exp_desc with
  | Texp_record (fields,_) -> 
      List.map (fun (_,{lbl_name},exp) -> (lbl_name,exp)) fields
  | _ -> failwith "parse_record_exp: unexpected expression"

let get_crtable_fn {exp_desc}= match exp_desc with
  | Texp_ident (Pdot (Pdot (Pident id, 
                            "CRTable",_),crfn,_),_,_) 
    when Ident.name id = "Crdts" -> Some crfn
  | _ -> None

let is_crtable_find e = match get_crtable_fn e with
  | Some "find" -> true 
  | _ -> false 

let is_crtable_update e = match get_crtable_fn e with
  | Some "update" -> true
  | _ -> false

let is_crtable_insert e = 
  match get_crtable_fn e with
    | Some "insert" -> true
    | _ -> false

let is_crtable_insert_or_delete e = 
  match get_crtable_fn e with
    | Some "insert" | Some "delete" -> true
    | _ -> false

let pervasives = [("Pervasives.@@", "@@"); 
                  ("Pervasives.::", "::"); 
                  ("Pervasives.=", "="); 
                  ("Pervasives.raise", "raise"); 
                  ("Pervasives.&&", "&&"); 
                  ("Pervasives.not", "not");
                  ("Pervasives.||", "||"); 
                  ("Pervasives.+", "+"); 
                  ("Pervasives.*", "*"); 
                  ("Pervasives.-", "-");
                  ("Pervasives.<>", "<>");
                  ("Pervasives.>", ">");
                  ("Pervasives.>=", ">=");
                  ("Pervasives.<", "<");
                  ("Pervasives.<=", "<=");]

let rec pp_const c = match c with
  | (Const_int i) -> sprintf "%d" i
  | (Const_char c) -> sprintf "%c" c
  | (Const_string (s,None)) -> sprintf "%s" s
  | (Const_string (s,Some s')) -> sprintf "%s%s" s s'
  | (Const_float s) -> sprintf "%s" s
  | _ -> sprintf "<-- some constant -->"

let rec pp_pat {pat_desc} =
  let f = pp_pat in
  match pat_desc with
    | Tpat_any -> sprintf "_"
    | Tpat_var (v,_) -> Ident.name v
    | Tpat_constant c -> pp_const c
    | Tpat_tuple pats -> sprintf "(%s)" @@ 
        String.concat "," @@ List.map f pats
    | Tpat_construct (_,{cstr_name},pats) -> sprintf "%s(%s)"
        cstr_name (String.concat "," @@ List.map f pats)
    | Tpat_record (fields,_) -> sprintf "{%s}" @@
        String.concat "; " @@ List.map 
          (fun (_,{lbl_name},pat) -> 
             sprintf "%s=%s" lbl_name (f pat)) fields
    | _ -> "<-- some pat -->"

and pp_expr {exp_desc} = 
  let x=1 in
  match exp_desc with
    | Texp_ident (path,_,_) -> sprintf "%s" @@ 
        String.concat "." @@ Path.all_names path
    | Texp_constant c -> pp_const c
    | Texp_let (_,[valbind],e) -> sprintf "(let %s in %s)"
          (pp_valbind valbind) (pp_expr e)
    | Texp_function (Nolabel, cases, _) -> 
          sprintf "(function %s)" @@ pp_cases cases
    | Texp_apply (e,args) -> 
        let e_str = pp_expr e in
        let arg_strs = List.map (fun (_,Some ei) ->  
                                      pp_expr ei) args in
        (match (List.assoc_opt e_str pervasives, arg_strs) with 
          | (Some op,[a1;a2]) -> sprintf "%s %s %s" a1 op a2
          | (Some op,[a]) -> sprintf "%s %s" op a
          | (Some _, _) | (None, _) -> sprintf "(%s %s)" e_str 
                       (String.concat " " @@ arg_strs))
    | Texp_tuple exps -> sprintf "(%s)" @@ String.concat "," @@
          List.map (pp_expr) exps
    | Texp_construct (_,{cstr_name},[]) -> sprintf "%s" cstr_name
    | Texp_construct (_,{cstr_name="::"},[e1; e2]) -> 
        sprintf "%s::%s" (pp_expr e1) (pp_expr e2)
    | Texp_construct (_,{cstr_name},exps) -> sprintf "%s(%s)"
        cstr_name (String.concat "," @@ List.map (pp_expr) exps)
    | Texp_record (fields,_) -> sprintf "{%s}" @@
        String.concat "; " @@ List.map 
          (fun (_,{lbl_name},exp) -> 
             sprintf "%s=%s" lbl_name (pp_expr exp)) fields
    | Texp_ifthenelse (e1,e2,Some e3) -> 
        sprintf "if %s then %s else %s" (pp_expr e1) 
          (pp_expr e2) (pp_expr e3)
    | Texp_sequence (e1,e2) -> sprintf "(%s; %s)" (pp_expr e1) 
                                 (pp_expr e2)
    | Texp_match (e,cases,_,_) -> sprintf "(match %s with %s)"
             (pp_expr e) (pp_cases cases)
    | _ -> "<-- some expr -->"

and pp_valbind {vb_pat; vb_expr} = sprintf "%s = %s" 
    (pp_pat vb_pat) (pp_expr vb_expr)

and pp_cases cases = String.concat " | " @@
  List.map (fun {c_lhs;c_rhs} -> sprintf "%s -> %s" 
                       (pp_pat c_lhs) (pp_expr c_rhs)) cases

end
