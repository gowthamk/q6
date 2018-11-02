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
