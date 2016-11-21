module List :
sig
  include module type of List
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val map_fold_left: ('b -> 'a -> ('c*'b)) -> 'b -> 'a list -> ('c list * 'b)
  val tabulate : int -> (int -> 'a) -> 'a list 
  val last : 'a list -> 'a
  val take : int -> 'a list -> 'a list
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

