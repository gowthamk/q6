module List :
sig
  include module type of List
  val zip : 'a list -> 'b list -> ('a * 'b) list
end =
struct
  include List
  let zip l1 l2 = map2 (fun x y -> (x,y)) l1 l2 
end
