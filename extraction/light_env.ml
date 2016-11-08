module type LIGHT_ENV = 
sig
  type elem
  type t
  val empty: t
  val add: Ident.t -> elem -> t -> t
  val find_same: Ident.t -> t -> elem
  val find_name: string -> t -> elem
  val find_all: string -> t -> elem list
  val fold_name: (Ident.t -> elem -> 'b -> 'b) -> t -> 'b -> 'b
  val fold_all: (Ident.t -> elem -> 'b -> 'b) -> t -> 'b -> 'b
  val iter: (Ident.t -> elem -> unit) -> t -> unit
  val print: t -> unit
end
module Make = functor(Val: sig 
                        type t 
                        val to_string : t -> string
                      end) ->
struct
  open Typedtree
  type elem = Val.t
  type t = elem Ident.tbl
  let empty = Ident.empty
  let add = Ident.add
  let find_same = Ident.find_same
  let find_name = Ident.find_name
  let find_all = Ident.find_all
  let fold_name = Ident.fold_name
  let fold_all = Ident.fold_all
  let iter = Ident.iter
  let print = Ident.iter 
      (fun id elem -> 
        let str = "  "^(Ident.name id)^" :-> "^(Val.to_string elem) in
          Printf.printf "%s\n" str) 
end
