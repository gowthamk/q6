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
  val print : t -> unit
end
module Make : functor(Val: sig 
                        type t 
                        val to_string : t -> string
                      end) -> LIGHT_ENV with type elem = Val.t



