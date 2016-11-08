open Speclang
open Specelab

(* Verification Condition *)
type t = TE.t * Predicate.t list * Predicate.t

val print : t -> unit
val print_all : t list -> unit
