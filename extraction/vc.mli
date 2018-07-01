open Speclang
open Specelab

(* Sequential Verification Condition *)
type seq_t = TE.t * Predicate.t list * Predicate.t

(* Verification Condition *)
type t = {txn: Ident.t;
          kbinds:KE.t; 
          tbinds: TE.t; 
          (* exec: Axiomatic execution of the program and the
           * invariants. *)
          exec: Predicate.t list;
          (* pre-conditions: Invariant predicates in the pre-state *)
          pre: Predicate.t list; 
          (* post-condition: Invariant predicates in the post-state *)
          post: Predicate.t list}

val print_seq : seq_t -> unit
val print : t -> unit
(* val make: ~bindings:TE.t -> ~pre:Predicate.t -> ~prog:*)
