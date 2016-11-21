open Speclang
open Specelab

(* Sequential Verification Condition *)
type seq_t = TE.t * Predicate.t list * Predicate.t

(* Verification Condition *)
type t = {kbinds:KE.t; tbinds: TE.t; 
          (* program : a set of constraints (on effects) 
           * describing a (write) transaction's operational 
           * behaviour. *)
          prog: Predicate.t list;
          (* invariant : a set of constraints describing the
           * operational behaviour of a (read) tranasction, along 
           * with a constraint that must hold under such 
           * behaviour so that the transaction always returns true.*)
          (* inv: Predicate.t; *)
          (* pre-condition: a constraint that "projects" 
           * the invariant on the pre-state (i.e., set of effects
           * excluding those constrained by prog) *)
          pre: Predicate.t; 
          (* post-condition: a constraint that "projects" 
           * the invariant on the post-state (i.e., set of all 
           * effects, including those constrained by prog) *)
          post: Predicate.t}

val print_seq : seq_t -> unit
val print : t -> unit
(* val make: ~bindings:TE.t -> ~pre:Predicate.t -> ~prog:*)
