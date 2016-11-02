open Speclang
open Specelab

type env_t = (KE.t * TE.t * Predicate.t list * VE.t)

val doIt : env_t  -> Rdtspec.t -> int -> unit
