open Speclang
open Specelab

type env = {ke:KE.t; te:TE.t; pe: Predicate.t list; ve:VE.t}

val doIt : env  -> Rdtspec.t -> int -> unit
