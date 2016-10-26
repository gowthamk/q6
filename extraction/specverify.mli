open Specelab

type env = {ke:KE.t; te:TE.t; ve:VE.t}

val doIt : env  -> Rdtspec.t -> Ident.t list -> unit
