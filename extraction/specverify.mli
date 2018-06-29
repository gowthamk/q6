open Speclang
open Specelab
module VC = Vc

type env_t = (KE.t * TE.t * Predicate.t list * VE.t)

val doIt : env_t  -> Rdtspec.t -> (Ident.t (* fun name *) * VC.t) list
