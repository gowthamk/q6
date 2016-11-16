open Speclang
open Specelab
module VC = Vc

type env_t = (KE.t * TE.t * Predicate.t list * VE.t)

val doIt : env_t  -> Rdtspec.t -> int -> (Ident.t (* fun name *) * 
                                          VC.t list (* VCs. Last VC is the symbolic trace. *)) list
