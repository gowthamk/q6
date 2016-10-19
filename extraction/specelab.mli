open Speclang
open Light_env

module KE : LIGHT_ENV with type elem = Kind.t
module TE : LIGHT_ENV with type elem = RefinementType.t
module VE : LIGHT_ENV with type elem = SymbolicVal.t

val doIt: Rdtspec.t -> KE.t * TE.t * VE.t
