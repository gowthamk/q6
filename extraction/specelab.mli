open Rdtspec
open Speclang
open Light_env

module KE : LIGHT_ENV with type elem = Kind.t
module TE : LIGHT_ENV with type elem = Type.t
module VE : LIGHT_ENV with type elem = SymbolicVal.t

val type_of_coltype: Coltype.t -> (Ident.t * Tableschema.t) list -> Type.t
val doIt: Rdtspec.t -> KE.t * TE.t * VE.t
