open Types
open Typedtree
open Speclang

module Coltype = 
struct
  type t = Fkey of Ident.t | UUID | String | Int | Bool
end
module Effcons = 
struct
  type t = T of {name: Ident.t; args_t: (Ident.t*Coltype.t) list}
  let make ~name ~args_t = T {name=name; args_t=args_t}
end

module Tableschema = 
struct
  type t = T of {id_t : Coltype.t;
                 eff_cons : Effcons.t list}
  let make ~id_t ~eff_t = T {id_t=id_t; eff_cons=eff_t}
end

type t = T of {schemas: (Ident.t * Tableschema.t) list;
               reads: Fun.t list; 
               writes : Fun.t list; 
               aux: Fun.t list}
let make ~schemas ~reads ~writes ~aux = T {schemas; reads; writes; aux}
