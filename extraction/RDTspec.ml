open Types
open Typedtree

module Id = 
struct
  type t = T of string
  let to_string (T s) = s
  let from_string s = T s
end 
module Tabletype = Id

module Coltype = 
struct
  type t = Fkey of Tabletype.t | UUID | String | Int
end
module Effcons = 
struct
  type t = T of {name: Id.t; args_t: (Id.t*Coltype.t) list}
  let make ~name ~args_t = T {name=name; args_t=args_t}
end

module Efftyp = 
struct
  type t = T of Effcons.t list
  let make effconss = T effconss
end

module Tableschema = 
struct
  type t = T of {id_t : Coltype.t;
                 eff_t : Efftyp.t}
  let make ~id_t ~eff_t = T {id_t=id_t; eff_t=eff_t}
end

module Fun = 
struct
  type t = T of {name: Id.t; 
                 args_t: (Id.t * type_desc) list; 
                 res_t: type_desc;
                 body: expression_desc}
  let make ~name ~args_t ~res_t ~body = 
    T {name=name; args_t=args_t; res_t=res_t; body=body}
end

type t = T of {schemas: (Tabletype.t * Tableschema.t) list;
               reads: Fun.t list; 
               writes : Fun.t list; 
               aux: Fun.t list}
let make ~schemas ~reads ~writes ~aux = T {schemas; reads; writes; aux}
