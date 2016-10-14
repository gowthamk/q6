module type TABLE_TYPE = 
sig
  type id
  type eff
end
module Make = functor(S : TABLE_TYPE) ->
struct
  let get id read_eff = []

  let append id write_eff = ()
end
