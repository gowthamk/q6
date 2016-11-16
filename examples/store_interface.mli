module type TABLE_TYPE = 
sig
  type id
  type eff
end
module Make : functor(Table : TABLE_TYPE) ->
sig
  val get : Table.id -> Table.eff -> Table.eff option list
  val append : Table.id -> Table.eff -> unit
end
