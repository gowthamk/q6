module CRInt = struct
  type t = int

  let get t = t
  let add a t = fun t' -> t'+a
end

module CRTable = struct
  type 'a t = 'a list

  let find f g t = failwith "Unimpl."
  let update f g t = ()
  let delete g t = ()
  let insert x t = ()
end

module CRSet = struct
  type 'a t = 'a list

  let add x t = ()
  let remove x t = ()
  let get t = t
end

