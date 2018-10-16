module type T = 
sig
  val get_counterexample : unit -> unit
end

module type Z3 = module type of Z3encode

val make: (module Z3) -> #Encoding_env.encoding_env -> Vc.t -> (module T)
