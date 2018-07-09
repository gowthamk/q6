open Utils
open Vc

module type T = 
sig
  val get_counterexample : unit -> unit
end

module type Z3 = module type of Z3encode

let make (module Z3: Z3) cmap tmap fmap vc = 
(module struct
  let get_counterexample () = 
    let model = Z3.get_model () in 
    let _ = try Unix.mkdir "Models" 0o777 
            with Unix.Unix_error(Unix.EEXIST,_,_) -> () in
    let txn_id = vc.txn in
    let inv_id = vc.inv in
    let vc_name = (Ident.name txn_id)^"_" ^(Ident.name inv_id) in
    let out_chan = open_out @@ "Models/"^vc_name^".z3" in
    let _ = output_string out_chan @@ Z3.Model.to_string model in
    ()
end : T)
