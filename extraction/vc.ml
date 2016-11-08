open Speclang
open Specelab
module SV = SymbolicVal
module P = Predicate

(* Verification Condition *)
type t = TE.t * Predicate.t list * Predicate.t

let printf = Printf.printf

let print (te,antePs,conseqP) = 
  begin
    printf "bindings {\n";
    TE.print te;
    printf "} in\n";
    List.iter (fun p -> 
                 Printf.printf "  /\\   %s\n" 
                   (P.to_string p)) antePs;
    print_string "=>";
    Printf.printf "\t%s\n" (P.to_string conseqP);
  end

let print_all vcs = 
  List.iteri (fun i vc -> 
                (printf "VC(%d):\n" i; print vc))
    vcs
