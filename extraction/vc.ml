open Speclang
open Specelab
module SV = SymbolicVal
module P = Predicate

(* Sequential Verification Condition *)
type seq_t = TE.t * Predicate.t list * Predicate.t

(* Verification Condition *)
type t = {txn:Ident.t;
          inv: Ident.t;
          kbinds:KE.t; 
          tbinds: TE.t; 
          (* exec: Axiomatic execution of the program and the
           * invariants. *)
          exec: Predicate.t list;
          (* pre-conditions: Invariant predicate in the pre-state *)
          pre: Predicate.t; 
          (* post-condition: Invariant predicate in the post-state *)
          post: Predicate.t}

let printf = Printf.printf

let print_seq (te,antePs,conseqP) = 
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

let print {txn; inv; kbinds; tbinds; exec; pre; post} =
  begin
    printf "--------- VC (%s |- %s) -------\n" 
           (Ident.name txn) (Ident.name inv);
    printf "\027[38;5;4mbindings {\027[0m\n";
    printf "  \027[38;5;4mkinds\027[0m\n";
    KE.print kbinds;
    printf "  \027[38;5;4mtypes\027[0m\n";
    TE.print tbinds;
    printf "\027[38;5;4m} \027[0m\n";
    printf "\027[38;5;4mprog: \027[0m\n";
    List.iter (fun p -> 
                 Printf.printf "    /\\   %s\n" 
                   (P.to_string p)) exec;
    printf "\027[38;5;4mpre: \027[0m\n";
    (*List.iter (fun p -> 
                 Printf.printf "    /\\   %s\n" 
                   (P.to_string p)) pre;*)
    Printf.printf "    %s\n" (P.to_string pre);
    (*print_string "  =>";
    Printf.printf "    %s\n" (P.to_string inv);*)
    printf "\027[38;5;4mpost: \027[0m\n";
    (*List.iter (fun p -> 
                 Printf.printf "    /\\   %s\n" 
                   (P.to_string p)) post;*)
    Printf.printf "    %s\n" (P.to_string post);
    (*print_string "  =>";
    Printf.printf "    %s\n" (P.to_string inv);*)
  end
