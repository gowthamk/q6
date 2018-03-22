open Q6_interface

type repl_id = int

(* The eff type in each module describes the messages that the
 * corresponding component sends. For instance, a proposer only ever
 * sends Prepare and Propose messages (Get is a read).*)
module Proposer = 
struct
  type id = repl_id
  type eff = Prepare of {round:int}
           | Propose of {round:int; value:string}
           | Get
end

module Proposer_table =
struct
  include Store_interface.Make(Proposer)
end

module Acceptor = 
struct
  type id = repl_id
  type eff = Promise of {round:int; prev_vote: (int*string) option}
           | Accept of {round:int; value:string}
           | Get
end

module Acceptor_table =
struct
  include Store_interface.Make(Acceptor)
end

module Learner = 
struct
  type id = repl_id
  type eff = Decide of {round:int; value:string}
           | Get
end

module Learner_table =
struct
  include Store_interface.Make(Learner)
end

(* ----------- ACTIONS OF PROPOSER ------------*)

(* prepare is sent to prepare nodes for a round led by the current
 * node, It elicits promises from nodes to participate in the round.*)
let do_prepare n r = 
  Proposer_table.append n (Proposer.Prepare {round=r})

(* A node n can propose in a round r for which it has previously sent
 * a Prepare message, only if a quorum of nodes responded with
 * promises for r. Each promise is tagged (via prev_vote) with the
 * details of the Accept vote cast by the sender in the highest among
 * the rounds it participated so far. The value associated with the
 * max among such votes cast by all members in the quorum is returned
 * by this function. This should be the value of the proposal.
 *)
let do_check_proposable n r repl_ids = 
  let open Acceptor in
  let n_repls = List.length repl_ids in
  let promises = List.fold_right
      (fun n' acc -> 
         let hist = Acceptor_table.get n' Acceptor.Get in 
         let promise_opt = List.find_opt
           (fun eff -> match eff with
              | Promise {round=r'} -> r' = r
              | _ -> false) 
           hist in 
         match promise_opt with 
           | Some promise -> promise::acc
           | None -> acc) repl_ids [] in
  let n_promises = List.length promises in
  let max_vote = List.fold_right 
      (fun p acc -> match p,acc with
         | (Promise {prev_vote=Some (r,v)}, Some (r',_)) -> 
             if r>r' then Some (r,v) else acc
         | (Promise {prev_vote=Some (r,v)}, None) -> Some (r,v)
         | _ -> acc) in
  (2*n_promises > n_repls, max_vote)

let do_propose n r v = 
  Proposer_table.append n (Proposer.Propose {round=r; value=v})

(* Returns the highest round in which the node n promised to vote. *)
let get_highest_promise_by n = 
  let open Acceptor in
  let hist = Acceptor_table.get n Acceptor.Get in
  let max  = List.fold_right 
      (fun x acc -> match x,acc with
         | Promise {round=r}, Some r' -> 
             if r>r' then Some r else Some r'
         | Promise {round=r}, None -> Some r
         | _ -> acc) hist None in
  max

(* Returns the highest round for which a Prepare message exists in
 * plist *)
let get_highest_prepare plist = 
  let open Proposer in
  List.fold_right 
    (fun x acc -> match x,acc with 
       | Prepare {round=r}, Some r' -> 
           if r>r' then Some r else Some r'
       | Prepare {round=r}, None -> Some r
       | _ -> acc) plist None

(* If a proposer tried to prepare the node n for a later round than
 * which n is currently participating, then we return such a round.
 *)
let do_get_promisable_prepare n repl_ids = 
  let open Proposer in
  let open Acceptor in
  let phist = List.concat @@ List.map 
      (fun n' -> Proposer_table.get n' Proposer.Get) repl_ids in
  let cur_round = get_highest_promise_by n in
  let outstanding_prepares = List.filter 
      (fun p -> match p,cur_round with 
         | Prepare {round=r}, Some r' -> r>r'
         | Prepare _ , None -> true
         | _, _ -> false) phist in
  get_highest_prepare outstanding_prepares

(* We return the highest round in which the node n voted, and also the
 * value associated with the vote.  *)
let do_get_highest_accept_by n = 
  let open Acceptor in
  let hist = Acceptor_table.get n Acceptor.Get in
  let max  = List.fold_right 
      (fun x acc -> match x,acc with
         | Accept {round=r; value=v}, Some (r',v') -> 
             if r>r' then Some (r,v) else Some (r',v')
         | Accept {round=r; value=v}, None -> Some (r,v)
         | _ -> acc) hist None in
  max

let do_promise n r = 
  let p = do_get_highest_accept_by n in
  Acceptor_table.append n (Acceptor.Promise {round=r; prev_vote=p})

(*
 * Proposal is acceptable iff I promised to accept it, and I haven't
 * moved on to a later round.
 *)
let do_check_proposal_acceptable n r = 
  let open Acceptor in
  let cur_round = get_highest_promise_by n in
  match cur_round with
    | Some r' -> r'=r
    | None -> false

let do_accept_proposal n r v = 
  Acceptor_table.append n (Acceptor.Accept {round=r; value=v})
 
(* The learner learns about all the proposals for which a quorum of
 * nodes have cast their votes.
 *)
let do_learn repl_ids = 
  let n_repls = List.length repl_ids in
  let ahist = List.concat @@ List.map 
      (fun n -> Acceptor_table.get n Acceptor.Get) repl_ids in
  let accepts = List.fold_right 
      (fun x acc -> match x with 
         | Acceptor.Accept {round=r;value=v} -> (r,v)::acc 
         | _ -> acc) ahist [] in
  let quorum_accepts = List.find_all
    (fun (r,_) ->
      let accepts_of_r = List.find_all (fun (r',_) -> r'=r) 
                        accepts in
      let n_accepts_of_r = List.length accepts_of_r in
      2*n_accepts_of_r > n_repls)
    accepts in
  List.sort_uniq compare quorum_accepts

let do_decide n (r,v) = 
  Learner_table.append n (Learner.Decide {round=r; value=v})


