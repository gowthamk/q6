open Q6_interface

type repl_id = int

(* The eff type in each module describes the messages that the
 * corresponding component sends. For instance, a proposer only ever
 * sends Prepare and Propose messages (Get is a read).*)
module Proposer = 
struct
  type id = Uuid.t(*repl_id*)
  type eff = Prepare of {round:int}
           | Propose of {round:int; value:int}
           | Get
end

module Proposer_table =
struct
  include Store_interface.Make(Proposer)
end

module Acceptor = 
struct
  type id = Uuid.t(*repl_id*)
  type eff = Promise of {round:int}
           | PromiseWithPrev of {round:int; prev_vote_round: int; 
                                 prev_vote_val:int}
           | Accept of {round:int; value:int}
           | Get
end

module Acceptor_table =
struct
  include Store_interface.Make(Acceptor)
end

module Learner = 
struct
  type id = Uuid.t(*repl_id*)
  type eff = Decide of {round:int; value:int}
           | Get
end

module Learner_table =
struct
  include Store_interface.Make(Learner)
end

module List = 
struct
  open List
  let rec map f l = match l with
    | [] -> []
    | x::xs -> (f x)::(map f xs)

  let rec concat ls = 
    let rec append l1 l2 = match l1 with
      | [] -> l2
      | x::xs -> x::(append xs l2) in
      match ls with
        | [] -> []
        | l::rest -> append l (concat rest)

  let rec fold_left f b l = match l with
    | [] -> b
    | x::xs -> fold_left f (f b x) xs

  let rec fold_right f l b = match l with
    | [] -> b
    | x::xs -> f x (fold_right f xs b)

  let rec iter f l = match l with
    | [] -> ()
    | x::xs -> (f x; iter f xs)

  let rec first_some l = match l with
    | [] -> None
    | x::xs -> (match x with 
                  | None -> first_some xs
                  | Some _ -> x)

  let rec forall l f = match l with
    | [] -> true
    | x::xs -> (f x)&&(forall xs f)

  let rec exists l f = match l with
    | [] -> false
    | x::xs -> (f x)||(exists xs f)

  let rec all_same l =
    let rec all_same_v (l: int option list) (v:int) : bool =
      match l with
      | [] -> true
      | x::xs -> let t = all_same_v xs v in
                 (match x with
                 | Some y -> y=v && t
                 | _ -> t) in
    match l with
    | [] -> true
    | x::xs -> (match x with
               | Some y -> all_same_v xs y
               | _ -> all_same xs)

  let rec length l = 
    match l with
    | [] -> 0
    | x::xs -> 1 + length xs
end

let get_all = []

(* ----------------- ACTIONS OF THE PROPOSER ---------------------- *)

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
(*let do_check_proposable n r repl_ids = 
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

(* ----------------- ACTIONS OF THE ACCEPTOR --------------------- *)

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
 
(* ----------------- ACTIONS OF THE LEARNER --------------------- *)

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
  Learner_table.append n (Learner.Decide {round=r; value=v})*)

(*** Auxilliary Functions Begin ***)

let get_decided_v x1 = 
  match x1 with
  | Some x ->
    (match x with 
    | Learner.Decide {value=v} -> Some v 
    | _ -> None)
  | _ -> None

let get_proposed_v_for_r r x1 = 
  match x1 with
  | Some x -> 
    (match x with 
    | Proposer.Propose {round=r1; value=v} -> if r=r1 then Some v else None
    | _ -> None)
  | _ -> None

let check_accepted_rv r v eff1 = 
 match eff1 with
 | Some eff ->
   (match eff with
   | Acceptor.Accept{round=r1;value=v1} -> r1=r && v1=v
   | _ -> false)
 | _ -> false

let check_proposed_rv r v eff1 = 
  match eff1 with
  | Some eff ->
    (match eff with
           | Proposer.Propose{round=r1;value=v1} -> r1=r && v1=v
           | _ -> false)
  | _ -> false

 let check_decided_rv r v x1 = 
   match x1 with
   | Some x -> 
     (match x with 
     | Learner.Decide {round=r1; value=v1} -> r1=r && v1=v
     | _ -> false)
   | _ -> false

 let inc_if_decided_rv r v x1 acc = 
   match x1 with
  | Some x -> 
    (match x with 
    | Acceptor.Accept {round=r1;value=v1} -> 
      if r=r1&&v=v1 then acc+1 else acc
    | _ -> acc)
  | _ -> acc

 let check_accepted_r r eff1 =
  match eff1 with
  | Some eff ->
    (match eff with
    | Acceptor.Accept{round=r2} -> 
      r=r2
    | _ -> false)
  | _ -> false

(*** Auxilliary Functions End ***)

(*∀n1,n2 : node,r1,r2 : round,v1,v2 : value. 
 decision(n1,r1,v1) ∧ decision(n2,r2,v2) → v1 = v2 *)

let inv1 (dummy:int) = 
  let hist = get_all in 
  let lvalues = List.map (get_decided_v) hist in
  List.all_same lvalues

(*∀r : round,v1,v2 : value. 
 propose_msg(r,v1) ∧ propose_msg(r,v2) → v1 = v2*)

let inv2 r = 
  let hist = get_all in
  let pvalues = List.map (get_proposed_v_for_r r) hist in
  List.all_same pvalues

(*∀n : node,r : round,v : value. 
 vote_msg(n,r,v) → propose_msg(r,v)*)

let inv3 n r v = 
  let hist = get_all in
  if List.exists hist (check_accepted_rv r v) then
    List.exists hist (check_proposed_rv r v) 
  else true

(*∀r : round,v : value. 
(∃n : node. decision(n,r,v)) → ∃q : quorum.∀n : node. member(n,q) → vote_msg(n,r,v) *) 

 let inv4 r v = 
   let hist = get_all in
   let rv_decided = List.exists hist (check_decided_rv r v) in
   if rv_decided then
     let n_repls = 3 in (*List.length repl_ids in*)
     let n_accepts = List.fold_right (inc_if_decided_rv r v) hist 0 in
     2*n_accepts > n_repls
   else true

(* ∀n : node, r,r′: round, v,v′: value. 
 join_ack_msg(n,r, ⊥,v) ∧ r′ < r → ¬vote_msg(n,r′,v′) *)

 let check_inv5 r' ahist eff1 = 
   match eff1 with
   | Some eff ->
       (match eff with
       | Acceptor.Promise {round=r} -> 
         if r'<r then 
           not (List.exists ahist (check_accepted_r r'))
         else true
       | _ -> true)
   | _ -> true

 let inv5 n r' = 
   let ahist = Acceptor_table.get n Acceptor.Get in
   List.forall ahist (check_inv5 r' ahist)

(* ∀n : node, r,r′: round, v : value. 
 join_ack_msg(n,r,r′,v) ∧ r′ <> ⊥ → r′ < r ∧ vote_msg(n,r′,v) *)

let check_inv6 ahist eff1 = 
  match eff1 with
  | Some eff ->
        (match eff with
        | Acceptor.PromiseWithPrev {prev_vote_round=r';
                            prev_vote_val=v;round=r} -> 
            r'<r && List.exists ahist (check_accepted_rv r' v)
        | _ -> true)
  | _ -> true

let inv6 n = 
  let ahist = Acceptor_table.get n Acceptor.Get in
  List.forall ahist (check_inv6 ahist)

(* ∀n : node, r,r′,r′′: round, v,v′: value.
join_ack_msg(n,r,r′,v) ∧ r′ <> ⊥ ∧ r′ < r′′ < r → ¬vote_msg(n,r′′,v′) *)

let check_inv7 r'' ahist eff1 = 
  match eff1 with
   | Some eff ->
         (match eff with
         | Acceptor.PromiseWithPrev {prev_vote_round=r';
                              prev_vote_val=v;round=r} -> 
           if r'<r'' && r''<r then
             not (List.exists ahist (check_accepted_r r''))
           else true
         | _ -> true)
   | _ -> true
 
let inv7 n r'' = 
  let ahist = Acceptor_table.get n Acceptor.Get in
  List.forall ahist (check_inv7 r'' ahist) 

let inv_fun (n:Uuid.t) (r:int) (v:int) =
  inv7 n r &&
  inv6 n &&
  inv5 n r &&
  inv4 r v &&
  inv3 n r v &&
  inv2 r &&
  inv1 0