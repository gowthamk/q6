open Q6_interface

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
end

module Acceptor = 
struct
  type id = int
  type eff = PrepareRequest of {n:int}
            | SetPromise of {proposal_id: int}
            | Accept of {proposal_id:int; v:int}
            | Accepted of {proposal_id:int; v:int}
            | GetSummary
end

module Acceptor_table =
struct
  include Store_interface.Make(Acceptor)
end

module Learner = 
struct
  type id = int
  type eff = Accepted of {proposal_id:int; v:int; 
                          acceptor:Acceptor.id}
            | GetSummary
end

module Learner_table =
struct
  include Store_interface.Make(Learner)
end

module Proposer = 
struct
  type id = int
  type eff = PrepareResponse of {proposal_id: int; v: int}
             | Ack of {proposal_id: int; acceptor: Acceptor.id;
               prev_accepted_n: int;prev_accepted_v: int}
             | AcceptRequested of {proposal_id:int; v:int}
             | GetSummary
end

module Proposer_table =
struct
  include Store_interface.Make(Proposer)
end

let rec first f b l = match l with
  | [] -> b
  | x::xs -> 
      let t = first f b xs in
      match x with 
      | Some y -> if f y then y 
          else t
      | None -> t

let is_gte ts tsop' = match tsop' with 
 | Some ts' -> ts' <= ts 
 | None -> true

let is_max_in (ts_list : int option list) (ts:int) = 
  List.forall ts_list (is_gte ts)

let rec max_ts (ts_list: int option list) : int = 
  first (is_max_in ts_list) (0-1) ts_list

(*let do_proposal n1 v1 =
  (*n must be a unique value, enforce this in contracts*)
  Acceptor_table.append (0-1) (Acceptor.PrepareRequest{n=n1; v=v1})*)

let rec get_v_for_proposal proposal effs = 
  match effs with
  | [] -> 0-1
  | eff::rest ->
    let t = get_v_for_proposal proposal rest in
    (match eff with
    | Some x -> 
      (match x with
      | Acceptor.Accepted{proposal_id=n1; v=v1} -> 
        if n1=proposal then v1 else t
      | _ -> t)
    | _ -> t)

let get_proposal_id eff =
  match eff with
  | Some x -> 
    (match x with
    | Acceptor.PrepareRequest{n=n1} -> Some n1
    | _ -> None)
  | _ -> None

let get_promise eff =
  match eff with
  | Some x -> 
    (match x with
    | Acceptor.SetPromise{proposal_id=pid} -> Some pid
    | _ -> None)
  | _ -> None

let get_accepted eff =
  match eff with
  | Some x -> 
    (match x with
    | Acceptor.Accepted{proposal_id=pid} -> Some pid
    | _ -> None)
  | _ -> None

let prev_accepted_case acceptor_effs max_prev_accepted n1 a_id p_id = 
  let prev_v = get_v_for_proposal max_prev_accepted acceptor_effs in
  begin
    Proposer_table.append p_id (Proposer.Ack{proposal_id=n1;
                              prev_accepted_n=max_prev_accepted;
                              prev_accepted_v=prev_v;
                              acceptor=a_id});
    Acceptor_table.append a_id (Acceptor.SetPromise{proposal_id=n1})
  end

let prev_not_accepted_case n1 a_id (p_id:Proposer.id) = 
  Proposer_table.append p_id (Proposer.Ack{proposal_id=n1;
                               prev_accepted_n=(0-1);
                               prev_accepted_v=(0-1);
                               acceptor=a_id});
  Acceptor_table.append a_id (Acceptor.SetPromise{proposal_id=n1})

let do_response acceptor_effs n1 a_id p_id =
  begin
    let prev_accepted = List.map get_accepted acceptor_effs in
    let max_prev_accepted = max_ts prev_accepted in
    if max_prev_accepted > -1 then
      (*A previous value was accepted*) 
      prev_accepted_case acceptor_effs max_prev_accepted n1 a_id p_id
    else
      prev_not_accepted_case n1 a_id p_id
  end

(*Paxos Phase-1 acceptor responds to prepare message*)

let gt x y = x > y

let do_proposal_response n1 a_id p_id = 
  let acceptor_effs = Acceptor_table.get a_id (Acceptor.GetSummary) in
  let prev_promises = List.map get_promise acceptor_effs in
  let max_prev_promise = max_ts prev_promises in
  if gt n1 max_prev_promise then 
    do_response acceptor_effs n1 a_id p_id 
  else ()

let cnt_vote n eff acc = 
 match eff with
 | Some x -> 
     (match x with
     | Proposer.Ack{proposal_id=max_n} -> 
       if max_n=n then acc+1 else acc
     | _ -> acc)
 | _ -> acc

let cnt_votes effs n = List.fold_right (cnt_vote n) effs 0

let get_v n' eff = 
 match eff with
 | Some x -> 
     (match x with
     | Proposer.Ack{proposal_id=max_n;prev_accepted_v=v} -> 
       if max_n=n' then Some v else None
     | _ -> None)
 | _ -> None

let get_acceptor n' eff = 
  match eff with
  | Some x -> 
      (match x with
      | Proposer.Ack{proposal_id=max_n;acceptor=a_id} -> 
        if max_n=n' then a_id else (0-1)
      | _ -> (0-1))
  | _ -> (0-1)

let send_accept v_max v' n' p_id a_id =
  if a_id > -1 then 
  (if v_max > -1 then
   begin
     Acceptor_table.append a_id (Acceptor.Accept{proposal_id=n'; v=v_max});
     Proposer_table.append p_id (Proposer.AcceptRequested{proposal_id=n'; 
                                            v=v_max})
   end
  else 
   begin
    Acceptor_table.append a_id (Acceptor.Accept{proposal_id=n'; v=v'});
    Proposer_table.append p_id (Proposer.AcceptRequested{proposal_id=n'; 
                                            v=v'})
   end)
  else ()

(*Paxos Phase-2 proposer responds to promise message*)

let do_promise_response n' v' p_id =
  let prep_response_effs = Proposer_table.get p_id (Proposer.GetSummary) in
  if gt (cnt_votes prep_response_effs n') 1 then
    (let v_list = List.map (get_v n') prep_response_effs in
    let v_max = max_ts v_list in
    let acceptors = List.map (get_acceptor n') prep_response_effs in
    List.iter (send_accept v_max v' n' p_id) acceptors)
  else ()

let rec check_accept n v' effs = 
  match effs with
  | [] -> false
  | eff::rest -> 
    let t = check_accept n v' rest in
    (match eff with
     | Some x -> (match x with
                 | Acceptor.Accept{proposal_id=n1; v=v1} -> 
                   if n=n1 && v'=v1 then true else t
                 | _ -> t)
     | _ -> t) 

(*Paxos Phase-3 acceptor responds to accept message*)

let get_n_from_prepare eff = 
  match eff with
  | Some x -> 
    (match x with
    | Acceptor.PrepareRequest{n=n1} -> Some n1
    | _ -> None)
  | _ -> None

let do_accept n' v' a_id =
  let acceptor_effs = Acceptor_table.get a_id (Acceptor.GetSummary) in
  (*if check_accept n' v' acceptor_effs then*)
  let curr_proposals = List.map get_n_from_prepare acceptor_effs in
  let max_n = max_ts curr_proposals in
  if gt max_n n' then
  begin
    Acceptor_table.append a_id (Acceptor.Accepted{proposal_id=n';v=v'});
    Learner_table.append (0-1) (Learner.Accepted{proposal_id=n';v=v';
                                acceptor=a_id})
  end
  else ()
   (*else ()*)

let get_n_from_ack eff = 
 match eff with
 | Some x -> 
     (match x with
     | Proposer.Ack{proposal_id=max_n} -> 
       Some max_n
     | _ -> None)
 | _ -> None

let check_accepted_n n eff = 
  match eff with
  | Some x -> (match x with
             | Acceptor.Accepted{proposal_id=n1; v=v1} -> 
               n=n1
             | _ -> false)
  | _ -> false

let inv_fun1 n1 a_id = 
  (*An accepter accepts a proposal numbered n if and only if it has not 
    responded to a prepare message with a number n' > n *)
  let acceptor_effs = Acceptor_table.get a_id (Acceptor.GetSummary) in
  let prev_promises = List.map get_promise acceptor_effs in
  let n' = max_ts prev_promises in
  if List.exists acceptor_effs (check_accepted_n n1) then
    gt n1 n'
  else true

let rec check_accept_issued n v' effs = 
  match effs with
  | [] -> false
  | eff::rest -> 
    let t = check_accept_issued n v' rest in
    (match eff with
     | Some x -> 
       (match x with
        | Proposer.AcceptRequested{proposal_id=n1; v=v1} -> 
          if n=n1 && v'=v1 then true else t
        | _ -> t)
     | _ -> t)

let get_acceptor_for_nv n v eff = 
  match eff with
  | Some x -> 
    (match x with
     | Learner.Accepted{proposal_id=n1; v=v1} -> 
       if n1=n&&v1=v then n1 else (0-1)
     | _ -> (0-1))
  | _ -> (0-1)

let acceptor_accepted_lt_n n a_id eff acc = 
  match eff with
  | Some x -> 
    (match x with
     | Learner.Accepted{proposal_id=n1; v=v1; acceptor=a} -> 
       if a=a_id && n1<n then false else acc
     | _ -> acc)
  | _ -> acc

let accepted_lt_n n effs a_id acc = 
  let b = List.fold_right (acceptor_accepted_lt_n n a_id) effs true in
  if b then acc+1 else acc

let get_v_if_lt_n n a_id eff = 
  match eff with
  | Some x -> 
    (match x with
     | Learner.Accepted{proposal_id=n1; v=v1; acceptor=a} -> 
       if a=a_id && n1<n then Some v1 else None
     | _ -> None)
  | _ -> None

let accepted_lt_n_v_is_max n v effs a_id acc = 
  let v_list = List.map (get_v_if_lt_n n a_id) effs in
  let v_max = max_ts v_list in
  if v=v_max then acc+1 else acc

let inv_fun2 n' v' p_id = 
  (* For any v and n, if a proposal with value v and number n has been issued 
    (by sending accept messages) then there is a majority of accepters S 
    such that either*) 
  let proposer_effs = Proposer_table.get p_id (Proposer.GetSummary) in
  let accept_issued = check_accept_issued n' v' proposer_effs in
  let learner_effs = Learner_table.get (0-1) (Learner.GetSummary) in
  if accept_issued then
    (let acceptors = List.map (get_acceptor_for_nv n' v') learner_effs in
    let cnt_acceptors_acc_lt_n = List.fold_right (accepted_lt_n n' learner_effs) 
                                                   acceptors 0 in
  (*(a) no accepter in S has accepted any proposal numbered less than n*)
    let a = gt 2 cnt_acceptors_acc_lt_n in 
    let cnt_acceptors_acc_lt_n_v_is_max = List.fold_right 
                       (accepted_lt_n_v_is_max n' v' learner_effs) acceptors 0 in
  (*or (b) v is the value of the highest-numbered proposal among all proposals 
  numbered less than n accepted by the accepters in S (>=2)
  <=> *)
    let b = gt cnt_acceptors_acc_lt_n_v_is_max 1 in
    a||b)
  else true