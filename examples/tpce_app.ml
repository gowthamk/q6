open Q6_interface

module List = 
struct
  open List
  let rec map f l = match l with
    | [] -> []
    | x::xs -> (f x)::(map f xs)

  let rec fold_right f l b = match l with
    | [] -> b
    | x::xs -> f x (fold_right f xs b)

  let rec iter f l = match l with
    | [] -> ()
    | x::xs -> (f x; iter f xs)

  let rec length l = match l with
    | [] -> 0
    | x::xs -> 1 + (length xs)

  let rec first_some l = match l with
    | [] -> None
    | x::xs -> (match x with 
                  | None -> first_some xs
                  | Some _ -> x)

  let rec forall l f = match l with
    | [] -> true
    | x::xs -> (f x)&&(forall xs f)

  let rec filter f l = match l with
    | [] -> []
    | x::xs -> if f x then x::filter f xs else filter f xs

  let rec contains l x = match l with
    | [] -> false
    | y::ys -> y=x || contains ys x

  let rec hd l = match l with
    | [] -> raise Inconsistency
    | x::xs -> x

  let rec exists l f = match l with
    | [] -> false
    | x::xs -> (f x)||(exists xs f)
end

module L =
struct
  let forall l f = true
  let exists l f = true
end

(*If no consistency is mentioned beside the effect, then it's EC.*)

module Broker = struct
  type id = Uuid.t
  type eff = Get
    | AddCommision of {b_id: id;b_ca_id:Uuid.t(*Customer*);b_comm:int}
end

module Broker_table =
struct
  include Store_interface.Make(Broker)
end

module Trade = struct
  type id = Uuid.t
  type eff = Get (*Consistency: CW*)
    | AddTrade of {t_id:id; t_ca_id:Uuid.t(*Customer.id*);t_comm:int}
    | SetCmpltAndComm of {t_id:id;t_ca_id:Uuid.t(*Customer.id*); t_comm:int} (*Consistency: TW+CW*)
end

module Trade_table =
struct
  include Store_interface.Make(Trade)
end

module Holding = struct
  type id = Uuid.t
  type eff = Get
    | AddHolding of {h_t_id:Trade.id; h_ca_id:Uuid.t(*Customer.id*); h_qty:int}
end

module Holding_table =
struct
  include Store_interface.Make(Holding)
end

module HoldingSummary = struct
  type id = Uuid.t
  type eff = Get
    | AddHoldingQty of {hs_ca_id: Uuid.t(*Customer.id*); hs_qty :int}
end

module HoldingSummary_table =
struct
  include Store_interface.Make(HoldingSummary)
end

(*One dummy id per table*)
let dummy_tid = Uuid.create()
let dummy_bid = Uuid.create()
let dummy_hid = Uuid.create()
let dummy_hsid = Uuid.create()

(* Irrelevant *)
(*let do_trade_order_txn acct_id =
  let comm_amount = b_comm * trade_qty * requested_price in
  let t_id = Uuid.create() in
  Trade_table.append t_id Trade.AddTrade {t_ca_id=acct_id; t_comm=comm_amount}*)

(*<<<<<<<<<<AUXILIARY FUNCTIONS BEGIN>>>>>>>>>>>>>>>>*)
let check_trade_exists tid ca_id trade_eff =
  match trade_eff with
  | Some x ->
    (match x with
     | Trade.AddTrade{t_id=tid1; t_ca_id=cid1} -> tid=tid1 && ca_id=cid1
     | _ -> false)
  | _ -> false

let check_completed tid trade_eff =
  match trade_eff with
  | Some x ->
    (match x with
     | Trade.SetCmpltAndComm{t_id=tid1} -> tid=tid1
     | _ -> false)
  | _ -> false

let get_broker_num_trades ca_id eff acc =
  match eff with
  | Some x ->
    (match x with
     | Broker.AddCommision{b_ca_id=customer} -> 
       if ca_id=customer then acc+1 else acc
     | _ -> acc)
  | _ -> acc

let get_broker_comm ca_id eff acc =
  match eff with
  | Some x ->
    (match x with
     | Broker.AddCommision{b_ca_id=customer;b_comm=comm} -> 
       if ca_id=customer then acc+comm else acc
     | _ -> acc)
  | _ -> acc

let get_num_trades_by_customer ca_id trade_effs eff acc =
  match eff with
  | Some x ->
    (match x with
     | Trade.AddTrade{t_id=tid;t_ca_id=customer} ->
       if customer=ca_id && (List.exists trade_effs (check_completed tid))
       then acc+1 else acc
     | _ -> acc)
  | _ -> acc

let get_trades_comm_by_customer ca_id eff acc =
  match eff with
  | Some x ->
    (match x with
     | Trade.SetCmpltAndComm{t_ca_id=customer;t_comm=comm} -> 
       if customer=ca_id then acc+comm else acc
     | _ -> acc)
  | _ -> acc

let get_holding_qty ca_id eff acc =
  match eff with
  | Some x ->
    (match x with
     | Holding.AddHolding{h_ca_id=customer; h_qty=qty} -> 
       if customer=ca_id then acc+qty else acc
     | _ -> acc)
  | _ -> acc

let get_holding_summary_qty ca_id eff acc =
  match eff with
  | Some x ->
    (match x with
     | HoldingSummary.AddHoldingQty{hs_ca_id=customer;hs_qty=qty} ->
       if customer=ca_id then acc+qty else acc
     | _ -> acc)
  | _ -> acc
(* <<<<<<<<<<AUXILIARY FUNCTIONS END>>>>>>>>>>>>>>>>*)

(*Txn Consistency: Atomic*)
let do_trade_res_txn (tid:Trade.id) acct_id trade_qty trade_price comm_rate broker_id tt_is_sell = 
  let comm_amount = comm_rate * trade_qty * trade_price in
  let trade_effs = Trade_table.get dummy_tid (Trade.Get) in
  if (List.exists trade_effs (check_trade_exists tid acct_id)) && 
     (not (List.exists trade_effs (check_completed tid))) then
  begin
    Trade_table.append dummy_tid (Trade.SetCmpltAndComm 
                                      {t_id=tid;t_ca_id=acct_id; t_comm=comm_amount});
    (* Combining updates to b_comm and b_num_trades, 
       1 Broker.AddCommision effect = b_num_trades++ *)
    Broker_table.append dummy_bid (Broker.AddCommision {b_id=broker_id;b_ca_id=acct_id;
                                                          b_comm=comm_amount});
    if tt_is_sell then
    begin
      let qty = 0-trade_qty in
      (*Assume there exists only one symbol.*)
      HoldingSummary_table.append dummy_hsid (HoldingSummary.AddHoldingQty{hs_ca_id=acct_id;hs_qty=qty});
      Holding_table.append dummy_hid (Holding.AddHolding{h_t_id=tid;h_ca_id=acct_id; h_qty=qty})
    end
    else
    begin
      HoldingSummary_table.append dummy_hsid (HoldingSummary.AddHoldingQty{hs_ca_id=acct_id;hs_qty=trade_qty});
      Holding_table.append dummy_hid (Holding.AddHolding{h_t_id=tid;h_ca_id=acct_id; h_qty=trade_qty})
    end
  end
  else () 

(*<<<<<<<<<< INVARIANT FUNCTIONS BEGIN >>>>>>>>>>>>>>>>*)

let inv_fun1 ca_id1 =
  let trade_effs = Trade_table.get dummy_tid (Trade.Get) in
  let broker_effs = Broker_table.get dummy_bid (Broker.Get) in  
  let b_num_trades = List.fold_right (get_broker_num_trades ca_id1) broker_effs 0 in
  let num_trades_by_customer = List.fold_right 
                      (get_num_trades_by_customer ca_id1 trade_effs) trade_effs 0 in
  b_num_trades = num_trades_by_customer

let inv_fun2 ca_id2 =
  let trade_effs = Trade_table.get dummy_tid (Trade.Get) in
  let broker_effs = Broker_table.get dummy_bid (Broker.Get) in  
  let b_comm = List.fold_right (get_broker_comm ca_id2) broker_effs 0 in
  let t_comm = List.fold_right (get_trades_comm_by_customer ca_id2) trade_effs 0 in
  b_comm = t_comm

let inv_fun3 ca_id3 =
  let holding_summary_effs = HoldingSummary_table.get dummy_hsid (HoldingSummary.Get) in  
  let holding_effs = Holding_table.get dummy_hid (Holding.Get) in
  let h_qty = List.fold_right (get_holding_qty ca_id3) holding_effs 0 in
  let hs_qty = List.fold_right (get_holding_summary_qty ca_id3) holding_summary_effs 0 in
  h_qty = hs_qty
(*<<<<<<<<<< INVARIANT FUNCTIONS END >>>>>>>>>>>>>>>>*)
