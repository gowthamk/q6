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

module Item = 
struct
  type id = Uuid.t
  type eff = GetItem
             | StockItem of {desc: string; minPrice: int; maxBid:int}
             | RemoveFromStock
             | UpdateMaxBid of {amt: int}
end

module Item_table =
struct
  include Store_interface.Make(Item)
end

module Wallet = 
struct
  type id = Uuid.t
  type eff =  GetBalance
              | DepositToWallet of {amt: int}
              | WithdrawFromWallet of {amt: int}
end 

module Wallet_table =
struct
  include Store_interface.Make(Wallet)
end

module Bids = 
struct
  type id = Uuid.t
  type eff =  AddBid of {walletID: Wallet.id; itemID: Item.id}
              | GetBid
              | CancelBid
end 

module Bids_table =
struct
  include Store_interface.Make(Bids)
end

module ItemBids = 
struct
  type id = Item.id
  type eff = AddItemBid of {bidID: Bids.id}
             | GetBidsByItem 
             | RemoveItemBid of {bidID: Bids.id}
end

module ItemBids_table =
struct
  include Store_interface.Make(ItemBids)
end

module WalletBids = 
struct
  type id = Wallet.id
  type eff = AddWalletBid of {bidID: Bids.id; timestamp: int}
             | GetBidsByWallet
             | RemoveWalletBid of {bidID: Bids.id; timestamp: int}
end

module WalletBids_table =
struct
  include Store_interface.Make(WalletBids)
end

module DummyModuleForMkkeyString = struct
  type id = string
  type eff = Get
end

module DummyModuleForMkkeyString_table =
struct
  include Store_interface.Make(DummyModuleForMkkeyString)
end

module WalletItems = 
struct
  type id = Wallet.id
  type eff = AddWalletItem of {itemID: Item.id}
             | GetItemsByWallet
end

module WalletItems_table =
struct
  include Store_interface.Make(WalletItems)
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

let if_ab_get_ts (bidsid:Bids.id) (eff: WalletBids.eff option) = match eff with
  | Some x -> (match x with
      | WalletBids.AddWalletBid {bidID=bidsid1; timestamp=ts} -> 
          if bidsid=bidsid1 then Some ts else None
      | _ -> None)
  | None -> None

let if_rb_get_ts (bidsid:Bids.id) (eff: WalletBids.eff option) = match eff with
  | Some x -> (match x with
      | WalletBids.RemoveWalletBid {bidID=bidsid1; timestamp=ts} -> 
          if bidsid=bidsid1 then Some ts else None
      | _ -> None)
  | None -> None

let is_valid_bid bidsid ctxt = 
  let ab_ts = List.map (if_ab_get_ts bidsid) ctxt in
  let rb_ts = List.map (if_rb_get_ts bidsid) ctxt in
  let max_ab_ts = max_ts ab_ts in
  let max_rb_ts = max_ts rb_ts in
    max_ab_ts >= max_rb_ts

let find_bids_by_wallet ctxt eff =
  match eff with
  | Some x -> 
    (match x with 
    | WalletBids.AddWalletBid {bidID=bidsid} -> 
      if is_valid_bid bidsid ctxt then Some bidsid else None
    | _ -> None) 
  | _ -> None

let get_bids_by_wallet wid =
  let ctxt = WalletBids_table.get wid (WalletBids.GetBidsByWallet) in
  List.map (find_bids_by_wallet ctxt) ctxt

let get_amt x = 
  match x with 
  | Some e -> (match e with 
                 | Wallet.WithdrawFromWallet {amt=a} -> 0-a
                 | Wallet.DepositToWallet {amt=a} -> a
                 | _ -> 0)
  | None -> 0

let compute_bal b acc = b+acc

let get_balance_wallet wid = 
  let ctxt = Wallet_table.get wid (Wallet.GetBalance) in
  let bals = List.map (get_amt) ctxt in
  let bal = List.fold_right compute_bal bals 0 in
  bal

let do_withdraw_wallet wid a = 
  let curr_bal = get_balance_wallet wid in
  if curr_bal >= a then 
    (Wallet_table.append wid (Wallet.WithdrawFromWallet {amt=a}); true)
  else false

let do_bid_for_item itemid wid = 
  let bidid = Uuid.create() in
  begin
    WalletBids_table.append wid (WalletBids.AddWalletBid{bidID=bidid; timestamp=0});
    Bids_table.append bidid (Bids.AddBid{walletID=wid; itemID=itemid})
  end

let bid_eff_has_add eff = 
  match eff with
  | Some x -> (match x with
              | Bids.AddBid {walletID=wid; itemID=iid} -> true
              | _ -> false)
  | _ -> false

let bid_eff_has_cancel eff = 
  match eff with 
  | Some x -> (match x with
              | Bids.CancelBid -> true
              | _ -> false)
  | _ -> false

let bid_exists bidid = 
  match bidid with
  | Some x -> let l = Bids_table.get x (Bids.GetBid) in
              let b = List.exists l (bid_eff_has_cancel) in
              if b then false 
              else List.exists l (bid_eff_has_add)
  | _ -> true

let check_bid_for_item wid = 
  let bids_by_wallet = get_bids_by_wallet wid in
  List.forall bids_by_wallet bid_exists

let check_withdraw_wallet wid = 
  let bal = get_balance_wallet wid in
  bal >= 0

let inv_fun wid = 
  (check_bid_for_item wid) && (check_withdraw_wallet wid)