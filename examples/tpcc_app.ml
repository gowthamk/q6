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

module Warehouse = struct
  type id = Uuid.t
  type eff = Get
    | AddYTD of {w_id:id; ytd:int} 
end

module Warehouse_table =
struct
  include Store_interface.Make(Warehouse)
end

module District = struct
  type id = Uuid.t
  type eff = Get 
    | Add
    | IncNextOID of {d_id:id; d_w_id:Warehouse.id} (*Consistency: TW*)
end

module District_table =
struct
  include Store_interface.Make(District)
end

module Customer = struct
  type id = Uuid.t
  type eff = Get
    | AddBal of {c_id:id; c_w_id:Warehouse.id; c_d_id:District.id; c_bal:int}
end

module Customer_table =
struct
  include Store_interface.Make(Customer)
end

module History = struct
  type id = Uuid.t
  type eff = Get
    | Append of {h_w_id: Warehouse.id; h_d_id: District.id; h_c_id: Customer.id; 
                 h_c_w_id: Warehouse.id; h_c_d_id: District.id; h_amount: int}
end

module History_table =
struct
  include Store_interface.Make(History)
end

module Order = struct
  type id = Uuid.t
  type eff = Get 
    | Add of {o_id: int; o_w_id: Warehouse.id; o_d_id: District.id; 
              o_c_id: Customer.id; o_ol_cnt: int}
    | SetCarrier of {o_id: int; o_w_id: Warehouse.id; o_d_id: District.id;
                     o_carrier_id: int}
end

module Order_table =
struct
  include Store_interface.Make(Order)
end

module Orderline = struct
  type id = Uuid.t
  type eff = Get
    | Add of  {ol_o_id: int; ol_d_id: District.id; ol_w_id: Warehouse.id; 
               ol_amt: int; (*ol_i_id: Item.id;*) ol_supply_w_id: Warehouse.id;
               ol_delivery_d: int; ol_qty: int; ol_c_id: Customer.id}
    | SetDeliveryDate of {ol_o_id: int; ol_d_id: District.id; 
                          ol_w_id: Warehouse.id;ol_delivery_d: int}
end

module Orderline_table =
struct
  include Store_interface.Make(Orderline)
end

(* One dummy id per table *)
(* All the effects for a single table are added on the same dummy key,
   makes checking the invariant easier. The effect specifies the id it
   is actually to be applied on. For example, the IncNextOID of the district 
   table specifies the d_id:District.id and d_w_id:Warehouse.id it corresponds
   to as part of its record.*)
let dummy_hid = Uuid.create()
let dummy_did = Uuid.create()
let dummy_oid = Uuid.create()
let dummy_noid = Uuid.create()
let dummy_olid = Uuid.create()
let dummy_wid = Uuid.create()
let dummy_cid = Uuid.create()

(*<<<<<<<<<<AUXILIARY FUNCTIONS BEGIN>>>>>>>>>>>>>>>>*)

let rec first f b l = match l with
  | [] -> b
  | x::xs -> let t = first f b xs in
                     match x with 
                    | Some y -> if f y then y 
                        else t
                    | None -> t

let is_gte (ts:int) tsop' = match tsop' with 
 | Some ts' -> ts' <= ts 
 | None -> true

let is_lte (ts:int) tsop' = match tsop' with 
 | Some ts' -> ts' >= ts 
 | None -> true

let is_max_in ts_list ts = 
  List.forall ts_list (is_gte ts)

let is_min_in ts_list ts = 
  List.forall ts_list (is_lte ts)
    
let max ts_list = 
  first (is_max_in ts_list) (0-1) ts_list

let min ts_list = 
  first (is_min_in ts_list) (0-1) ts_list

let sum a b = a+b
let sub a b = a-b

let timestamp = 0

let get_nextoid_sum did dwid eff1 acc =
  match eff1 with
  | Some z -> 
    (match z with 
     | District.IncNextOID {d_id=did2; d_w_id=dwid2} -> 
        if did2 = did && dwid2 = dwid then sum acc 1 else acc
     | _ -> acc)
  | _ -> acc

let get_latest_nextoid did dwid = 
  let d_effs = District_table.get dummy_did (District.Get) in
  List.fold_right (get_nextoid_sum did dwid) d_effs 0

let get_oadd_oid did dwid eff1 = 
  match eff1 with 
  | Some z -> 
    (match z with 
    | Order.Add {o_id=oid2; o_w_id=wid2; o_d_id=did2} -> 
      if did2 = did && wid2 = dwid then Some oid2 else None
    | _ -> None)
  | _ -> None

let get_maxoid did dwid =
  let o_effs = Order_table.get dummy_oid (Order.Get) in
  let oid_list = List.map (get_oadd_oid did dwid) o_effs in 
  max oid_list

let get_waddytd dwid eff acc = 
 match eff with 
 | Some x -> (match x with 
            | Warehouse.AddYTD {w_id=dwid1; ytd=ytd1} -> 
              if dwid1=dwid then sum acc ytd1 else acc
            | _ -> acc)
 | _ -> acc

let get_warehouse_ytd dwid =
  let whs_effs = Warehouse_table.get dummy_wid (Warehouse.Get) in
  List.fold_right (get_waddytd dwid) whs_effs 0

let get_caddbal cid cdid cwid eff1 = 
  match eff1 with 
  | Some y -> (match y with 
             | Customer.AddBal {c_id=cid1; c_w_id=wid1; 
                                 c_d_id=did1;c_bal=bal} -> 
                if cid1=cid && wid1=cwid && did1=cdid 
                then bal else 0
             | _ -> 0)
  | _ -> 0 

let get_customer_bal (cid:Customer.id) (cdid:District.id) (cwid:Warehouse.id) =
  let c_effs = Customer_table.get dummy_cid (Customer.Get) in
  List.fold_right sum (List.map (get_caddbal cid cdid cwid) c_effs) 0

 let get_hamt_wid wid eff acc = 
   match eff with
   | Some x -> (match x with
                | History.Append {h_w_id = hdwid; h_d_id = hdid; h_amount = h_amt} -> 
                  if hdwid=wid then sum acc h_amt else acc
                | _ -> acc)
   | _ -> acc

 let get_olamt wid did oid eff = 
   match eff with
   | Some x -> (match x with
               | Orderline.Add {ol_o_id= oid1; ol_d_id=did1; ol_w_id=wid1; ol_amt=amt} -> 
                 if (wid1=wid && did1=did && oid1=oid) then amt else 0
               | _ -> 0)
   | _ -> 0

 let rec get_olcnt wid did oid effs = 
   match effs with
   | [] -> 0
   | eff::rest ->
     let t = get_olcnt wid did oid rest in
     (match eff with
     | Some x -> (match x with
                 | Order.Add {o_w_id=wid1; o_d_id=did1; o_ol_cnt=cnt; o_id=oid1} -> 
                   if (wid1=wid && did1=did && oid1=oid) then cnt else t
                 | _ -> t)
     | _ -> t)

 let get_hamt_wcdid wid cid did eff acc = 
   match eff with
   | Some x -> (match x with
                | History.Append {h_c_w_id = hdwid; h_c_d_id = hdid; 
                                  h_c_id = hcid; h_amount = h_amt} -> 
                  if hdwid=wid && hdid=did && hcid=cid then sum acc h_amt else acc
                | _ -> acc)
   | _ -> acc

 let get_ol_rows_cnt oid did wid eff acc = 
   match eff with 
   | Some x -> (match x with
                | Orderline.Add {ol_o_id=oid1; ol_d_id=did1; ol_w_id=wid1} -> 
                  if oid = oid1 && did = did1 && wid = wid1 
                    then sum acc 1 else acc
                | _ -> acc)
   | _ -> acc

 let process_ireq olsupplywid olqty latest_nextoid did wid cid ireq = 
   let ireq_ol_supply_w_id = olsupplywid in
   let ireq_ol_qty = olqty in
   let price = 3 in
     begin
       Orderline_table.append dummy_olid (Orderline.Add 
        {ol_o_id=latest_nextoid;
         ol_c_id=cid;
         ol_d_id=did; 
         ol_w_id=wid; 
         ol_supply_w_id=ireq_ol_supply_w_id; 
         ol_amt=price * ireq_ol_qty;
         ol_delivery_d=(0-1);
         ol_qty=ireq_ol_qty})
     end 

let get_ol_ids wid did o eff = 
  match eff with
  | Some x -> 
    (match x with
    | Orderline.Add {ol_o_id= oid1; ol_d_id=did1; ol_w_id=wid1} ->
      if oid1=o && wid1=wid && did1=did 
        then Some oid1 else None
    | _ -> None)
  | _ -> None

let get_olamt_cid wid did cid orderline_ctxt oeff =
  match oeff with
  | Some x -> 
      (match x with 
       | Order.Add {o_id=oid; o_c_id=ocid; o_w_id=w_id; o_d_id=d_id} ->
          if w_id = wid && d_id = did && ocid=cid then
            let amts = List.map (get_olamt wid did oid) orderline_ctxt in
            let amt = List.fold_right sum amts 0 in 
            amt
          else 0
       | _ -> 0) 
  | _ -> 0

let process_ol ol did wid =  
  match ol with
  | Some olx ->
    Orderline_table.append dummy_olid (Orderline.SetDeliveryDate{ol_o_id=olx;
    ol_d_id=did;ol_w_id=wid;ol_delivery_d=0})
  | _ -> ()
 
let rec process_order wid did o oeffs = 
  match oeffs with
  | [] -> ()
  | oeff::rest -> 
    let t = process_order wid did o rest in
    match oeff with
    | Some x -> 
      (match x with 
       | Order.Add {o_id=oid; o_c_id=ocid; o_w_id=w_id; o_d_id=d_id} ->
           if w_id = wid && d_id = did && o=oid then 
           (let orderline_ctxt = Orderline_table.get dummy_olid (Orderline.Get) in
            let ols = List.map (get_ol_ids wid did o) orderline_ctxt in
            let amts = List.map (get_olamt wid did o) orderline_ctxt in
            let amt = List.fold_right sum amts 0 in 
            begin
              (*NewOrder_table.append dummy_noid (NewOrder.Remove{no_w_id = wid;
                                         no_o_id=o;no_d_id = did});*)
              Order_table.append dummy_oid (Order.SetCarrier {o_id=o;o_w_id=wid;
                                         o_d_id=did;o_carrier_id=0});
              Orderline_table.append dummy_olid (Orderline.SetDeliveryDate{ol_o_id=o;
                                         ol_d_id=did;ol_w_id=wid;ol_delivery_d=0});
              Customer_table.append dummy_cid (Customer.AddBal{c_id=ocid;
                                 c_bal=amt; c_d_id=did;c_w_id=wid});
            end)
           else t
       | _ -> t)
    | _ -> t

let check_delivery_set wid did oid oleff = 
  match oleff with
  | Some eff -> 
    (match eff with
     | Orderline.SetDeliveryDate{ol_o_id=olx;
        ol_d_id=did1;ol_w_id=wid1} ->
      olx=oid && did=did1 && wid1=wid
     | _ -> false)
  | _ -> false

let check_carrier_set wid did oid oeff =
  match oeff with
  | Some eff ->
    (match eff with
     | Order.SetCarrier{o_id=o;o_w_id=wid1;o_d_id=did1} ->
        o=oid && did=did1 && wid1=wid
     | _ -> false)
  | _ -> false

(* <<<<<<<<<<AUXILIARY FUNCTIONS END>>>>>>>>>>>>>>>>*)

(*Txn Consistency: Atomic*)
let do_new_order_txn did wid cid olqty olsupplywid = 
  let ireqs = [1;2] in
  begin
    (*TODO: without appending something to key dummy_did
      we can't do get_latest_nextoid on key dummy_did.*)
    District_table.append dummy_did (District.Add);
    let latest_nextoid = get_latest_nextoid did wid in
    District_table.append dummy_did (District.IncNextOID 
                               {d_id=did;
                                d_w_id=wid});
    (* -1 for o_carried_id represents None *)
    Order_table.append dummy_oid (Order.Add 
     {o_id=latest_nextoid; o_w_id=wid; o_d_id=did; 
      o_c_id=cid; o_ol_cnt=(List.length ireqs)});
    List.iter (process_ireq olsupplywid olqty 
               latest_nextoid did wid cid) ireqs
  end

(*Txn Consistency: Atomic*)
let do_payment_txn h_amt did dwid cdid cwid cid =
  begin
    Warehouse_table.append dummy_wid 
                (Warehouse.AddYTD {w_id = dwid; ytd=h_amt});
    Customer_table.append dummy_cid (Customer.AddBal{c_id=cid; c_w_id=cwid; 
    c_d_id=cdid; c_bal=(-1*h_amt)});
    History_table.append dummy_hid
     (History.Append {h_w_id = dwid; h_d_id = did; 
                      h_c_id = cid; h_c_w_id = cwid; 
                      h_c_d_id = cdid; h_amount = h_amt})
  end

 (*
 * Delivery transaction.
   Assumes the order o being processed here is the minimum order id from the
   new order table to reduce verification complexity.
 *)
(*Txn Consistency: Atomic*)
let do_delivery_txn wid did o =
  let o_effs = Order_table.get dummy_oid Order.Get in
  process_order wid did o o_effs

(*<<<<<<<<<< INVARIANT FUNCTIONS BEGIN >>>>>>>>>>>>>>>>*)

(* D_NEXT_O_ID - 1 = max(O_ID) *)
 let inv11 did wid = 
  let latest_nextoid = get_latest_nextoid did wid in
  let max_oid_order = get_maxoid did wid in
  latest_nextoid = (sum max_oid_order 1)

 (* For any row in the ORDER table, 
    O_OL_CNT must equal the number of rows in the 
    ORDER-LINE table for the corresponding order 
    defined by (O_W_ID, O_D_ID, O_ID) = (OL_W_ID, OL_D_ID, OL_O_ID).*)
 let inv12 oid did wid = 
  let order_ctxt = Order_table.get dummy_oid (Order.Get) in
  let orderline_ctxt = Orderline_table.get dummy_olid (Orderline.Get) in
  let v1 = get_olcnt wid did oid order_ctxt in
  let v2 = List.fold_right (get_ol_rows_cnt oid did wid) orderline_ctxt 0 in
  v1=v2

 let inv_new_order_txn (oid1:int) did1 wid1 =
  inv11 did1 wid1 &&
  inv12 oid1 did1 wid1

 (*W_YTD = sum(H_AMOUNT)*)
 let inv23 (did:District.id) (wid:Warehouse.id) (warehouse_ytd:int) (history_ctxt: History.eff option list) = 
   let v1 = warehouse_ytd in
   let v2 = List.fold_right (get_hamt_wid wid) history_ctxt 0 in
   v1 = v2

 let inv_payment_txn did2 wid2 =
  let warehouse_ytd = get_warehouse_ytd wid2 in
  let history_ctxt = History_table.get dummy_hid (History.Get) in
  inv23 did2 wid2 warehouse_ytd history_ctxt

 (*C_BALANCE = sum(OL_AMOUNT) - sum(H_AMOUNT)*)
 let inv31 did wid cid ol_amt cust_bal history_ctxt =  
  let v1 = List.fold_right (get_hamt_wcdid wid cid did) history_ctxt 0 in
  let v2 = ol_amt in
  let v3 = cust_bal in
  v3=(v2-v1)

 let inv_payment_and_delivery_txn (oid3:int) cid3 wid3 did3 = 
  let orderline_ctxt = Orderline_table.get dummy_olid (Orderline.Get) in
  let order_ctxt = Order_table.get dummy_oid (Order.Get) in
  let cust_bal = get_customer_bal cid3 did3 wid3 in
  let history_ctxt = History_table.get dummy_hid (History.Get) in
  let ol_amt = List.fold_right sum 
                (List.map (get_olamt_cid wid3 did3 
                             cid3 orderline_ctxt) order_ctxt) 0 in
  inv31 did3 wid3 cid3 ol_amt cust_bal history_ctxt

 (*For any row in the ORDER-LINE table, OL_DELIVERY_D is set to a null date/time 
   if and only if the corresponding row in the ORDER table defined by 
   (O_W_ID, O_D_ID, O_ID) = (OL_W_ID, OL_D_ID, OL_O_ID) 
   has O_CARRIER_ID set to a null value.*)
 let inv_delivery_txn wid4 did4 oid4 =
   let order_ctxt = Order_table.get dummy_oid (Order.Get) in
   let orderline_ctxt = Orderline_table.get dummy_olid (Orderline.Get) in
   if List.exists orderline_ctxt (check_delivery_set wid4 did4 oid4) 
   then List.exists order_ctxt (check_carrier_set wid4 did4 oid4) 
   else true
