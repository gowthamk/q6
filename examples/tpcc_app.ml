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

  let rec nth l n = 
    match l with 
    | [] -> raise (Failure "empty list")
    | x::xs -> if n=0 then x else nth xs (n-1)

  (*let rec fold_left f b l = match l with
    | [] -> b
    | x::xs -> fold_left f (f b x) xs*)

  let rec fold_right f l b = match l with
    | [] -> b
    | x::xs -> f x (fold_right f xs b)

  let rec iter f l = match l with
    | [] -> ()
    | x::xs -> (f x; iter f xs)

  (*let rec iteri_helper f i l = match l with
    | [] -> ()
    | x::xs -> (f i x; iteri_helper f (i+1) xs)

  let iteri f l = iteri_helper f 0 l*)

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

  let rec exists l f = match l with
    | [] -> false
    | x::xs -> (f x)||(exists xs f)
end

module L =
struct
  let forall l f = true
  let exists l f = true
end

module Warehouse = struct
  type id = Uuid.t
  type eff = GetYTD
    | SetYTD of {w_id:id; ytd: int; ts:int}
end

module Warehouse_table =
struct
  include Store_interface.Make(Warehouse)
end

module District = struct
  type id = Uuid.t
  type eff = GetYTD
    | SetYTD of {d_id: id; d_w_id: Warehouse.id; ytd: int; ts:int}
    (*| GetNextOID of {d_id: id; d_w_id: id; next_o_id: int}*)
    | SetNextOID of {d_id: id; d_w_id: Warehouse.id; next_o_id: int; ts:int}
    | Get
end

module District_table =
struct
  include Store_interface.Make(District)
end

module Customer = struct
  type id = Uuid.t
  type eff = GetBal
    | SetBal of {c_id:id; c_w_id: id; c_d_id: id; c_bal:int; ts:int}
    | GetYTDPayment
    | SetYTDPayment of {c_id:id; c_w_id: id; c_d_id: id; 
                        c_ytd_payment: int; ts:int}
    | GetPaymentCnt
    | SetPaymentCnt of {c_id:id; c_w_id: id; c_d_id: id; 
                        c_payment_cnt: int; ts:int}
    | GetDeliveryCnt
    | SetDeliveryCnt of {c_id:id; c_w_id: id; c_d_id: id; 
                         c_delivery_cnt: int; ts:int}
end

module Customer_table =
struct
  include Store_interface.Make(Customer)
end

module History = struct
  type id = Uuid.t
  type eff = Get
    | Append of {h_w_id: id; h_d_id: id; h_c_id: id; 
                 h_c_w_id: id; h_c_d_id: id; h_amount: int}
end

module DummyModuleForMkkeyString = struct
  type id = string
  type eff = Get
end

module DummyModuleForMkkeyString_table =
struct
  include Store_interface.Make(DummyModuleForMkkeyString)
end

module History_table =
struct
  include Store_interface.Make(History)
end

module Order = struct
  type id = int
  type eff = Get 
    | Add of {o_id: id; o_w_id: Warehouse.id; o_d_id: District.id; o_c_id: Customer.id; o_ol_cnt: int}
end

module Order_table =
struct
  include Store_interface.Make(Order)
end

module Item = struct
  type id = Uuid.t
  type eff = Get
    | Add of {i_id: id; i_name: string; i_price: int}
end

module Item_table =
struct
  include Store_interface.Make(Item)
end

module Stock = struct
  type id = Item.id
  type eff = Get
    (*| Add of {s_i_id: Item.id; s_w_id: Warehouse.id; s_qty: int; 
              s_ytd: int; s_order_cnt: int}*)
    | SetYTDPayment of {s_i_id: Item.id; s_w_id: Warehouse.id; c_ytd_payment: int; ts: int}
    | SetQuantity of {s_i_id: Item.id; s_w_id: Warehouse.id; s_qty: int; ts: int}
    | SetOrderCnt of {s_i_id: Item.id; s_w_id: Warehouse.id; s_order_cnt: int; ts: int}
end

module Stock_table =
struct
  include Store_interface.Make(Stock)
end

module Orderline = struct
  type id = Order.id
  type eff = Get
    | Add of  {ol_o_id: Order.id; ol_d_id: District.id; ol_w_id: Warehouse.id; ol_num: int; ol_amt: int; 
               ol_i_id: Item.id; ol_supply_w_id: Warehouse.id;ol_qty: int}
end

module Orderline_table =
struct
  include Store_interface.Make(Orderline)
end

module DistrictCreate = struct
  type id = Uuid.t
  type eff = DistrictAdd of {d_id: District.id;w_id: Warehouse.id}
            | Get
end

module DistrictCreate_table =
struct
  include Store_interface.Make(DistrictCreate)
end

type item_req = {ol_i_id: Item.id; ol_supply_w_id: Warehouse.id; ol_qty: int}

let is_eff_max_nextoid did dwid ts1 eff1 =
  match eff1 with
  | Some z -> 
    (match z with 
     | District.SetNextOID {d_id=did2; d_w_id=dwid2; next_o_id=nextoid2; ts=ts2} -> 
        if did2 = did && dwid2 = dwid then ts1>=ts2 else true
     | _ -> true)
  | _ -> true

let rec find_nextoid did dwid d_effs deffs =
  match deffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_nextoid did dwid d_effs effs in
    match eff with 
    | Some y -> 
      (match y with 
       | District.SetNextOID {d_id=did1; d_w_id=dwid1; next_o_id=nextoid1; ts=ts1} -> 
          if did1 = did && dwid1 = dwid then
            if List.forall d_effs (is_eff_max_nextoid did dwid ts1)
            then nextoid1 else t
          else t                                                       
       | _ -> t)
    | _ -> t

let get_latest_nextoid did dwid = 
  let d_effs = District_table.get did (District.Get) in
  find_nextoid did dwid d_effs d_effs

let is_eff_max_qty w_id ts1 eff1 = 
  match eff1 with 
  | Some y -> 
    (match y with 
     | Stock.SetQuantity {s_i_id= iid2; s_w_id= wid2; s_qty= qty2; ts=ts2} -> 
        if wid2=w_id then ts1>=ts2 else true
     | _ -> true)
  | _ -> true

let rec find_qty stk_effs stkeffs w_id =
  match stkeffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_qty stk_effs effs w_id in
    match eff with 
    | Some x -> (match x with 
                 | Stock.SetQuantity {s_i_id= iid1; s_w_id= wid1; s_qty= qty1; ts=ts1} -> 
                     if wid1=w_id then
                       if List.forall stk_effs (is_eff_max_qty w_id ts1)
                       then qty1 else t
                     else t
                 | _ -> t)
    | _ -> t

let get_qty ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in
  find_qty stk_effs stk_effs ireq_ol_supply_w_id

let find_price eff acc = 
  match eff with 
  | Some x -> (match x with
              | Item.Add {i_id=id; i_name=name; i_price=price} -> price
              | _ -> acc)
  | _ -> acc

let get_price ireq_ol_i_id =
  let itemEffs = Item_table.get ireq_ol_i_id (Item.Get) in 
  List.fold_right find_price itemEffs (0-1)

let is_eff_max_ytd wid ts1 eff1 = 
  match eff1 with
  | Some y -> (match y with 
    | Stock.SetYTDPayment {s_i_id= iid2; s_w_id= wid2; c_ytd_payment= ytd2;ts=ts2} -> 
      if wid2=wid then ts1>=ts2 else true
    | _ -> true)
  | _ -> true

let rec find_ytd stk_effs stkeffs wid = 
  match stkeffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_ytd stk_effs effs wid in
    match eff with 
    | Some x -> (match x with 
                | Stock.SetYTDPayment {s_i_id= iid1; s_w_id= wid1; c_ytd_payment= ytd1;ts=ts1} -> 
                   if wid1=wid then
                     if List.forall stk_effs (is_eff_max_ytd wid ts1)
                     then ytd1 else t
                   else t
                | _ -> t)
    | _ -> t

let get_ytd ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in
  find_ytd stk_effs stk_effs ireq_ol_supply_w_id

let is_eff_max_cnt wid ts1 eff1 = 
  match eff1 with 
  | Some y -> 
    (match y with 
     | Stock.SetOrderCnt {s_i_id= iid2; s_w_id= wid2; s_order_cnt= cnt2; ts= ts2} -> 
        if wid2=wid then ts1>=ts2 else true
     | _ -> true)
  | _ -> true

let rec find_stkcnt stk_effs stkeffs wid = 
  match stkeffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_stkcnt stk_effs effs wid in
    match eff with 
    | Some x -> (match x with 
              | Stock.SetOrderCnt {s_i_id= iid1; s_w_id= wid1; s_order_cnt= cnt1; ts= ts1} -> 
                 if wid1=wid then
                   if List.forall stk_effs (is_eff_max_cnt wid ts1)
                   then cnt1 else t
                 else t
              | _ -> t)
    | _ -> t

let get_latest_stkcnt ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in
  find_stkcnt stk_effs stk_effs ireq_ol_supply_w_id

let do_new_order_txn (*ireqs_no*) gen_olqty did wid cid dwid gen_oliid gen_olsupplywid = 
  (* TODO: kind of ireqs not found *)
  (*let ireqs = gen_list ireqs_no [] in*)
  let ireqs = [1(*;2;3;4;5*)] in
  let latest_nextoid = get_latest_nextoid did dwid in
  let nextoid = latest_nextoid + 1 in
  let ts1 = 0 (*int_of_float (Unix.time ())*) in
    begin
      District_table.append did (District.SetNextOID 
      {d_id=did; 
       d_w_id=wid; 
       next_o_id=nextoid; 
       ts=ts1});
      (*Is this approach correct??*)
      let dummy_oid = -1 in 
      Order_table.append dummy_oid (Order.Add 
       {o_id=latest_nextoid; o_w_id=wid; o_d_id=did; 
             o_c_id=cid; o_ol_cnt=(List.length ireqs)});
      List.iter 
        (fun ireq -> 
          let ireq_ol_i_id = gen_oliid in
          let ireq_ol_supply_w_id = gen_olsupplywid in
          let ireq_ol_qty = gen_olqty in
          (*let qty = get_qty ireq_ol_i_id ireq_ol_supply_w_id in*)
          let price = get_price ireq_ol_i_id in
            begin
              (*if qty >= ireq_ol_qty + 10 
              then Stock_table.append ireq_ol_i_id (Stock.SetQuantity 
              {s_i_id= ireq_ol_i_id; 
               s_w_id= ireq_ol_supply_w_id; 
               s_qty= qty - ireq_ol_qty; ts=ts1})
              else 
               (*stk.s_qty <- stk.s_qty - ireq_ol_qty + 91;*)
                Stock_table.append ireq_ol_i_id 
                (Stock.SetQuantity {s_i_id= ireq_ol_i_id; 
                 s_w_id= ireq_ol_supply_w_id; 
                 s_qty= (qty-ireq_ol_qty+91); 
                ts=ts1});*)
                (*stk.s_ytd <- stk.s_ytd + ireq_ol_qty;*)
                (*let latest_ytd = get_ytd ireq_ol_i_id ireq_ol_supply_w_id in
                Stock_table.append ireq_ol_i_id 
                (Stock.SetYTDPayment {s_i_id= ireq_ol_i_id; 
                 s_w_id= ireq_ol_supply_w_id; 
                 c_ytd_payment= (latest_ytd + ireq_ol_qty);ts=ts1});*)
                (*stk.s_order_cnt <- stk.s_order_cnt + 1;*)
                (*let latest_cnt = get_latest_stkcnt ireq_ol_i_id ireq_ol_supply_w_id in
                Stock_table.append ireq_ol_i_id 
                (Stock.SetOrderCnt {s_i_id= ireq_ol_i_id; 
                s_w_id= ireq_ol_supply_w_id; 
                s_order_cnt= latest_cnt+1; 
                ts= ts1});*)
                (*db.order_lines <- db.order_lines @ [ol]*)
              Orderline_table.append latest_nextoid (Orderline.Add 
               {ol_o_id=latest_nextoid;
                ol_d_id=did; 
                ol_w_id=wid; 
                ol_num=0; 
                ol_i_id=ireq_ol_i_id; 
                ol_supply_w_id=ireq_ol_supply_w_id; 
                ol_amt=price * ireq_ol_qty;
                ol_qty=ireq_ol_qty})
            end ) ireqs
    end

let is_eff_max_oid did dwid oid1 eff1 = 
  match eff1 with 
  | Some z -> 
    (match z with 
    | Order.Add {o_id=oid2; o_w_id=wid2; o_d_id=did2; o_c_id=cid2; o_ol_cnt=cnt2} -> 
      if did2 = did && wid2 = dwid then oid1>=oid2 else true
    | _ -> true)
  | _ -> true

let rec find_maxoid order_effs ordereffs did dwid = 
  match ordereffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_maxoid order_effs effs did dwid in
    match eff with 
    | Some y -> (match y with 
        | Order.Add {o_id=oid1; o_w_id=wid1; o_d_id=did1; o_c_id=cid1; o_ol_cnt=cnt1} -> 
            if did = did1 && dwid = wid1 then
              if List.forall order_effs (is_eff_max_oid did dwid oid1)
              then oid1 else t
            else t
        | _ -> t)
    | _ -> t

let get_maxoid did dwid =
  let dummy_oid = -1 in
  let order_effs = Order_table.get dummy_oid (Order.Get) in
  find_maxoid order_effs order_effs did dwid

let rec is_eff_max_wtyd dwid ts1 eff1 =
  match eff1 with 
  | Some y -> (match y with 
     | Warehouse.SetYTD {w_id=dwid2; ytd=ytd2; ts=ts2} -> 
        if dwid=dwid2 then ts1>=ts2 else true
     | _ -> true)
  | _ -> true

let rec find_warehouse_ytd dwid whs_effs whseffs =
  match whseffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_warehouse_ytd dwid whs_effs effs in
    match eff with 
    | Some x -> (match x with 
               | Warehouse.SetYTD {w_id=dwid1; ytd=ytd1; ts=ts1} -> 
                  if dwid=dwid1 then
                    if List.forall whs_effs (is_eff_max_wtyd dwid ts1)
                    then ytd1 else t
                  else t
               | _ -> t)
    | _ -> t 

let get_warehouse_ytd dwid =
  let whs_effs = Warehouse_table.get dwid (Warehouse.GetYTD) in
  find_warehouse_ytd dwid whs_effs whs_effs

let is_eff_max_dytd dwid ts1 eff1 =
  match eff1 with 
  | Some y -> (match y with 
             | District.SetYTD {d_id=id2; d_w_id=wid2; ytd=ytd2; ts=ts2} -> 
                if wid2=dwid then ts1>=ts2 else true
             | _ -> true)
  | _ -> true

let rec find_district_ytd dwid d_effs deffs = 
  match deffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_district_ytd dwid d_effs effs in
    match eff with 
    | Some x -> (match x with 
               | District.SetYTD {d_id=id; d_w_id=wid; ytd=ytd1; ts=ts1} -> 
                  if wid=dwid then
                    if List.forall d_effs (is_eff_max_dytd dwid ts1)
                    then ytd1 else t
                  else t
               | _ -> t)
    | _ -> t

let get_district_ytd did dwid =
  let d_effs = District_table.get did (District.GetYTD) in
  find_district_ytd dwid d_effs d_effs

let is_eff_max_cbal cwid ts1 eff1 = 
  match eff1 with 
  | Some y -> (match y with 
             | Customer.SetBal {c_w_id=wid1; ts=ts2;c_bal=bal} -> 
                if wid1=cwid then ts1>=ts2 else true
             | _ -> true)
  | _ -> true

let rec find_customer_bal cdid cwid c_effs ceffs = 
  match ceffs with
  | [] -> -1
  | eff::effs ->  
    let t = find_customer_bal cdid cwid c_effs effs in
    match eff with 
    | Some x -> (match x with 
               | Customer.SetBal {c_d_id=did;c_w_id=wid; ts=ts1;c_bal=bal1} -> 
                  if wid=cwid && did=cdid then
                    if List.forall c_effs (is_eff_max_cbal cwid ts1)
                    then bal1 else t
                  else t
               | _ -> t)
    | _ -> t

let get_customer_bal cid cdid cwid =
  let c_effs = Customer_table.get cid (Customer.GetBal) in
  find_customer_bal cdid cwid c_effs c_effs

let is_eff_max_cytd cwid ts1 eff1 =
  match eff1 with 
  | Some y -> (match y with 
    | Customer.SetYTDPayment {c_w_id=wid1; c_ytd_payment=ytd1;ts=ts2} -> 
        if wid1=cwid then ts1>=ts2 else true
    | _ -> true)
  | _ -> true

let rec find_customer_ytd cwid c_effs ceffs = 
  match ceffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_customer_ytd cwid c_effs effs in
    match eff with 
     | Some x -> (match x with 
                | Customer.SetYTDPayment {c_w_id=wid; ts=ts1; c_ytd_payment=ytd1} -> 
                   if wid=cwid then
                     if List.forall c_effs (is_eff_max_cytd cwid ts1)
                     then ytd1 else t
                   else t
                | _ -> t)
     | _ -> t

let get_customer_ytd cid cwid = 
  let c_effs = Customer_table.get cid (Customer.GetYTDPayment) in
  find_customer_ytd cwid c_effs c_effs

let is_eff_max_pycnt cwid ts1 eff1 = 
  match eff1 with 
  | Some y -> (match y with 
     | Customer.SetPaymentCnt {c_w_id=wid1; c_payment_cnt=cnt1;ts=ts2} -> 
          if wid1=cwid then ts1>=ts2 else true
     | _ -> true)
  | _ -> true

let rec find_customer_pycnt cwid c_effs ceffs = 
  match ceffs with
  | [] -> -1
  | eff::effs -> 
    let t = find_customer_pycnt cwid c_effs effs in
    match eff with 
    | Some x -> (match x with 
               | Customer.SetPaymentCnt {c_w_id=wid; ts=ts1; c_payment_cnt=cnt} -> 
                  if wid=cwid then 
                    if List.forall c_effs (is_eff_max_pycnt cwid ts1)
                    then cnt else t
                  else t
               | _ -> t)
    | _ -> t

let get_customer_pycnt cid cwid = 
  let c_effs = Customer_table.get cid (Customer.GetPaymentCnt) in
  find_customer_pycnt cwid c_effs c_effs
  
let do_payment_txn dummy_id_DistrictCreate dummy_id_History h_amt did dwid cdid cwid cid =
  let ts1 = 0 in
  begin
    DistrictCreate_table.append dummy_id_DistrictCreate 
    (DistrictCreate.DistrictAdd {d_id=did;w_id=dwid});
    let w_ytd = get_warehouse_ytd dwid in
    Warehouse_table.append dwid (Warehouse.SetYTD {w_id = dwid; ytd=w_ytd+h_amt; ts=ts1});
    let d_ytd = get_district_ytd did dwid in
    District_table.append did (District.SetYTD {d_id=did; d_w_id=dwid; 
    ytd=d_ytd+h_amt; ts=ts1});
    let c_bal = get_customer_bal cid cdid cwid in
    Customer_table.append cid (Customer.SetBal{c_id=cid; c_w_id=cwid; 
    c_d_id=cdid; c_bal=c_bal-h_amt; ts=ts1});
    (*let c_ytd = get_customer_ytd cid cwid in*)
    Customer_table.append cid (Customer.SetYTDPayment{c_id=cid; c_w_id=cwid; 
    c_d_id=cdid; c_ytd_payment=h_amt; ts=ts1});
    (*let c_pycnt = get_customer_pycnt cid cwid in
    Customer_table.append cid (Customer.SetPaymentCnt{c_id=cid; c_w_id=cwid; 
    c_d_id=cdid; c_payment_cnt=c_pycnt+1; ts=ts1});*)
    History_table.append dummy_id_History 
     (History.Append {h_w_id = dwid; h_d_id = did; 
                      h_c_id = cid; h_c_w_id = cwid; 
                      h_c_d_id = cdid; h_amount = h_amt})
  end

 let get_did eff = 
   match eff with
   | Some x -> (match x with 
               | DistrictCreate.DistrictAdd {d_id=id1} -> Some id1
               | _ -> None)
   | _ -> None

 let get_dytd wid id = 
   match id with
   | Some x -> get_district_ytd x wid 
   | _ -> 0

 let get_hamt wid did eff = 
   match eff with
   | Some x -> (match x with
                | History.Append {h_w_id = hdwid; h_d_id = hdid; h_amount = h_amt} -> 
                  if hdwid=wid && hdid=did then h_amt else 0
                | _ -> 0)
   | _ -> 0

 let get_hamt_sum wid eff acc = 
   match eff with
   | Some x -> (match x with
                | History.Append {h_w_id = hdwid; h_d_id = hdid; h_amount = h_amt} -> 
                  if hdwid=wid then acc+h_amt else acc
                | _ -> acc)
   | _ -> acc

 let get_olamt wid did oid eff = 
   match eff with
   | Some x -> (match x with
               | Orderline.Add {ol_o_id= oid1; ol_d_id=did1; ol_w_id=wid1; ol_amt=amt} -> 
                 if (wid1=wid && did1=did && oid1=oid) then amt else 0
               | _ -> 0)
   | _ -> 0

 let get_ocnt wid did oid eff = 
   match eff with
   | Some x -> (match x with
               | Order.Add {o_w_id=wid1; o_d_id=did1; o_ol_cnt=cnt; o_id=oid1} -> 
                 if (wid1=wid && did1=did && oid1=oid) then cnt else 0
               | _ -> 0)
   | _ -> 0

 let get_hamt_wcid wid did cid eff = 
   match eff with
   | Some x -> (match x with
                | History.Append {h_w_id = hdwid; h_d_id = hdid; h_c_id = hcid; h_amount = h_amt} -> 
                  if (hdwid=wid && hdid=did && hcid=cid) then h_amt else 0
                | _ -> 0)
   | _ -> 0

 let get_ol_rows_cnt did wid eff acc = 
   match eff with 
   | Some x -> (match x with
                | Orderline.Add {ol_d_id=did1; ol_w_id=wid1} -> 
                  if did = did1 && wid = wid1 then acc+1 else acc
                | _ -> acc)
   | _ -> acc

 (*
 * Delivery transaction.
 *)
let delivery_txn dummy_id_DistrictCreate wid =
  (*let dists = L.filter (fun d -> d.d_w_id = wid) db.districts in*)
  let ctxt = DistrictCreate_table.get dummy_id_DistrictCreate DistrictCreate.Get in
  let dists = List.map (fun eff -> match eff with
                                   | DistrictCreate.Add {d_id=id; w_id=id1} -> 
                                     if id1=wid then Some id else None
                                   | _ -> None) ctxt in
  let oldest_nords = 
    List.map (fun d -> 
             match d with
             | Some did ->
               let nords = L.filter 
                             (fun no -> no.no_w_id = wid && 
                                        no.no_d_id = did) 
                             db.new_orders in
                 (* sort new_orders in increasing order *)
                 match L.sort (fun no1 no2 -> no1.no_o_id - no2.no_o_id) 
                         nords with 
                   | [] -> (d.d_id, None) 
                   | no::_ -> 
                       let o = find_order (w_id, d.d_id, no.no_o_id) in
                       let ols = L.filter 
                                   (fun ol -> ol.ol_w_id = o.o_w_id && 
                                              ol.ol_d_id = o.o_d_id && 
                                              ol.ol_o_id = o.o_id)
                                   db.order_lines in
                       let amt = L.sum @@ L.map (fun ol -> ol.ol_amt) ols in
                       let c = find_customer (w_id, d.d_id, o.o_c_id) in
                        (d.d_id, Some (no,o,ols,amt,c)
             | _ -> )) dists in
    List.iter 
      (function (d_id, None) -> () 
         | (d_id, Some (no,o,ols,amt,c)) -> 
              begin
                db.new_orders <- 
                  L.delete (fun no' -> no'.no_w_id = no.no_w_id && 
                                       no'.no_d_id = no.no_d_id) 
                    db.new_orders;
                o.o_carrier_id <- Some ();
                List.iter (fun ol -> 
                  ol.ol_delivery_d <- Some (U.gmtime @@ U.time ())) ols;
                c.c_bal <- c.c_bal + amt;
                c.c_delivery_cnt <- c.c_delivery_cnt + 1;
              end) 
      oldest_nords

 let inv_new_order_txn oid did wid =
   (* D_NEXT_O_ID - 1 = max(O_ID) *)
   (let latest_nextoid = get_latest_nextoid did wid in
   let max_oid_order = get_maxoid did wid in
   latest_nextoid = (max_oid_order+1)) &&

   (* For any row in the ORDER table, 
     O_OL_CNT must equal the number of rows in the ORDER-LINE table for the corresponding order 
     defined by (O_W_ID, O_D_ID, O_ID) = (OL_W_ID, OL_D_ID, OL_O_ID).*)
   let dummy_oid = -1 in
   let orderline_ctxt = Orderline_table.get oid (Orderline.Get) in
   (let v1 = (let ctxt = Order_table.get dummy_oid (Order.Get) in
              let ord_cnts = List.map (get_ocnt wid did oid) ctxt in
              List.fold_right (+) ord_cnts 0) in
    let v2 = List.fold_right (get_ol_rows_cnt did wid) orderline_ctxt 0 in
    v1=v2)

 let inv_payment_txn dummy_id_DistrictCreate dummy_id_History oid did wid cid =
  let history_ctxt = History_table.get dummy_id_History (History.Get) in

  (* W_YTD = sum(D_YTD) *)
  ( let ctxt = DistrictCreate_table.get dummy_id_DistrictCreate DistrictCreate.Get in
    let district_ids = List.map (fun eff -> match eff with
                                          | Some x -> (match x with 
                                                      | DistrictCreate.DistrictAdd {id=id1} -> Some id1
                                                      | _ -> None)
                                          | _ -> None) ctxt in
    let district_ytds = List.map (fun id -> match id with
                                           | Some x -> get_district_ytd x wid 
                                           | _ -> 0) district_ids in
    let v1 = List.fold_right (fun ytd acc -> ytd+acc) district_ytds 0 in
    let v2 = get_warehouse_ytd wid in
  v1=v2) &&

  (*D_YTD = sum(H_AMOUNT) *)
  (let v1 = get_district_ytd did wid in
   let amts_list = List.map (get_hamt wid did) history_ctxt in
   let v2 = (List.fold_right (+) amts_list 0) in
   v1 = v2) &&
  
  (* W_YTD = sum(H_AMOUNT) *)
  (let v1 = get_warehouse_ytd wid in
   let v2 = (List.fold_right (get_hamt_sum wid) history_ctxt 0) in
   v1 = v2) &&

  let orderline_ctxt = Orderline_table.get oid (Orderline.Get) in
  let cust_bal = get_customer_bal cid did wid in
  let orderline_amts = List.map (get_olamt wid did oid) orderline_ctxt in
  let orderline_amt = List.fold_right (+) orderline_amts 0 in

  (*C_BALANCE = sum(OL_AMOUNT) - sum(H_AMOUNT)*) 
  (let v1 = (let amts_list = List.map (get_hamt_wcid wid did cid) history_ctxt in
              List.fold_right (+) amts_list 0) in
   let v2 = orderline_amt in
   let v3 = cust_bal in
    v3=(v2-v1)) &&

  (*C_BALANCE + C_YTD_PAYMENT = sum(OL_AMOUNT)*)
  (let v1 = get_customer_ytd cid wid in
   let v2 = cust_bal in
   let v3 = orderline_amt in 
    v3 = (v1+v2))

(*
(*
 * Order Status transaction.
 *)
let order_status_txn c_w_id c_d_id c_id = 
  let c = find_customer (c_w_id,c_d_id,c_id) in
  let ords = L.filter (fun o -> o.o_w_id = c_w_id && 
                                o.o_d_id = c_d_id && 
                                o.o_c_id = c_id) db.orders in
  (* sort ords in decreasing order *)
  let o = L.hd @@ L.sort (fun o1 o2 -> o2.o_id - o1.o_id) ords in
  let ols = L.filter (fun ol -> ol.ol_w_id = o.o_w_id && 
                                ol.ol_d_id = o.o_d_id && 
                                ol.ol_o_id = o.o_id) db.order_lines in
  let o_info = L.map (fun (ol:order_line) -> 
                        (ol.ol_qty, ol.ol_delivery_d)) ols in
    (c.c_bal,o_info)

(*
 * Stock-level transaction.
 *)
let stock_level_txn Warehouse.id d_w_id d_id thres = 
  let dist = find_dist (d_w_id,d_id) in
  let next_o_id = dist.d_next_o_id in
  let ols = L.filter (fun ol -> ol.ol_w_id = Warehouse.id && 
                                ol.ol_d_id = d_id && 
                                ol.ol_o_id < next_o_id && 
                                ol.ol_o_id >= next_o_id - 20) 
              db.order_lines in
  let stks = L.map (fun ol -> (ol.ol_i_id,find_stk (w_id,ol.ol_i_id))) 
               ols in
    stks*)