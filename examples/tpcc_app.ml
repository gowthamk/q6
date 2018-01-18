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

  let rec fold_left f b l = match l with
    | [] -> b
    | x::xs -> fold_left f (f b x) xs

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

module IdByTable = struct
  type id = Uuid.t
  type eff = DistrictAdd of {id: Uuid.t}
            | Get
end

module IdByTable_table =
struct
  include Store_interface.Make(IdByTable)
end

type item_req = {ol_i_id: Item.id; ol_supply_w_id: Warehouse.id; ol_qty: int}

let get_latest_nextoid did dwid = 
  let d_effs = District_table.get did (District.Get) in
  let last_ts = List.fold_right (fun eff acc -> match eff with 
                    | Some y -> (match y with 
                                  | District.SetNextOID {d_id=did2; d_w_id=dwid2; next_o_id=nextoid2; ts=ts2} -> if dwid2=dwid && ts2>acc then ts2 else acc                                                       
                                  | _ -> acc)
                    | _ -> acc) d_effs 0 in
  List.fold_right (fun eff acc -> match eff with 
                    | Some y -> (match y with 
                                  | District.SetNextOID {d_id=did2; d_w_id=dwid2; next_o_id=nextoid2; ts=ts2} -> if dwid2=dwid && ts2=last_ts then nextoid2 else acc                                                       
                                  | _ -> acc)
                    | _ -> acc) d_effs 0

let get_dummy_hid x = Uuid.create()

let get_qty ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in 
  let latest_stk_ts = List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                              | Stock.SetQuantity {s_i_id= iid2; s_w_id= wid2; s_qty= qty2; ts=ts2} -> if wid2=ireq_ol_supply_w_id && ts2>acc then ts2 else acc
                              | _ -> acc)
                  | _ -> acc) stk_effs (0-1) in
  List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                              | Stock.SetQuantity {s_i_id= iid2; s_w_id= wid2; s_qty= qty2; ts=ts2} -> if wid2=ireq_ol_supply_w_id && ts2=latest_stk_ts then qty2 else acc
                              | _ -> acc)
                  | _ -> acc) stk_effs 0

let get_price ireq_ol_i_id =
  let itemEffs = Item_table.get ireq_ol_i_id (Item.Get) in 
  List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with
                                | Item.Add {i_id=id; i_name=name; i_price=price} -> price
                                | _ -> acc)
                    | _ -> acc) itemEffs 0

let get_ytd ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in
  let latest_stkytd_ts = List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                               | Stock.SetYTDPayment {s_i_id= iid2; s_w_id= wid2; c_ytd_payment= ytd2;ts=ts2} -> if wid2=ireq_ol_supply_w_id && ts2>acc then ts2 else acc
                               | _ -> acc)
                   | _ -> acc) stk_effs (0-1) in
  List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                               | Stock.SetYTDPayment {s_i_id= iid2; s_w_id= wid2; c_ytd_payment= ytd2;ts=ts2} -> if wid2=ireq_ol_supply_w_id && ts2=latest_stkytd_ts then ytd2 else acc
                               | _ -> acc)
                   | _ -> acc) stk_effs 0

let get_latest_stkcnt ireq_ol_i_id ireq_ol_supply_w_id =
  let stk_effs = Stock_table.get ireq_ol_i_id (Stock.Get) in 
  let latest_stkcnt_ts = List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                               | Stock.SetOrderCnt {s_i_id= iid2; s_w_id= wid2; s_order_cnt= cnt2; ts= ts2} -> if wid2=ireq_ol_supply_w_id && ts2>acc then ts2 else acc
                               | _ -> acc)
                    | _ -> acc) stk_effs (0-1) in
  List.fold_right (fun eff acc -> match eff with 
                    | Some x -> (match x with 
                               | Stock.SetOrderCnt {s_i_id= iid2; s_w_id= wid2; s_order_cnt= cnt2; ts= ts2} -> if wid2=ireq_ol_supply_w_id && ts2=latest_stkcnt_ts then cnt2 else acc
                               | _ -> acc)
                    | _ -> acc) stk_effs 0

(*TODO: Only functions with upto two arguments are supported*)
let do_new_order_txn gen_olqty did wid cid dwid gen_oliid gen_olsupplywid = 
  (* TODO: kind of ireqs not found *)
  let ireqs = [1;2;3;4;5] in
  let d_effs = District_table.get did (District.Get) in 
  let latest_nextoid = get_latest_nextoid did dwid in
  let nextoid = latest_nextoid + 1 in
  let ts = 0 (*int_of_float (Unix.time ())*) in
    begin
      District_table.append did (District.SetNextOID {d_id=did; d_w_id=wid; next_o_id=nextoid; ts=ts});
      (*Is this approach correct??*)
      let dummy_oid = -1 in 
      Order_table.append dummy_oid(*latest_nextoid*) (Order.Add {o_id=latest_nextoid; o_w_id=wid; o_d_id=did; 
             o_c_id=cid; o_ol_cnt=(List.length ireqs)});
      List.iter 
        (fun ireq -> 
          let ireq_ol_i_id = gen_oliid in
          let ireq_ol_supply_w_id = gen_olsupplywid in
          let ireq_ol_qty = gen_olqty in
          let qty = get_qty ireq_ol_i_id ireq_ol_supply_w_id in
          let price = get_price ireq_ol_i_id in
            begin
              if qty >= ireq_ol_qty + 10 
              then Stock_table.append ireq_ol_i_id (Stock.SetQuantity {s_i_id= ireq_ol_i_id; s_w_id= ireq_ol_supply_w_id; s_qty= qty - ireq_ol_qty; ts=ts})
              else 
                (*stk.s_qty <- stk.s_qty - ireq_ol_qty + 91;*)
                Stock_table.append ireq_ol_i_id (Stock.SetQuantity {s_i_id= ireq_ol_i_id; s_w_id= ireq_ol_supply_w_id; s_qty= (qty-ireq_ol_qty+91); ts=ts});
                (*stk.s_ytd <- stk.s_ytd + ireq_ol_qty;*)
                let latest_ytd = get_ytd ireq_ol_i_id ireq_ol_supply_w_id in
                Stock_table.append ireq_ol_i_id (Stock.SetYTDPayment {s_i_id= ireq_ol_i_id; s_w_id= ireq_ol_supply_w_id; c_ytd_payment= (latest_ytd + ireq_ol_qty);ts=ts});
                (*stk.s_order_cnt <- stk.s_order_cnt + 1;*)
                let latest_cnt = get_latest_stkcnt ireq_ol_i_id ireq_ol_supply_w_id in
                Stock_table.append ireq_ol_i_id (Stock.SetOrderCnt {s_i_id= ireq_ol_i_id; s_w_id= ireq_ol_supply_w_id; s_order_cnt= latest_cnt+1; ts= ts});
                (*db.order_lines <- db.order_lines @ [ol]*)
                Orderline_table.append latest_nextoid (Orderline.Add {ol_o_id=latest_nextoid; ol_d_id=did; ol_w_id=wid; 
                      ol_num=0; ol_i_id=ireq_ol_i_id; 
                      ol_supply_w_id=ireq_ol_supply_w_id; 
                      ol_amt=price * ireq_ol_qty;
                      ol_qty=ireq_ol_qty})
               end ) ireqs
    end

let get_maxoid did dwid =
  let dummy_oid = -1 in
  let order_effs = Order_table.get dummy_oid (Order.Get) in
  List.fold_right (fun eff acc -> match eff with 
                    | Some y -> (match y with 
                        | Order.Add {o_id=oid1; o_w_id=wid1; o_d_id=did1; o_c_id=cid1; o_ol_cnt=cnt1} -> 
                            if (did = did1 && dwid = wid1 && oid1 > acc) then oid1 else acc
                        | _ -> acc)
                    | _ -> acc) order_effs 0

  let get_warehouse_ytd dwid =
    let whs_effs = Warehouse_table.get dwid (Warehouse.GetYTD) in
    let latest_whs_ts = List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Warehouse.SetYTD {w_id=dwid1; ytd=ytd1; ts=ts1} -> if dwid=dwid1 && ts1>acc then ts1 else acc
                                 | _ -> acc)
                      | _ -> acc) whs_effs (0-1) in
    List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Warehouse.SetYTD {w_id=dwid1; ytd=ytd1; ts=ts1} -> if ts1=latest_whs_ts then ytd1 else acc
                                 | _ -> acc)
                     | _ -> acc) whs_effs 0

  let get_district_ytd did dwid =
    let d_effs = District_table.get did (District.GetYTD) in
    let latest_d_ts = List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | District.SetYTD {d_id=id; d_w_id=wid; ytd=ytd1; ts=ts1} -> if wid=dwid && ts1>acc then ts1 else acc
                                 | _ -> acc)
                      | _ -> acc) d_effs (0-1) in
    List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | District.SetYTD {d_id=id; d_w_id=wid; ytd=ytd1; ts=ts1} -> if wid=dwid && ts1=latest_d_ts then ytd1 else acc
                                 | _ -> acc)
                     | _ -> acc) d_effs 0

  let get_customer_bal cid cwid =
    let c_effs = Customer_table.get cid (Customer.GetBal) in
    let latest_c_ts = List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetBal {c_w_id=wid; ts=ts1} -> if (wid=cwid && ts1>acc) then ts1 else acc
                                 | _ -> acc)
                      | _ -> acc) c_effs (0-1) in
    List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetBal {c_w_id=wid; ts=ts1;c_bal=bal} -> if (wid=cwid && ts1=latest_c_ts) then bal else acc
                                 | _ -> acc)
                     | _ -> acc) c_effs 0

  let get_customer_ytd cid cwid = 
    let c_effs = Customer_table.get cid (Customer.GetYTDPayment) in
    let latest_c_ts = List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetYTDPayment {c_w_id=wid; ts=ts1} -> if (wid=cwid && ts1>acc) then ts1 else acc
                                 | _ -> acc)
                      | _ -> acc) c_effs (0-1) in
    List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetYTDPayment {c_w_id=wid; c_ytd_payment=ytd;ts=ts1} -> if (wid=cwid && ts1=latest_c_ts) then ytd else acc
                                 | _ -> acc)
                     | _ -> acc) c_effs 0

  let get_customer_pycnt cid cwid = 
    let c_effs = Customer_table.get cid (Customer.GetPaymentCnt) in
    let latest_c_ts = List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetPaymentCnt {c_w_id=wid; ts=ts1} -> if (wid=cwid && ts1>acc) then ts1 else acc
                                 | _ -> acc)
                      | _ -> acc) c_effs (0-1) in
    List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with 
                                 | Customer.SetPaymentCnt {c_w_id=wid; c_payment_cnt=cnt;ts=ts1} -> if (wid=cwid && ts1=latest_c_ts) then cnt else acc
                                 | _ -> acc)
                     | _ -> acc) c_effs 0
  
  let do_payment_txn h_amt did dwid cdid cwid cid =
    let ts1 = 0 in
    let dummy_hid = Uuid.create() in
    begin
      IdByTable_table.append (Uuid.create()) (IdByTable.DistrictAdd {id=did});
      let w_ytd = get_warehouse_ytd dwid in
      Warehouse_table.append dwid (Warehouse.SetYTD {w_id = dwid; ytd=w_ytd+h_amt; ts=ts1});
      let d_ytd = get_district_ytd did dwid in
      District_table.append did (District.SetYTD {d_id=did; d_w_id=dwid; ytd=d_ytd+h_amt; ts=ts1});
      let c_bal = get_customer_bal cid cwid in
      Customer_table.append cid (Customer.SetBal{c_id=cid; c_w_id=cwid; c_d_id=cdid; c_bal=c_bal-h_amt; ts=ts1});
      let c_ytd = get_customer_ytd cid cwid in
      Customer_table.append cid (Customer.SetYTDPayment{c_id=cid; c_w_id=cwid; c_d_id=cdid; c_ytd_payment=h_amt; ts=ts1});
      let c_pycnt = get_customer_pycnt cid cwid in
      Customer_table.append cid (Customer.SetPaymentCnt{c_id=cid; c_w_id=cwid; c_d_id=cdid; c_payment_cnt=c_pycnt+1; ts=ts1});
      History_table.append dummy_hid (History.Append {h_w_id = dwid; h_d_id = did; h_c_id = cid; h_c_w_id = cwid; h_c_d_id = cdid; h_amount = h_amt})
    end

 let inv_fun oid did wid cid =
  (* W_YTD = sum(D_YTD) *)
  (*( let ctxt = IdByTable_table.get (Uuid.create()) IdByTable.Get in
    let district_ids = List.map (fun eff -> match eff with
                                          | Some x -> (match x with 
                                                      | IdByTable.DistrictAdd {id=id1} -> Some id1
                                                      | _ -> None)
                                          | _ -> None) ctxt in
    let district_ytds = List.map (fun id -> match id with
                                           | Some x -> get_district_ytd x wid 
                                           | _ -> 0) district_ids in
    let v1 = List.fold_right (fun ytd acc -> ytd+acc) district_ytds 0 in
    let v2 = get_warehouse_ytd wid in
  v1=v2) &&*)

  (* D_NEXT_O_ID - 1 = max(O_ID) *)
  (let latest_nextoid = get_latest_nextoid did wid in
  let max_oid_order = get_maxoid did wid in
  latest_nextoid = (max_oid_order+1)) &&
  
  let dummy_hid = Uuid.create() in
  let history_ctxt = History_table.get dummy_hid (History.Get) in

  (*D_YTD = sum(H_AMOUNT) *)
  (*(let v1 = get_district_ytd did wid in
   let amts_list = List.map (fun eff -> match eff with
                                 | Some x -> (match x with
                                              | History.Append {h_w_id = hdwid; h_d_id = hdid; h_amount = h_amt} -> if hdwid=wid && hdid=did then h_amt else 0
                                              | _ -> 0)
                                 | _ -> 0) history_ctxt in
   let v2 = (List.fold_right (fun amt acc -> amt+acc) amts_list 0) in
   v1 = v2) &&
  
  (* W_YTD = sum(H_AMOUNT) *)
  (let v1 = get_warehouse_ytd wid in
   let v2 = (List.fold_right (fun eff acc -> match eff with
                                 | Some x -> (match x with
                                              | History.Append {h_w_id = hdwid; h_d_id = hdid; h_amount = h_amt} -> if hdwid=wid then acc+h_amt else acc
                                              | _ -> acc)
                                 | _ -> acc) history_ctxt 0) in
   v1 = v2) &&*)

  let orderline_ctxt = Orderline_table.get oid (Orderline.Get) in
  let dummy_oid = -1 in
  let cust_bal = get_customer_bal cid wid in
  let orderline_amts = List.map (fun eff -> match eff with
                                  | Some x -> (match x with
                                              | Orderline.Add {ol_o_id= oid1; ol_d_id=did1; ol_w_id=wid1; ol_amt=amt} -> if (wid1=wid && did1=did && oid1=oid) then amt else 0
                                              | _ -> 0)
                                  | _ -> 0) orderline_ctxt in
  let orderline_amt = List.fold_right (fun amt acc -> amt+acc) orderline_amts 0 in

  (* For any row in the ORDER table, 
     O_OL_CNT must equal the number of rows in the ORDER-LINE table for the corresponding order 
     defined by (O_W_ID, O_D_ID, O_ID) = (OL_W_ID, OL_D_ID, OL_O_ID). 
    AND
     sum(O_OL_CNT) = [number of rows in the ORDER-LINE table for this district] *)
  (let v1 = (let ctxt = Order_table.get dummy_oid (Order.Get) in
             let ord_cnts = List.map (fun eff -> match eff with
                                  | Some x -> (match x with
                                              | Order.Add {o_w_id=wid1; o_d_id=did1; o_ol_cnt=cnt; o_id=oid1} -> if (wid1=wid && did1=did && oid1=oid) then cnt else 0
                                              | _ -> 0)
                                  | _ -> 0) ctxt in
             List.fold_right (fun cnt acc -> cnt+acc) ord_cnts 0) in
   let v2 = List.length orderline_ctxt in
   v1=v2) &&

  (*C_BALANCE = sum(OL_AMOUNT) - sum(H_AMOUNT)*) 
  (let v1 = (let amts_list = List.map (fun eff -> match eff with
                                 | Some x -> (match x with
                                              | History.Append {h_w_id = hdwid; h_d_id = hdid; h_c_id = hcid; h_amount = h_amt} -> if (hdwid=wid && hdid=did && hcid=cid) then h_amt else 0
                                              | _ -> 0)
                                 | _ -> 0) history_ctxt in
              List.fold_right (fun amt acc -> amt+acc) amts_list 0) in
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
 * Delivery transaction.
 *)
let delivery_txn Warehouse.id =
  let dists = L.filter (fun d -> d.d_w_id = Warehouse.id) db.districts in
  let oldest_nords = 
    L.map (fun d -> 
             let nords = L.filter 
                           (fun no -> no.no_w_id = Warehouse.id && 
                                      no.no_d_id = d.d_id) 
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
                      (d.d_id, Some (no,o,ols,amt,c))) dists in
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