type d_id = Uuid.t
type w_id = Uuid.t
type c_id = Uuid.t
type i_id = Uuid.t
type o_id = int

type warehouse = {w_id: w_id; mutable w_ytd: int}
type district = {d_id: d_id; d_w_id: w_id; 
                 mutable d_ytd: int; 
                 mutable d_next_o_id: o_id}
type customer = {c_id: c_id; c_d_id: d_id; c_w_id: w_id; 
                 mutable c_bal: int; 
                 mutable c_ytd_payment:int; 
                 mutable c_payment_cnt:int; 
                 mutable c_delivery_cnt:int;}
type order = {o_id:o_id; o_w_id: w_id; o_d_id: d_id; 
              o_c_id: c_id; o_ol_cnt: int; 
              mutable o_carrier_id: unit option}
type new_order= {no_o_id: o_id; no_d_id:d_id; no_w_id: w_id}
type order_line = {ol_o_id: o_id; ol_d_id: d_id; 
                   ol_w_id: w_id; ol_num: int; ol_amt: int; 
                   ol_i_id: i_id; ol_supply_w_id: w_id;
                   ol_qty: int; mutable ol_delivery_d: Unix.tm option}
type hist = {h_c_id: c_id; h_c_d_id: d_id; h_c_w_id: w_id; 
             h_d_id: d_id; h_w_id: w_id; h_amt: int}
type item = {i_id: i_id; i_name: string; i_price: int}
type stock = {s_i_id: i_id; s_w_id: w_id; mutable s_qty: int; 
              mutable s_ytd: int; mutable s_order_cnt: int}

type db = {mutable warehouses: warehouse list; 
           mutable districts: district list; 
           mutable customers: customer list;
           mutable orders: order list;
           mutable order_lines: order_line list;
           mutable hist: hist list;
           mutable new_orders: new_order list; 
           mutable items: item list;
           mutable stock: stock list}

type item_req = {ol_i_id: Uuid.t; ol_supply_w_id: Uuid.t; ol_qty: int}

module L = struct
  include List
  let rec sum l = failwith "Unimpl."
  let rec delete f l = failwith "Unimpl."
end
module U = Unix

exception RollBack

let db = {warehouses = []; districts = []; 
          customers = []; orders = []; 
          order_lines = []; new_orders = []; 
          items = []; hist = []; stock = []}

let find_warehouse w_id = 
  List.find (fun w -> w.w_id = w_id) db.warehouses

let find_dist (d_w_id,d_id) = 
  L.find (fun dist -> dist.d_w_id = d_w_id && 
                      dist.d_id = d_id) db.districts

let find_customer (c_w_id,c_d_id,c_id) =
  List.find (fun c -> c.c_w_id = c_w_id && 
                      c.c_d_id = c_d_id && 
                      c.c_id = c_id) db.customers

let find_item i_id = 
  try L.find (fun i -> i.i_id = i_id) db.items 
  with Not_found -> raise RollBack

let find_stk (s_w_id,s_i_id) = 
  L.find (fun s -> s.s_i_id = s_i_id && 
                   s.s_w_id = s_w_id) db.stock 

let find_order (w_id, d_id, o_id) = 
  L.find (fun o -> o.o_w_id = w_id && 
                   o.o_d_id = d_id && 
                   o.o_id = o_id) db.orders 

(*
 * New Order transaction. 
 *)
let new_order_txn w_id d_w_id d_id c_w_id c_d_id c_id
      (ireqs: item_req list) =
  let dist = find_dist (d_w_id,d_id) in
  let o_id = dist.d_next_o_id in
  let _ = dist.d_next_o_id <- o_id + 1 in
  let ord = {o_id=o_id; o_w_id=w_id; o_d_id=d_id; 
             o_c_id=c_id; o_ol_cnt=L.length ireqs; 
             o_carrier_id = None} in
  let new_ord = {no_o_id=o_id; no_w_id=w_id; no_d_id=d_id} in
    begin
      db.orders <- db.orders@[ord];
      db.new_orders <- db.new_orders@[new_ord];
      L.iteri 
        (fun i ireq -> 
          let stk = find_stk (ireq.ol_supply_w_id, ireq.ol_i_id) in 
          let item = find_item ireq.ol_i_id in 
          let ol = {ol_o_id=o_id; ol_d_id=d_id; ol_w_id=w_id; 
                    ol_num=i; ol_i_id=ireq.ol_i_id; 
                    ol_supply_w_id=ireq.ol_supply_w_id; 
                    ol_amt=item.i_price * ireq.ol_qty;
                    ol_qty=ireq.ol_qty; ol_delivery_d=None} in
            begin
              if stk.s_qty >= ireq.ol_qty + 10 
              then stk.s_qty <- stk.s_qty - ireq.ol_qty
              else stk.s_qty <- stk.s_qty - ireq.ol_qty + 91;
              stk.s_ytd <- stk.s_ytd + ireq.ol_qty;
              stk.s_order_cnt <- stk.s_order_cnt + 1;
              db.order_lines <- db.order_lines @ [ol]
            end) 
        ireqs
    end

(*
 * Payment transaction.
 * Pre: w_id == d_w_id 
 *)
let payment_txn w_id d_id d_w_id c_w_id c_d_id c_id h_amt = 
  let w = find_warehouse w_id in
  let d = find_dist (d_w_id,d_id) in
  let c = find_customer (c_w_id,c_d_id,c_id) in
  let h_item = {h_c_id = c_id; h_c_d_id = c_d_id; h_c_w_id = c_w_id; 
                h_d_id = d_id; h_w_id = w_id; h_amt = h_amt} in
    begin
      w.w_ytd <- w.w_ytd + h_amt;
      d.d_ytd <- d.d_ytd + h_amt;
      c.c_bal <- c.c_bal - h_amt;
      c.c_ytd_payment <- c.c_ytd_payment + h_amt;
      c.c_payment_cnt <- c.c_payment_cnt + 1;
      db.hist <- db.hist @ [h_item]
    end
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
let delivery_txn w_id =
  let dists = L.filter (fun d -> d.d_w_id = w_id) db.districts in
  let oldest_nords = 
    L.map (fun d -> 
             let nords = L.filter 
                           (fun no -> no.no_w_id = w_id && 
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
let stock_level_txn w_id d_w_id d_id thres = 
  let dist = find_dist (d_w_id,d_id) in
  let next_o_id = dist.d_next_o_id in
  let ols = L.filter (fun ol -> ol.ol_w_id = w_id && 
                                ol.ol_d_id = d_id && 
                                ol.ol_o_id < next_o_id && 
                                ol.ol_o_id >= next_o_id - 20) 
              db.order_lines in
  let stks = L.map (fun ol -> (ol.ol_i_id,find_stk (w_id,ol.ol_i_id))) 
               ols in
    stks
