open Q6_interface

module Warehouse = struct
  type id = Uuid.t
  type eff = GetYTD of {w_id: id}
    | SetYTD of {w_id:id; ytd: int; ts:int;}
end

module District = struct
  type id = Uuid.t
  type eff = GetYTD of {d_id: id; d_w_id: id}
    | SetYTD of {d_id: id; d_w_id: id; ytd: int; ts:int}
    | GetNextOID of {d_id: id; d_w_id: id; next_o_id: int}
    | SetNextOID of {d_id: id; d_w_id: id; next_o_id: int; ts:int}
end

module Customer = struct
  type id = Uuid.t
  type eff = GetBal of {c_id:id; c_w_id: id; c_d_id: id}
    | SetBal of {c_id:id; c_w_id: id; c_d_id: id; c_bal:int; ts:int}
    | GetYTDPayment of {c_id:id; c_w_id: id; c_d_id: id}
    | SetYTDPayment of {c_id:id; c_w_id: id; c_d_id: id; 
                        c_ytd_payment: int; ts:int}
    | GetPaymentCnt of {c_id:id; c_w_id: id; c_d_id: id}
    | SetPaymentCnt of {c_id:id; c_w_id: id; c_d_id: id; 
                        c_payment_cnt: int; ts:int}
    | GetDeliveryCnt of {c_id:id; c_w_id: id; c_d_id: id}
    | SetDeliveryCnt of {c_id:id; c_w_id: id; c_d_id: id; 
                         c_delivery_cnt: int; ts:int}
end

module History = struct
  type id = Uuid.t
  type eff = Get
    | Append of {h_w_id: id; h_d_id: id; h_c_id: id; 
                 h_c_w_id: id; h_c_d_id: id; h_amount: int}
end

module Order = struct
  type id = int
  type eff = Get 
    | Add of {o_w_id: Uuid.t; o_d_id: Uuid.t; o_c_id: Uuid.t; o_ol_cnt: int;}
end
