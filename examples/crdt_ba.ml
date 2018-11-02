open Crdts

module BankAccount_Types = struct
  type account = {id:Uuid.t; name:string; mutable bal:CRInt.t}
  type accounts_table =  account CRTable.t
  type ba_db = {accounts_table: accounts_table}
end

open BankAccount_Types

module Account(S:sig
                   val t: accounts_table
                 end) = struct
  open S

  let get_balance (acc_id:Uuid.t) = 
    let b = CRTable.find (fun {bal} -> bal) 
              (fun {id} -> id = acc_id) t in
    match b with | Some x -> CRInt.get x
                 | None -> 0

  let deposit (acc_id:Uuid.t) amt = 
    CRTable.update (fun {bal} -> CRInt.add amt bal)  
      (fun {id} -> id = acc_id) t 

  let withdraw (acc_id:Uuid.t) amt = 
    if get_balance acc_id >= amt then
      begin
        CRTable.update (fun {bal} -> CRInt.add (0-amt) bal)
          (fun {id} -> id = acc_id) t;
        true
      end
    else false
end

module Banking_App(S:sig 
                      val db: ba_db 
                    end) = struct
  module BA = Account(struct 
                       let t = S.db.accounts_table
                      end)
  open BA
  let transfer_txn (acc_id1:Uuid.t) (acc_id2:Uuid.t) amt = 
    let status = withdraw acc_id1 amt in 
    if status then deposit acc_id2 amt else ()
end
