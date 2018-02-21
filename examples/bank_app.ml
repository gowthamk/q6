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

module BA =
struct
  type id = Uuid.t
  type eff = Deposit of {amt:int}
    | Withdraw of {amt:int}
    | GetBalance
end

module BA_table =
struct
  include Store_interface.Make(BA)
end

let compute_bal eff = 
  match eff with 
 | Some e -> (match e with 
                | BA.Withdraw {amt=a} -> 0-a
                | BA.Deposit {amt=a} -> a
                | _ -> 0)
 | None -> 0

let add_bals b acc = b + acc

let get_balance acc_id = 
  let ctxt = BA_table.get acc_id (BA.GetBalance) in
  let bals = List.map compute_bal ctxt in
  let bal = List.fold_right add_bals bals 0 in
    bal

let do_withdraw acc_id a = 
  let cur_bal = get_balance acc_id in
    if (cur_bal >= a) then
      (BA_table.append acc_id (BA.Withdraw {amt=a}); true)
    else false

let inv_fun acc_id' = 
  let bal = get_balance acc_id' in
    bal >= 0