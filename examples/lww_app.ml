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

  let rec contains l x = match l with
    | [] -> false
    | y::ys -> if y=x then true else contains ys x

  (*let len l =
    let rec len_helper l len1 = 
      match l with 
      | [] -> len1
      | x::xs -> len_helper xs (len1+1) in
    len_helper l 0*)

  let rec exists l f = match l with
    | [] -> false
    | x::xs -> (f x)||(exists xs f)
end

module LWWRegister = 
struct
  type id = Uuid.t
  type eff = HARead
             | WriteReg of {value:int;ts:int}
             | HAWrite of {value:int}
             | CAUWrite of {value:int}
             | CAURead
             | STWrite of {value:int}
             | STRead
end

module LWWRegister_table =
struct
  include Store_interface.Make(LWWRegister)
end

let do_write rid v curr_ts =
  LWWRegister_table.append rid (LWWRegister.WriteReg{value=v;ts=curr_ts})

let is_gte ts tsop' = match tsop' with 
 | Some ts' -> ts' <= ts 
 | None -> true

let get_ts eff = 
  match eff with
  | Some x -> (match x with 
              | LWWRegister.WriteReg{value=v; ts=ts1} -> Some ts1
              | _ -> None)
  | _ -> None

let is_max_ts rid ts1 =
  let ctxt = LWWRegister_table.get rid (LWWRegister.HARead) in
  let ts_list = List.map get_ts ctxt in
  List.forall ts_list (is_gte ts1)

let is_true x = (x=true)

let rec cnt_writes eff_list cnt =
  match eff_list with
  | [] -> cnt
  | eff::effs -> (match eff with
                | Some x -> 
                  (match x with
                  | LWWRegister.WriteReg{value=v; ts=ts1} -> cnt_writes effs (cnt+1)
                  | _ -> cnt_writes effs cnt)
                | _ -> cnt_writes effs cnt)

let inv_write rid = 
  let st_read_effs = LWWRegister_table.get rid (LWWRegister.STRead) in
  let cau_read_effs = LWWRegister_table.get rid (LWWRegister.CAURead) in
  (cnt_writes cau_read_effs 0) <= (cnt_writes st_read_effs 0)
  (*let bool_list = List.map (List.contains st_read_effs) cau_read_effs in
    List.forall bool_list is_true)*)