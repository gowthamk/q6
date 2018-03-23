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
  type eff = ShowItem
            | AddToStock of {qty: int}
            | RemoveFromStock of {qty: int}
end

module Item_table =
struct
  include Store_interface.Make(Item)
end

module Cart = 
struct
  type id = Uuid.t
  type eff = AddCart
            | RemoveCart
            | AddItemsToCart of {item:Item.id; qty: int} 
            | GetCartSummary
            | RemoveItemsFromCart of {item: Item.id; qty:int}
end

module Cart_table =
struct
  include Store_interface.Make(Cart)
end

let get_item_cnt itemID eff = 
  match eff with 
 | Some x -> (match x with 
             | Cart.AddItemsToCart {item=id; qty=q} -> 
                if id=itemID then q else 0
             | Cart.RemoveItemsFromCart {item=id; qty=q} -> 
                if id=itemID then 0-q else 0
             | _ -> 0)
 | _ -> 0

let sum a b = a+b

let get_item_cnts cartID itemID = 
  let cart_effs = Cart_table.get cartID (Cart.GetCartSummary) in
  let qtys = List.map (get_item_cnt itemID) cart_effs in
  List.fold_right sum qtys 0

let get_item_stk itemID eff = 
  match eff with 
 | Some x -> (match x with 
             | Item.AddToStock {qty=q} -> q
             | Item.RemoveFromStock {qty=q} -> 0-q
             | _ -> 0)
 | _ -> 0

let get_item_stks itemID = 
  let item_effs = Item_table.get itemID (Item.ShowItem) in
  let qtys = List.map (get_item_stk itemID) item_effs in
  List.fold_right sum qtys 0

let do_addItemsToCart cartID itemID cnt = 
  let stk = get_item_stks itemID in
  if stk < cnt then ()
  else  
  begin
    Cart_table.append cartID (Cart.AddItemsToCart{item=itemID;qty=cnt});
    Item_table.append itemID (Item.RemoveFromStock{qty=cnt})
  end

let do_removeItemsFromCart cartID itemID cnt =
  if get_item_cnts cartID itemID < cnt then ()
  else
  begin
    Cart_table.append cartID (Cart.RemoveItemsFromCart{item=itemID;qty=cnt});
    Item_table.append itemID (Item.AddToStock{qty=cnt})
  end

let check_inv cartID eff = 
  match eff with
  | Some x -> (match x with
              | Cart.AddItemsToCart{item=itemID} -> 
                  get_item_cnts cartID itemID >= 0 &&
                  get_item_stks itemID >= 0
              | _ -> true)
  | _ -> true

let inv_fun cartID = 
  let cart_effs = Cart_table.get cartID (Cart.GetCartSummary) in
  List.forall cart_effs (check_inv cartID)