open Q6_interface
(*open Debug*)

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

  let rec fold_left g b l = match l with
    | [] -> b
    | x::xs -> fold_left g (g b x) xs

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

module L =
struct
  let forall l f = true
  let exists l f = true
end

module User = 
struct
  type id = Uuid.t
  type eff = Add of {username: string; pwd: string}
    | AddFollower of {follower_id: id; timestamp: int}
    | RemFollower of {follower_id: id;timestamp: int} 
    | GetFollowers
end
module User_table =
struct
  include Store_interface.Make(User)
end

module UserName = 
struct
  type id = string
  type eff = Add of {user_id: User.id} | GetId
end
module UserName_table =
struct
  include Store_interface.Make(UserName)
end

module Tweet =
struct
  type id = Uuid.t
  type eff = New of {author_id:User.id; content:string}
    | Get
end
module Tweet_table =
struct
  include Store_interface.Make(Tweet)
end

module Timeline = 
struct
  type id = User.id
  type eff = NewTweet of {tweet_id:Tweet.id}
    | Get
end
module Timeline_table =
struct
  include Store_interface.Make(Timeline)
end

module Userline = 
struct
  type id = User.id
  type eff = NewTweet of {tweet_id:Tweet.id}
    | Get
end
module Userline_table =

struct
  include Store_interface.Make(Userline)
end

let rec first f b l = match l with
  | [] -> b
  | x::xs -> match x with 
      | Some y -> if f y then y 
          else first f b xs
      | None -> first f b xs

let is_gte ts tsop' = match tsop' with 
 | Some ts' -> ts' <= ts 
 | None -> true

let is_max_in (ts_list : int option list) (ts:int) = 
  List.forall ts_list (is_gte ts)
    
let rec max_ts (ts_list: int option list) : int= 
  first (is_max_in ts_list) (0-1) ts_list

let if_af_get_ts (fid:User.id) (eff: User.eff option) = match eff with
  | Some x -> (match x with
      | User.AddFollower {follower_id=fid'; 
                     timestamp=ts} -> 
          if fid'=fid then Some ts else None
      | _ -> None)
  | None -> None

let if_rf_get_ts (fid:User.id) (eff: User.eff option) = match eff with
  | Some x -> (match x with
      | User.RemFollower {follower_id=fid'; 
                     timestamp=ts} -> 
          if fid'=fid then Some ts else None
      | _ -> None)
  | None -> None

let is_follower fid ctxt = 
  let af_ts = List.map (if_af_get_ts fid) ctxt in
  let rf_ts = List.map (if_rf_get_ts fid) ctxt in
  let max_af_ts = max_ts af_ts in
  let max_rf_ts = max_ts rf_ts in
    max_af_ts >= max_rf_ts

let get_fid ctxt' eff = 
  match eff with 
  | Some x -> 
      (match x with 
         | User.AddFollower {follower_id=fid; 
                             timestamp=ts} -> 
             if (is_follower fid ctxt') then Some fid else None
         | _ -> None)
  | _ -> None

let new_tweet tweet_id' fidop = 
  match fidop with 
  | Some fid -> Timeline_table.append fid 
             (Timeline.NewTweet {tweet_id=tweet_id'})
  | None -> ()

let do_new_tweet (uid:Uuid.t) (str:string) = causally_do @@
  let ctxt = User_table.get uid (User.GetFollowers) in
  let fids = List.map (get_fid ctxt) ctxt in
  let tweet_id = Uuid.create() in
    begin
      Tweet_table.append tweet_id (Tweet.New {author_id=uid; content=str});
      Userline_table.append uid (Userline.NewTweet {tweet_id=tweet_id});
      List.iter (new_tweet tweet_id) fids;
    end

let exists_tweet e' =
   match e' with 
   | Some y -> (match y with 
                  | (Tweet.New _) -> true 
                  | _ -> false)
   | _ -> false

let exists_in_tweet_table e = 
  match e with
  | Some x -> 
      (match x with 
         | Userline.NewTweet {tweet_id=tid} -> 
             List.exists (Tweet_table.get tid Tweet.Get) exists_tweet
         | _ -> false)
  | _ -> true

let inv_referential_integrity uid' = 
  List.forall (Userline_table.get uid' (Userline.Get)) exists_in_tweet_table

