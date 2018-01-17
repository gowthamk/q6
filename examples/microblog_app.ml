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

  let rev_list l =
  let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in 
  rev_acc [] l

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
    | AddFollowing of {leader_id: id; timestamp: int}
    | RemFollowing of {leader_id: id; timestamp: int}
    | AddFollower of {follower_id: id; timestamp: int}
    | RemFollower of {follower_id: id;timestamp: int} 
    | Blocks of {follower_id: id}
    | GetBlocks
    | IsBlockedBy of {leader_id: id}
    | GetIsBlockedBy
    | GetInfo
    | GetFollowers
    | GetFollowing
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


(*
 * There is a zip/map2 bug unfixed. Fix goes in mkfun 
 * inside rdtextract.ml
 *) 
(*let do_test1 uid name = 
  let x = [1;2] in
  let y = UserName.GetId in
  let z = UserName.Add {user_id=uid} in
  let u1 = UserName_table.append name z in
  let u2 = UserName_table.get name y in
  let u3 = List.map 
             (fun eff -> match eff with
                | Some (UserName.Add {user_id=uid'}) -> Some uid'
                | _ -> None) u2 in
  let u4 = List.fold_right (fun idop acc -> match idop with
                             | Some uid' -> uid'::acc
                             | None -> acc) u3 [] in
    u4*)

(*let do_add_user name pwd = 
  let uid = Uuid.create() in
  begin
    UserName_table.append name (UserName.Add {user_id=uid});
    User_table.append uid (User.Add {username=name;pwd=pwd})
  end*) 

let get_user_id_by_name nm = 
  let ctxt = (* ea *) UserName_table.get nm (UserName.GetId) in
  let ids = List.map (fun eff -> match eff with 
                        | Some (UserName.Add {user_id=id}) -> Some id 
                        | _ -> None) ctxt in
  let num_ids = List.fold_right (fun idop acc -> match idop with
                                   | None -> acc
                                   | Some _ -> 1 + acc) ids 0 in
    begin
      if num_ids > 1 then raise Inconsistency else ();
      List.first_some ids
    end

(*let do_block_user me other  = 
  let Some my_id = get_user_id_by_name me in
  let Some other_id = get_user_id_by_name other in
  let ts = int_of_float (Unix.time ()) in
    begin
      User_table.append my_id (User.Blocks {follower_id=other_id});
      User_table.append other_id (User.IsBlockedBy {leader_id=my_id});
      User_table.append my_id (User.RemFollower {follower_id=other_id; timestamp=ts}); 
      User_table.append other_id (User.RemFollowing {leader_id=my_id; timestamp=ts})
    end*)

let find_last_ts fid ctxt = 
  let ts_list = List.map (fun eff -> match eff with
                  | Some x -> (match x with 
                              | User.AddFollower {follower_id=fid1; timestamp=ts1} -> if fid=fid1 then ts1 else (0-1) 
                              | _ -> (match x with 
                                     | User.RemFollower {follower_id=fid2; timestamp=ts2} -> if fid2=fid then ts2 else (0-1)
                                     | _ -> (0-1)))
                  | _ -> (0-1)) ctxt in
  List.fold_left (fun acc ts -> if ts > acc then ts else acc) (0-1) ts_list
  (*List.fold_right (fun ts acc -> if ts > acc then ts else acc) ts_list (0-1)*)

let is_follower fid ctxt = 
  let ts = find_last_ts fid ctxt in
  List.fold_right (fun eff acc -> match eff with 
                      | Some x -> (match x with
                                    | User.AddFollower {follower_id=fid1; timestamp=ts1} -> fid1=fid && ts1=ts
                                    | _ -> acc)
                      | _ -> acc) ctxt false

let do_new_tweet uid str = 
  let ctxt = User_table.get uid (User.GetFollowers) in
  let fids = List.map 
               (fun eff -> match eff with 
                  | Some x -> 
                      (match x with 
                         | User.AddFollower {follower_id=fid; timestamp=ts} -> if (is_follower fid ctxt) then Some fid else None
                         | _ -> None)
                  | _ -> None) ctxt in
  let tweet_id = Uuid.create() in
    begin
      Tweet_table.append tweet_id (Tweet.New {author_id=uid; content=str});
      Userline_table.append uid (Userline.NewTweet {tweet_id=tweet_id});
      List.iter 
        (fun fidop -> match fidop with 
           | Some fid -> Timeline_table.append fid 
                      (Timeline.NewTweet {tweet_id=tweet_id})
           | None -> ()) fids;
    end 

let get_tweet tid = 
  let ctxt = Tweet_table.get tid (Tweet.Get) in
  let tweets = List.map (fun eff -> match eff with
                           | Some (Tweet.New {content}) -> Some content
                           | _ -> None) ctxt in
  let res = List.first_some tweets in
    res

let inv_fun uid' = 
  List.forall (Userline_table.get uid' (Userline.Get))
  (fun e -> match e with
           | Some x -> 
               (match x with 
                  | Userline.NewTweet {tweet_id=tid} -> 
                      List.exists (Tweet_table.get tid Tweet.Get) 
                        (fun e' -> match e' with 
                           | Some y -> (match y with 
                                          | (Tweet.New _) -> true 
                                          | _ -> false)
                           | _ -> false)
                  | _ -> false)
           | _ -> true)

let get_userline uid = 
  let ctxt = Userline_table.get uid (Userline.Get) in
  let tweets = List.map 
                 (fun x -> match x with 
                    | Some y -> 
                        (match y with 
                           | Userline.NewTweet {tweet_id=tid} -> 
                                Some (get_tweet tid)
                           | _ -> None)
                    | _ -> None) ctxt in
  (*let _ = List.iter (fun top -> match top with 
                           | Some x ->  (match x with
                                           | Some _ -> ()
                                           | None -> raise Inconsistency)
                           | None -> ()) 
            tweets in*)
    tweets