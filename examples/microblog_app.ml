open Q6_interface
module User = 
struct
  type id = Uuid.t
  type eff = Add of {username: string; pwd: string}
    | AddFollowing of {leader_id: id}
    | RemFollowing of {leader_id: id}
    | AddFollower of {follower_id: id}
    | RemFollower of {follower_id: id} 
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
let do_test1 uid name = 
  let x = [1;2] in
  let y = UserName.GetId in
  let z = UserName.Add {user_id=uid} in
  let u1 = UserName_table.append name z in
  let u2 = UserName_table.get name y in
    u2

let do_add_user name pwd = 
  let uid = Uuid.create() in
  begin
    UserName_table.append name @@ UserName.Add {user_id=uid};
    User_table.append uid @@ User.Add {username=name;pwd=pwd}
  end 

let get_user_id_by_name nm = 
  let ctxt = (* ea *) UserName_table.get nm (UserName.GetId) in
    (* [sel(e0,ea); sel(e1,ea); sel(e2,ea)]@f(S,ea) *)
  let ids = List.concat @@ 
              List.map (function (UserName.Add {user_id=id}) -> [id] 
                          | _ -> []) ctxt in
  let res = match ids with
      | [] -> None
      | [id] -> Some id
      | _ -> raise Inconsistency in
    res

let do_block_user me other  = 
  let Some my_id = get_user_id_by_name me in
  let Some other_id = get_user_id_by_name other in
    begin
      User_table.append my_id (User.Blocks {follower_id=other_id});
      User_table.append other_id (User.IsBlockedBy {leader_id=my_id});
      User_table.append my_id (User.RemFollower {follower_id=other_id}); 
      User_table.append other_id (User.RemFollowing {leader_id=my_id})
    end

let do_new_tweet uid str = 
  let ctxt = User_table.get uid (User.GetFollowers) in
  let fids = List.concat @@ List.map 
               (function (User.AddFollower {follower_id}) -> [follower_id]
                  | _ -> []) ctxt in
  let tweet_id = Uuid.create() in
    begin
      Tweet_table.append tweet_id (Tweet.New {author_id=uid; content=str});
      Userline_table.append uid (Userline.NewTweet {tweet_id=tweet_id});
      List.iter 
        (fun fid -> Timeline_table.append fid 
                      (Timeline.NewTweet {tweet_id=tweet_id})) fids;
    end

let get_tweet tid = 
  let ctxt = Tweet_table.get tid (Tweet.Get) in
  let tweets = List.concat @@
                List.map (function (Tweet.New {content}) -> [content]
                            | _ -> [] ) ctxt in
  let res = match tweets with 
    | [] -> None | [c] -> Some c
    | _ -> raise Inconsistency in
    res

let get_userline uid = 
  let ctxt = Userline_table.get uid (Userline.Get) in
  let tids = List.concat @@ 
               List.map 
                 (fun x -> match x with 
                    | (Userline.NewTweet {tweet_id}) -> [tweet_id] 
                    | _ -> []) ctxt in
  let tweets = List.map (fun tid -> match get_tweet tid with 
                           | Some c -> c
                           | None -> raise Inconsistency) tids in
    tweets
