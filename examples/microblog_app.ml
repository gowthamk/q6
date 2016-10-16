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

let do_add_user name pwd = 
  let uid = Uuid.create() in
  begin
    UserName_table.append name @@ UserName.Add {user_id=uid};
    User_table.append uid @@ User.Add {username=name;pwd=pwd}
  end 

let rec sum l = match l with 
  | [] -> 0
  | x::xs -> x + (sum xs)

let get_user_id_by_name nm = 
  let ctxt = UserName_table.get nm (UserName.GetId) in
  let ids = List.concat @@ 
              List.map (function (UserName.Add {user_id=id}) -> [id] 
                          | _ -> []) ctxt in
    match ids with
      | [] -> None
      | [id] -> Some id
      | _ -> raise Inconsistency

let do_block_user me other  = 
  let Some my_id = get_user_id_by_name me in
  let Some other_id = get_user_id_by_name other in
    begin
      User_table.append my_id (User.Blocks {follower_id=other_id});
      User_table.append other_id (User.IsBlockedBy {leader_id=my_id});
      User_table.append my_id (User.RemFollower {follower_id=other_id}); 
      User_table.append other_id (User.RemFollowing {leader_id=my_id})
    end
