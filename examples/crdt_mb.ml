open Crdts

module Microblog_Types = struct
  type user = {id:Uuid.t; name:string; mutable followers:Uuid.t CRSet.t}
  type users_table =  user CRTable.t


  type tweet = {id:Uuid.t; author_id: Uuid.t; content: string CRSet.t}
  type tweets_table = tweet CRTable.t

  type line_item = {(*user_*)id:Uuid.t; tweet_id:Uuid.t}
  type userline_table = line_item CRTable.t


  type timeline_table = line_item CRTable.t


  type mb_db = {users_table:users_table; 
                tweets_table: tweets_table; 
                userline_table: userline_table;
                timeline_table: timeline_table}
end

open Microblog_Types

module User(S:sig 
                 val t: users_table 
               end) = struct
  open S

  let add_follower (user_id:Uuid.t) (follower_id: Uuid.t) =
    CRTable.update 
      (fun {followers} -> CRSet.add follower_id followers) 
      (fun {id} -> id=user_id) t

  let remove_follower (user_id:Uuid.t) (follower_id: Uuid.t) =
    CRTable.update 
      (fun {followers} -> CRSet.remove follower_id followers) 
      (fun {id} -> id=user_id) t

  let get_followers (user_id:Uuid.t) : Uuid.t list = 
    CRTable.find (fun {followers} -> CRSet.get followers) 
       (fun {id} -> id = user_id) t
end


module Userline(S:sig 
                    val t: userline_table 
                  end) = struct
  open S

  let add (user_id:Uuid.t) (tweet_id:Uuid.t) = 
    CRTable.insert {id=user_id; tweet_id=tweet_id} t

  let get (user_id:Uuid.t) =
    CRTable.find (fun {tweet_id} -> tweet_id)
      (fun {id} -> id = user_id) t
end

module Timeline(S:sig 
                    val t: timeline_table 
                  end) = struct
  open S

  let add (user_id:Uuid.t) (tweet_id:Uuid.t) = 
    CRTable.insert {id=user_id; tweet_id=tweet_id} t

  let get (user_id:Uuid.t) =
    CRTable.find (fun {tweet_id} -> tweet_id)
      (fun {id} -> id = user_id) t
end

module Tweet(S:sig
                val t: tweets_table
               end) = struct
  open S

  let add tweet_id author_id content = 
    CRTable.insert {id=tweet_id; author_id=author_id; 
                    content=CRSet.singleton content} t

  let get tweet_id =
    CRTable.find (fun {content} -> CRSet.get content)
      (fun {id} -> id = tweet_id) t
end
     
module MicroblogApp(S:sig 
                        val db: mb_db 
                      end) = struct
  open S
  module User = User(struct let t = db.users_table end)
  module Userline = Userline(struct let t = db.userline_table end)
  module Timeline = Timeline(struct let t = db.userline_table end)
  module Tweet = Tweet(struct let t = db.tweets_table end)

  let do_new_tweet (uid:Uuid.t) (str:string) = 
    let tweet_id = Uuid.create () in
    let fols = User.get_followers uid in
    begin
      Tweet.add tweet_id uid str;
      Userline.add uid tweet_id;
      List.iter (fun fid -> Timeline.add fid tweet_id) fols;
    end

  let inv_referential_integrity uid' = 
    let ul_tweet_ids = Userline.get uid' in
    let exists_in_tweet_table tid = 
      match Tweet.get tid with
        | tweet::_ -> true
        | _ -> false in
    List.for_all (exists_in_tweet_table) ul_tweet_ids

end
