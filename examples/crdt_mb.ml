open Crdts

module Microblog_Types = struct
  type user = {id:Uuid.t; name:string; mutable followers:Uuid.t CRSet.t}
  type users_table =  user CRTable.t
  type tweet = {id:Uuid.t; author_id: Uuid.t; content: string}
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
    let fols = CRTable.find (fun {followers} -> followers) 
                (fun {id} -> id = user_id) t in
    match fols with | Some fs -> CRSet.get fs
                    | None -> []
end


module Userline(S:sig 
                    val t: userline_table 
                  end) = struct
  open S

  let add (user_id:Uuid.t) (tweet_id:Uuid.t) = 
    CRTable.insert {id=user_id; tweet_id=tweet_id} t
end

module Timeline(S:sig 
                    val t: timeline_table 
                  end) = struct
  open S

  let add (user_id:Uuid.t) (tweet_id:Uuid.t) = 
    CRTable.insert {id=user_id; tweet_id=tweet_id} t
end

module Tweet(S:sig
                val t: tweets_table
               end) = struct
  open S

  let add tweet_id author_id content = 
    CRTable.insert {id=tweet_id; author_id=author_id; 
                    content=content} t
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

end
