module Z3 = Z3encode
module Expr = Z3.Expr
module Sort = Z3.Sort
module FuncDecl = Z3.FuncDecl
module Type = Speclang.Type 

let printf = Printf.printf

let mk_app = Z3.mk_app

class encoding_env = 
  object (self)
    val cmap : (string,Expr.expr) Hashtbl.t = Hashtbl.create 211
    val tmap : (Type.t,Sort.sort) Hashtbl.t = Hashtbl.create 47
    val fmap : (string,FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 47

    method get_cmap = cmap
    method get_tmap = tmap
    method get_fmap = fmap

    method sort_of_typ typ = try Hashtbl.find tmap typ 
                          with Not_found ->
                            (printf "%s not found in tmap" 
                               (Type.to_string typ); raise Not_found)
    method fun_of_str str = try Hashtbl.find fmap str
                          with Not_found ->
                            (printf "%s not found in fmap" str;
                             raise Not_found)
    method const_of_name n = try Hashtbl.find cmap n 
                          with Not_found -> (printf "%s not found in cmap" n; 
                                             raise Not_found)
    method const_of_id id = self#const_of_name @@ Ident.name id
    method all_mkkey_funs () = Hashtbl.fold (fun name func acc -> 
                              if Str.string_match (Str.regexp "^mkkey_") name 0
                              then func::acc else acc) fmap []
    method reset () = 
      Hashtbl.clear cmap;
      Hashtbl.clear tmap;
      Hashtbl.clear fmap;

    method vis (e1,e2) = mk_app (self#fun_of_str "vis") [e1; e2]
    method so (e1,e2) = mk_app (self#fun_of_str "so") [e1; e2]
    method hb (e1,e2) = mk_app (self#fun_of_str "hb") [e1; e2]
    method ar (e1,e2) = mk_app (self#fun_of_str "ar") [e1; e2]
    method ar_id (id1,id2) = mk_app (self#fun_of_str "ar_id") [id1; id2]
    method ar_oper (op1,op2) = mk_app (self#fun_of_str "ar_oper") [op1; op2]
    method sameobj (e1,e2) = mk_app (self#fun_of_str "sameobj") [e1; e2]
    method objtyp e = mk_app (self#fun_of_str "objtyp") [e]
    method objid e = mk_app (self#fun_of_str "objid") [e]
    method replid e = mk_app (self#fun_of_str "replid") [e]
    method ssn e = mk_app (self#fun_of_str "ssn") [e]
    method txn e = mk_app (self#fun_of_str "txn") [e]
    method currtxn e = mk_app (self#fun_of_str "currtxn") [e]
    method seqno e = mk_app (self#fun_of_str "seqno") [e]
    method oper e = mk_app (self#fun_of_str "oper") [e]

  end

