module Z3 = Z3encode
module Expr = Z3.Expr
module Sort = Z3.Sort
module FuncDecl = Z3.FuncDecl
module Type = Speclang.Type

(*
 * encoding_env object maintains the state of encoding.
 *)
class encoding_env :
  object
    val cmap : (string, Expr.expr) Hashtbl.t
    val fmap : (string, FuncDecl.func_decl) Hashtbl.t
    val tmap : (Type.t, Sort.sort) Hashtbl.t
    method all_mkkey_funs : unit -> FuncDecl.func_decl list
    method ar : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method ar_id : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method ar_oper : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method const_of_id : Ident.t -> Expr.expr
    method const_of_name : string -> Expr.expr
    method currtxn : Z3.Expr.expr -> Z3.Expr.expr
    method fun_of_str : string -> FuncDecl.func_decl
    method get_cmap : (string, Expr.expr) Hashtbl.t
    method get_fmap : (string, FuncDecl.func_decl) Hashtbl.t
    method get_tmap : (Type.t, Sort.sort) Hashtbl.t
    method hb : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method objid : Z3.Expr.expr -> Z3.Expr.expr
    method objtyp : Z3.Expr.expr -> Z3.Expr.expr
    method oper : Z3.Expr.expr -> Z3.Expr.expr
    method replid : Z3.Expr.expr -> Z3.Expr.expr
    method reset : unit -> unit
    method sameobj : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method seqno : Z3.Expr.expr -> Z3.Expr.expr
    method so : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
    method sort_of_typ : Type.t -> Sort.sort
    method ssn : Z3.Expr.expr -> Z3.Expr.expr
    method txn : Z3.Expr.expr -> Z3.Expr.expr
    method vis : Z3.Expr.expr * Z3.Expr.expr -> Z3.Expr.expr
  end
