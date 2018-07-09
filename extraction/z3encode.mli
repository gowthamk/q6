module Log = Z3.Log
module Solver = Z3.Solver
module Model = Z3.Model
module Symbol = Z3.Symbol
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Sort = Z3.Sort
module Datatype = Z3.Datatype
module FuncDecl = Z3.FuncDecl
module Quantifier = Z3.Quantifier
module Expr = Z3.Expr
module Constructor = Z3.Datatype.Constructor
val mk_new_ctx : unit -> Z3.context
val ctx_to_string : unit -> string
val reset : unit -> unit
val sym : string -> Symbol.symbol
val mk_app : Z3.FuncDecl.func_decl -> Z3.Expr.expr list -> Z3.Expr.expr
val mk_int_sort : unit -> Z3.Sort.sort
val mk_bool_sort : unit -> Z3.Sort.sort
val mk_numeral_i : int -> Z3.Expr.expr
val mk_uninterpreted_s : string -> Z3.Sort.sort
val mk_const_s : string -> Z3.Sort.sort -> Expr.expr
val mk_constructor_s :
  string ->
  Z3.Symbol.symbol ->
  Z3.Symbol.symbol list ->
  Z3.Sort.sort option list -> int list -> Z3.Datatype.Constructor.constructor
val mk_sort_s :
  string -> Z3.Datatype.Constructor.constructor list -> Z3.Sort.sort
val mk_func_decl_s :
  string -> Z3.Sort.sort list -> Z3.Sort.sort -> Z3.FuncDecl.func_decl
val mk_and : Z3.Expr.expr list -> Z3.Expr.expr
val mk_or : Z3.Expr.expr list -> Z3.Expr.expr
val mk_eq : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_gt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_lt : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_ge : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_le : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_not : Z3.Expr.expr -> Z3.Expr.expr
val mk_true : unit -> Z3.Expr.expr
val mk_false : unit -> Z3.Expr.expr
val mk_ite : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_distinct : Z3.Expr.expr list -> Z3.Expr.expr
val mk_add : Z3.Expr.expr list -> Z3.Expr.expr
val mk_sub : Z3.Expr.expr list -> Z3.Expr.expr
val mk_mul : Z3.Expr.expr list -> Z3.Expr.expr
val _assert : Z3.Expr.expr -> unit
val _assert_all : Z3.Expr.expr list -> unit
val push : unit -> unit
val pop : unit -> unit
val check_sat : unit -> Solver.status
                          val get_model : unit -> Z3.Model.model
val ( @=> ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @<=> ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @& ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @| ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @= ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @< ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @> ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @>= ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @<= ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( @!= ) : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val ( !@ ) : Z3.Expr.expr -> Z3.Expr.expr
val forall :
  Z3.Sort.sort list ->
  (Z3.Expr.expr list -> Z3.Expr.expr) -> Z3.Quantifier.quantifier
val expr_of_quantifier : Z3.Quantifier.quantifier -> Z3.Expr.expr

