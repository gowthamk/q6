open Utils
open Z3
open Z3.SMT
open Z3.Sort
open Z3.Expr
open Z3.Optimize
open Z3.Solver
open Z3.Symbol
open Z3.Datatype
open Z3.FuncDecl
open Z3.Boolean
open Z3.Arithmetic 
open Z3.Arithmetic.Integer
open Z3.Quantifier
module Log = Z3.Log
module Solver = Z3.Solver
module OptSolver = Z3.Optimize
module Model = Z3.Model
module Symbol = Z3.Symbol
module Optimize = Z3.Optimize
module Int = Z3.Arithmetic.Integer
module Bool = Z3.Boolean
module Sort = Z3.Sort
module Datatype = Z3.Datatype
module FuncDecl = Z3.FuncDecl
module Quantifier = Z3.Quantifier
module Expr = Z3.Expr
module Constructor = Z3.Datatype.Constructor

let mk_new_ctx () = 
  let cfg = [("model", "true"); ("proof", "false")] in
    mk_context cfg

let ctx = ref @@ mk_new_ctx ()
let solver = ref @@ mk_solver !ctx None 

let ctx_to_string () = Solver.to_string !solver

let reset () = 
  begin
    ctx := mk_new_ctx ();
    solver := mk_solver !ctx None;
  end

(*
 * Z3 API for the current ctx
 *)
let sym s = Symbol.mk_string !ctx s
let mk_app f args = mk_app !ctx f args
let mk_int_sort () = Int.mk_sort !ctx
let mk_bool_sort () = Bool.mk_sort !ctx
let mk_numeral_i i = Int.mk_numeral_i !ctx i
let mk_uninterpreted_s s = mk_uninterpreted_s !ctx s
let mk_const_s str sort = Expr.mk_const_s !ctx str sort
let mk_constructor_s a b c d e = mk_constructor_s !ctx a b c d e
let mk_sort_s a b = mk_sort_s !ctx a b
let mk_func_decl_s name arg_sorts res_sort = 
  mk_func_decl_s !ctx name arg_sorts res_sort
let mk_and conjs = mk_and !ctx conjs
let mk_or conjs = mk_or !ctx conjs
let mk_eq e1 e2 = mk_eq !ctx e1 e2
let mk_gt e1 e2 = mk_gt !ctx e1 e2
let mk_lt e1 e2 = mk_lt !ctx e1 e2
let mk_ge e1 e2 = mk_ge !ctx e1 e2
let mk_le e1 e2 = mk_le !ctx e1 e2
let mk_not e = mk_not !ctx e
let mk_true () = mk_true !ctx
let mk_false () = mk_false !ctx
let mk_ite e1 e2 e3 = mk_ite !ctx e1 e2 e3
let mk_distinct es = mk_distinct !ctx es
let mk_add es = mk_add !ctx es
let mk_sub es = mk_sub !ctx es
let mk_mul es = mk_mul !ctx es
let _assert e = Solver.add !solver [e]
let _assert_all e = Solver.add !solver e
let push () = Solver.push !solver
let pop () = Solver.pop !solver 1
let check_sat () = Solver.check !solver []
let get_model () = match Solver.get_model !solver with
  | Some model -> model
  | None -> failwith "No model exists!"

let (@=>) e1 e2 = mk_implies !ctx e1 e2
let (@<=>) e1 e2 = mk_iff !ctx e1 e2
let (@&) e1 e2 = mk_and [e1; e2]
let (@|) e1 e2 = mk_or [e1; e2]
let (@=) e1 e2 = mk_eq e1 e2
let (@<) e1 e2 = mk_lt e1 e2
let (@>) e1 e2 = mk_gt e1 e2
let (@>=) e1 e2 = mk_ge e1 e2
let (@<=) e1 e2 = mk_le e1 e2
let (@!=) e1 e2 = mk_not (e1 @= e2)
let (!@) e = mk_not e

let forall sorts f = 
  let n = List.length sorts in
  let names = List.tabulate n 
                (fun i -> sym @@ "a"^(string_of_int i)) in
  let vars = List.tabulate n 
               (fun i -> mk_bound !ctx (n-i-1) 
                           (List.nth sorts i)) in
  let body = f vars in
    mk_forall !ctx sorts names body None [] [] None None

let expr_of_quantifier = expr_of_quantifier

