open Asttypes
open Path
open Types
open Typedtree
open Speclang
open Utils
open Printf
open QueleaUtils

module R = Rdtextract 

let len = List.length 

let find_typedec_mod str_items = 
  let last_token str = 
    List.last @@ Str.split (Str.regexp "_") str in
  let s = List.find 
      (fun {str_desc} -> match str_desc with 
         | Tstr_module {mb_id} when (last_token 
                  @@ Ident.name mb_id = "Types") -> true
         | _ -> false) str_items in
  match s.str_desc with 
    | Tstr_module mod_bind -> mod_bind
    | _ -> failwith "find_typedec_mod: Impossible!"

let structure_of_mod = function
  | {mb_expr={mod_desc=Tmod_structure struc}} -> struc
  | _ -> failwith "structure_of_mod: mod not a structure"

(*
 * Return All record type decs in the given structure
 *)
let filter_record_type_decs str_items = 
  let record_type_dec str_item = match str_item.str_desc with
      | Tstr_type (_,[{typ_kind=Ttype_record _} 
                      as type_dec]) -> Some type_dec
      | _ -> None in
  List.map_some record_type_dec str_items
(*
 * Find all table type names and their record type names
 *)
let get_table_types str_items = 
  let open Path in
  let debug str path = printf "%s =%s didn't match\n" str
                        (Printtyp.string_of_path path) in
  let table_type_of str_item = match str_item.str_desc with
    | Tstr_type (_,[{typ_kind=Ttype_abstract; 
                     typ_manifest=Some 
                       {ctyp_desc=Ttyp_constr (crt_path,_,[crt_arg])}; 
                     typ_name={txt=ttype_name}}]) 
      when (match crt_path with
            | Pdot (Pdot(Pident id,"CRTable",_),"t",_) 
              when (Ident.name id = "Crdts") -> true
            | Pdot (Pdot(Pident id,"CRTable",_),"t",_) 
              when (Ident.name id <> "Crdts") -> 
                (printf "\"Crdts\" module missing?"; false)
            | _ -> debug ttype_name crt_path;false) -> 
        let rtype_name = match crt_arg with
          | {ctyp_desc=Ttyp_constr (Pident rt_id,_,[])} -> 
              Ident.name rt_id
          | _ -> failwith "table_type_of: Unexpected!\n" in
        Some (ttype_name,rtype_name)
    | _ -> None in
  let names = List.map_some table_type_of str_items in
  names


(*
 * Gets (sig ... end) and struc if the given module is 
 * functor(_:(sig ... end)) -> struc.
 *)
let get_arg_sig_and_struc_if_functor ({mod_desc}:module_expr) = 
  match mod_desc with
    | Tmod_functor (_,_,Some {mty_desc},{mod_desc}) -> 
        (match (mty_desc, mod_desc) with
          | (Tmty_signature sign, 
             Tmod_structure struc) -> Some (sign,struc)
          | _ -> None)
    | _ -> None

(*
 * Returns typ.name if the given module is a functor whose (first)
 * argument signature is of the form "sig val t:typ end"
 *)
let get_tname_if_targ_sig targ_sig =
  match targ_sig with
    | {sig_items=[{sig_desc=Tsig_value {val_name={txt="t"}; 
                                             val_desc={ctyp_desc}}}]} -> 
        (match ctyp_desc with 
          | Ttyp_constr (path, _,[]) -> Some (Path.last path)
          | _ -> None)
    | _ -> None

(*
 * Returns (mod.name, type.name, structure) if the given str_item is a
 * functor definition of the form
 *       module mod = functor(_:sig val t:typ end) -> structure
 *)
let get_modname_tname_and_struc_if_tmod {str_desc} = 
  match str_desc with 
    | Tstr_module {mb_name={txt}; mb_expr} -> 
        let ss_opt = get_arg_sig_and_struc_if_functor mb_expr in
        (match ss_opt with
          | Some (sign,struc) -> 
              (match get_tname_if_targ_sig sign with 
                | Some tname -> Some (txt, tname, struc)
                | None -> None)
          | None -> None)
    | _ -> None

(*
 * Intermediate representation of a table module
 *)

type tmod1 = {name: string; 
              tname:string; 
              rtype_dec: type_declaration;
              structure:structure}

(*
 * tr_pairs:string*type_declaration is a list of table type names and
 * their record type declaration. This function maps tr_pairs to tmods.
 *)
let filter_table_mods tr_pairs str_items = 
  let tmod_defs = List.map_some get_modname_tname_and_struc_if_tmod
                            str_items in
  List.map 
    (fun (tname, rtype_dec) -> 
       let (name,_,struc) = try List.find (fun (name,tname',struc) -> 
                                                      tname' = tname) 
                                  tmod_defs 
                            with Not_found -> failwith @@ "Table \
                               module for "^tname^" not found" in
       {name=name; 
        tname=tname; 
        rtype_dec=rtype_dec; 
        structure=struc}) 
    tr_pairs 

(*
 * Second IR for table mod. Type annot_fun denotes a function
 * annotated with the label of the CRDT type it reads/writes.
 *)
type crdt = CRInt | CRSet 

type annot_fun = Fun.t * string * crdt

type cr_fun = Read of annot_fun
            | Update of annot_fun
            | Insert of Fun.t
            | Aux of Fun.t

type tmod2 = {name: string;
              tname: string;
              rtype_dec: type_declaration;
              cr_funs: cr_fun list}

let get_fun_if_fun_bind (rec_flag, {vb_pat; vb_expr}) = 
  match (vb_pat.pat_desc, vb_expr.exp_desc) with 
    | (Tpat_var (_,loc), Texp_function (_,[case],_)) -> 
        let (args,body) = Misc.extract_lambda case in
        let open Types in
        let arrow_t = vb_expr.exp_type.desc in
        let (arg_ts,res_t) = Misc.uncurry_arrow arrow_t in 
          Some (Fun.make ~name: (Ident.create loc.txt) 
                 ~rec_flag: rec_flag
                 ~args_t: (List.zip args arg_ts) 
                 ~res_t: res_t ~body: body)
    | _ -> None

(*
 * returns a list of record type components and their types.
 *)
let rtype_components {typ_kind} : (string*core_type) list = 
  match typ_kind with
    | Ttype_record ldecs -> 
        List.map (fun {ld_name={txt};ld_type} -> 
                                      (txt,ld_type)) ldecs
    | _ -> failwith "Expected record type. Got sth else."

(*
 * Returns "lbl" if the given expression is of the form:
 *      fun {lbl} -> e'
 *)
let get_projected_column {exp_desc} = match exp_desc with
  | Texp_function (_,[case],_) -> 
      let (args,_) = Misc.extract_lambda case in
      (match args with
        | [arg] -> Ident.name arg
        | _ -> failwith "get_projected_column: Unexpected!")
  | _ -> failwith "get_projected_column: Fn expected."

let get_type_of_column (col:string) 
                       (rcomps:(string*core_type) list) = 
  try List.assoc col rcomps 
  with Not_found -> failwith @@ "Unknown column "^col

let rec maybe_crdt_of_core_type {ctyp_desc} = match ctyp_desc with
  | Ttyp_constr (Pdot (Pdot(Pident id,"CRInt",_),"t",_), _,[]) 
    when Ident.name id = "Crdts" -> Some CRInt
  | Ttyp_constr (Pdot (Pdot(Pident id,"CRSet",_),"t",_), _,_) 
    when Ident.name id = "Crdts" -> Some CRSet
  | Ttyp_constr(path, _, _) -> 
      (printf "path is %s\n" @@ Printtyp.string_of_path path; None)
  | Ttyp_alias (core_typ,_) -> maybe_crdt_of_core_type core_typ 
  | Ttyp_poly ([],core_typ) -> maybe_crdt_of_core_type core_typ
  | _ -> None

let crdt_of_core_type core_type = 
  let fail_msg () = 
      Printtyp.type_expr Format.str_formatter core_type.ctyp_type;
       "crdt_of_core_type: "^(Format.flush_str_formatter ())
        ^" is not CRDT\n" in
  match maybe_crdt_of_core_type core_type with
    | Some crdt -> crdt
    | _ -> failwith @@ fail_msg ()

let get_crdt_component rcomps = 
  let inj x = function | Some y -> Some (x,y)
                       | None -> None in
  let cr_comps = List.map_some 
      (fun (name,core_type) -> 
         inj name @@ maybe_crdt_of_core_type core_type)
      rcomps in
  match cr_comps with
    | [cr_comp] -> cr_comp
    | [] -> failwith "get_crdt_component: there are none!"
    | _ -> failwith "get_crdt_component: there are too many!\
                     \ Unimpl."

let classify_fun_in_tmod (({rtype_dec} as tmod):tmod1)
                         (Fun.T {name; body} as fun_t) =
  let fn_name = Ident.name name in
  (* ------ *)
  let fn_status = ref (Aux fun_t) in
  (* ------ *)
  let rcomps = rtype_components rtype_dec in
  let open TypedtreeIter in
  let iter_exp ({exp_desc} as exp) = match exp_desc with
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2); 
                      (Nolabel,Some e3)])
      when (is_crtable_find e || is_crtable_update e) ->
        let col = get_projected_column e1 in
        let col_core_type = get_type_of_column col rcomps in
        let col_crdt_type = crdt_of_core_type col_core_type in
        let annot_fun = (fun_t, col, col_crdt_type) in
        begin
          if is_crtable_find e 
          then ((*printf "%s is read fn\n" fn_name;*)
               fn_status := Read annot_fun)
          else ((*printf "%s is update fn\n" fn_name; *)
               fn_status := Update annot_fun)
        end
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2)]) 
      when is_crtable_insert_or_delete e ->
        begin
          (*printf "%s is insert/delete fn\n" fn_name;*)
          fn_status := Insert fun_t
        end
    | _ -> ()(*Printtyped.expression 0 Format.str_formatter exp*) in
  let module Iterator = MakeIterator(struct
      include DefaultIteratorArgument
      let enter_expression = iter_exp
    end) in
  let _ = Iterator.iter_expression body in
  !fn_status

let classify_funs_in_tmod ({structure={str_items}} as tmod) = 
  let get_if_val_bind {str_desc} = match str_desc with
    | Tstr_value (Recursive, [val_bind]) -> Some (true, val_bind)
    | Tstr_value (_, [val_bind]) -> Some (false, val_bind)
    | _ -> None in
  let val_binds = List.map_some get_if_val_bind str_items in
  let funs = List.map_some get_fun_if_fun_bind val_binds in
  (*let _ = printf "%s has %d funs\n" (tmod.name) (len funs) in*)
  let cr_funs = List.map (classify_fun_in_tmod tmod) funs in
  {name=tmod.name; tname=tmod.tname; 
   rtype_dec=tmod.rtype_dec; cr_funs=cr_funs}

(*
 * Effects
 *)
module Eff = 
struct
  type t = T of {name: Ident.t; 
                 args: (Ident.t*Types.type_desc) list;
                 interpreter: Fun.t option;
                 generator: Fun.t}
end

let ts_id = Ident.create "timestamp"
let int_id = Ident.create "int"

let append_id_exp = exp_of_id @@ Ident.create "append"
let get_id_exp = exp_of_id @@ Ident.create "get"

let mk_eff_append_exp_desc id_exp eff_id eff_args = 
  let cons_name = Ident.name eff_id in
  let loc = longident_loc_of cons_name in
  let cons_desc = cons_desc_of cons_name in
  let arg_ids = List.map fst eff_args in
  let arg_record = reflective_record_of arg_ids in
  let cons_app_desc = Texp_construct (loc, cons_desc, 
                                      [arg_record]) in
  let cons_app = exp_of cons_app_desc in
  Texp_apply (append_id_exp, [(Nolabel,Some id_exp); 
                              (Nolabel,Some cons_app)])
 
let transform_interp interp crdt args = match (interp,crdt) with
  | ({exp_desc=Texp_function (_,[case],_)}, CRSet) -> 
      let ([crdt_arg],body) = Misc.extract_lambda case in
      let args' = args@[(crdt_arg,Tnil)] in
      let aset_id = Ident.create "_adds" in
      let rset_id = Ident.create "_removes" in
      let aset = exp_of_id aset_id in
      let rset = exp_of_id rset_id in
      let ts_exp = exp_of_id ts_id in
      let open TypedtreeMap in
      let map_exp ({exp_desc} as exp) = match exp_desc with
        | Texp_apply (e, [(Nolabel,Some e1); 
                          (Nolabel,Some _)]) 
          when pp_expr e = "Crdts.CRSet.add" -> 
            let list_cons = cons_desc_of "::" in
            let e1' = exp_of @@ Texp_tuple [e1;ts_exp] in
            let lloc = longident_loc_of @@ Ident.name aset_id in
            let aset' = exp_of @@ Texp_construct 
                          (lloc, list_cons, [e1'; aset]) in
            exp_of @@ Texp_tuple [aset';rset]
        | Texp_apply (e, [(Nolabel,Some e1); 
                          (Nolabel,Some _)]) 
          when pp_expr e = "Crdts.CRSet.remove" -> 
            let list_cons = cons_desc_of "::" in
            let lloc = longident_loc_of @@ Ident.name aset_id in
            let e1' = exp_of @@ Texp_tuple [e1;ts_exp] in
            let rset' = exp_of @@ Texp_construct 
                          (lloc, list_cons, [e1'; rset]) in
            exp_of @@ Texp_tuple[aset; rset']
        | _ -> exp in
      let module Mapper = MakeMap(struct
          include DefaultMapArgument
          let enter_expression = map_exp
        end) in
      let body' = Mapper.map_expression body in
      let case' = {c_lhs=tuple_pat_of_ids aset_id rset_id;
                   c_rhs=body'; c_guard=None} in 
      let body'' = exp_of @@ Texp_match 
                      (exp_of_id crdt_arg, [case'], [], Total) in
      let interp' = Fun.make ~name:Fun.anonymous
                              ~rec_flag:false ~args_t:args' 
                              ~res_t:Tnil ~body:body'' in
      interp'
  | ({exp_desc=Texp_function (_,[case],_)}, CRInt) -> 
      let ([crdt_arg],body) = Misc.extract_lambda case in
      let args' = args@[(crdt_arg,Tnil)] in
      let open TypedtreeMap in
      let map_exp ({exp_desc} as exp) = match exp_desc with
        | Texp_apply (e, [(Nolabel,Some e1); 
                          (Nolabel,Some e2)]) 
          when pp_expr e = "Crdts.CRInt.add" -> 
            add_exp_of e1 e2
        | _ -> exp in
      let module Mapper = MakeMap(struct
          include DefaultMapArgument
          let enter_expression = map_exp
        end) in
      let body' = Mapper.map_expression body in
      let interp' = Fun.make ~name:Fun.anonymous 
                             ~rec_flag:false ~args_t:args' 
                             ~res_t:Tnil ~body:body' in
      interp'
  | _ -> failwith "Intep is not a function!"

let parse_id_exp e = 
  let id_exp = ref None in
  let open TypedtreeIter in
  let module Iterator = MakeIterator(struct
      include DefaultIteratorArgument
      let enter_expression ({exp_desc}) = 
        match exp_desc with
          | Texp_apply (e, [(Nolabel,Some e1);
                            (Nolabel,Some e2)]) 
            when (pp_expr e = "Pervasives.=") ->
              let s1 = pp_expr e1 in
              let s2 = pp_expr e2 in
              if s1 = "id" then id_exp:= Some e2 
              else if s2 = "id" then id_exp := Some e1
              else ()
          | _ -> ()
    end) in
  let _ = Iterator.iter_expression e in
  match !id_exp with
    | Some id_exp -> id_exp
    | None -> failwith "Id expression not found!"

(*
 * Currently we map one function to one effect only.
 *)
let eff_of_annot_upd (Fun.T {name=fn_id; rec_flag; args_t; 
                            res_t; body}, label, crdt) =
  let fname = Ident.name fn_id in
  let eff_name = String.capitalize_ascii fname in
  let eff_id = Ident.create eff_name in
  let eff_args = match crdt with
    | CRInt -> args_t
    | CRSet -> args_t@[(ts_id, Tconstr (Pident int_id, 
                                        [], ref Mnil))] in
  (*
   * Interpretation fn is effectively the second argument of update.
   *)
  let open TypedtreeMap in
  (* ---------- *)
  let interp = ref None in
  (* ---------- *)
  let map_exp ({exp_desc} as exp) = match exp_desc with
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2); 
                      (Nolabel,Some e3)])
      when is_crtable_update e ->
        let _ = interp := Some e1 in
        (*
         * By convention, selection predicate of update is an 
         * equality on id
         *)
        let id_exp = parse_id_exp e2 in 
        let exp_desc' = mk_eff_append_exp_desc id_exp 
                                          eff_id eff_args in
        {exp with exp_desc=exp_desc'}
    | _ -> exp(*Printtyped.expression 0 Format.str_formatter exp*) in
  let module Mapper = MakeMap(struct
      include DefaultMapArgument
      let enter_expression = map_exp
    end) in
  let body' = Mapper.map_expression body in
  let upd' = Fun.make ~name:fn_id ~rec_flag:rec_flag
                      ~args_t:eff_args ~res_t:res_t
                      ~body:body' in
  let interp = match !interp with
    | None -> failwith "Interpreter expression not found!"
    | Some interp_fn ->
      (*
       * body' is the body of generator. !interp is the interp fn.
       *)
        begin
          printf "Transformed body of %s:\n" fname;
          printf "    %s\n" (pp_expr body');
          (*Printtyped.expression 1 Format.std_formatter body';*)
          printf "Interpreter function for %s:\n" fname;
          (*Printtyped.expression 1 Format.std_formatter interp_fn;*)
          printf "    %s\n" (pp_expr interp_fn);
          interp_fn
        end in
  let interp' = transform_interp interp crdt eff_args in
  let _ = printf "Transformed interpreter fn:\n    %s\n" 
                  (pp_expr @@ Fun.body interp') in
  let eff = Eff.T {name=eff_id; args=eff_args; 
                   interpreter=Some interp'; 
                   generator=upd'} in
  eff

let eff_of_insert (Fun.T {name=fn_id; rec_flag; args_t; 
                          res_t; body}) =
  let fname = Ident.name fn_id in
  let eff_name = String.capitalize_ascii fname in
  let eff_id = Ident.create eff_name in
  let eff_args = args_t in
  let open TypedtreeMap in
  let map_exp ({exp_desc} as exp) = match exp_desc with
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2)])
      when is_crtable_insert e ->
        let fields = parse_record_exp e1 in
        let id_exp = List.assoc "id" fields in
        let exp_desc' = mk_eff_append_exp_desc id_exp 
                                          eff_id eff_args in
        {exp with exp_desc=exp_desc'}
    | _ -> exp(*Printtyped.expression 0 Format.str_formatter exp*) in
  let module Mapper = MakeMap(struct
      include DefaultMapArgument
      let enter_expression = map_exp
    end) in
  let body' = Mapper.map_expression body in
  let ins' = Fun.make ~name:fn_id ~rec_flag:rec_flag
                      ~args_t:eff_args ~res_t:res_t
                      ~body:body' in
  let _ = begin
            printf "Transformed body of %s:\n" fname;
            printf "    %s\n" (pp_expr body'); 
          end in
  let eff = Eff.T {name=eff_id; args=eff_args; 
                   interpreter=None; generator=ins'} in
  eff

(*
 * Read functions
 *)

let mk_fold_fn effs read_label = 
  let eff_to_case (Eff.T {name; args; 
                          interpreter; 
                          generator}) acc_id = 
    let eff_name = Ident.name name in
    let loc = longident_loc_of eff_name in
    let cdesc = cons_desc_of eff_name in
    let rec_pat = record_pat_of @@ List.map fst args in
    let lhs_pat = pat_of @@ Tpat_construct (loc, cdesc, [rec_pat]) in
    let rhs_exp = match interpreter with
      | Some (Fun.T {body; args_t}) -> 
          mk_simple_let_exp (fst @@ List.last args_t) 
                            acc_id body
      | None -> exp_of_id @@ Ident.create read_label in
    {c_lhs=lhs_pat; c_guard=None; c_rhs=rhs_exp} in
  let acc_id = Ident.create "acc" in
  let cases = List.map (fun eff -> eff_to_case eff acc_id) effs in
  let eff_id = Ident.create "eff" in
  let eff_exp = exp_of_id eff_id in
  let match_exp = exp_of @@ 
      Texp_match (eff_exp, cases, [], Total)  in
  let inner_case = mk_simple_case acc_id match_exp in
  let inner_fn = exp_of @@ Texp_function (Nolabel, 
                                          [inner_case], 
                                          Total) in
  let outer_case = mk_simple_case eff_id inner_fn in
    exp_of @@ Texp_function (Nolabel, [outer_case], Total)

let mk_eff_get_exp_desc id_exp eff_id =
  let cons_name = Ident.name eff_id in
  let loc = longident_loc_of cons_name in
  let cons_desc = cons_desc_of cons_name in
  let cons_app_desc = Texp_construct (loc, cons_desc, []) in
  let cons_app = exp_of cons_app_desc in
  Texp_apply (get_id_exp, [(Nolabel,Some id_exp); 
                           (Nolabel,Some cons_app)])

let transform_crfind id_exp eff_id wr_effs label crdt =
  let get_exp = exp_of @@ mk_eff_get_exp_desc id_exp eff_id in
  let ctxt_id = Ident.create "ctxt" in
  let ctxt_exp = exp_of_id ctxt_id in
  let ctxt_pat = pat_of_id ctxt_id in
  let foldfn = mk_fold_fn wr_effs label in
  let frexp = exp_of_id @@ Ident.create "List.fold_right" in
  let bexp = match crdt with
    | CRInt -> exp_of @@ Texp_constant (Const_int 0)
    | CRSet -> 
        let cdesc = cons_desc_of "[]" in
        let loc = longident_loc_of "[]" in
        let nil_e = exp_of @@ Texp_construct(loc, cdesc, []) in
        exp_of @@ Texp_tuple [nil_e; nil_e] in
  let fold_exp = exp_of @@ 
          Texp_apply (frexp, [(Nolabel, Some foldfn); 
                              (Nolabel, Some ctxt_exp);
                              (Nolabel, Some bexp)]) in
  let inner_exp = match crdt with
    | CRInt -> fold_exp
    | CRSet -> exp_of @@ Texp_apply (exp_of_id @@ 
                                        Ident.create "compute_set", 
                                     [(Nolabel, Some fold_exp)]) in
  let vb = {vb_pat=ctxt_pat; vb_expr=get_exp; 
            vb_attributes=[]; vb_loc=Location.none} in
  let let_exp = exp_of @@ Texp_let (Nonrecursive, [vb],inner_exp) in
  let_exp

let transform_read (Fun.T {name; rec_flag; body; 
                           args_t; res_t}, label, crdt) wr_effs =
  let read_name = Ident.name name in
  let read_eff_name = String.capitalize_ascii read_name in
  let read_eff_id = Ident.create read_eff_name in
  let open TypedtreeMap in
  let map_exp ({exp_desc} as exp) = match exp_desc with
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2);
                      (Nolabel,Some e3)]) 
      when is_crtable_find e -> 
        let id_exp = parse_id_exp e2 in
        let new_exp = transform_crfind id_exp read_eff_id 
                          wr_effs label crdt in
        new_exp
    | _ -> exp in
  let module Mapper = MakeMap(struct
      include DefaultMapArgument
      let enter_expression = map_exp
    end) in
  let body' = Mapper.map_expression body in
  let _ = printf "Transformed read of %s:\n    %s\n"
            (Ident.name name) (pp_expr body') in
  Fun.make ~name:name ~rec_flag:rec_flag ~args_t:args_t 
            ~res_t:res_t ~body:body'


let mk_eff_cons_for_tmod ({rtype_dec; cr_funs} as tmod) =
  let wr_effs = List.map_some 
      (function 
        | Update annot_fn -> Some (eff_of_annot_upd annot_fn) 
        | Insert fn -> Some (eff_of_insert fn)
        | _ -> None) cr_funs in
  let read_funs = List.map_some
      (function 
        | Read annot_fn -> Some (transform_read annot_fn wr_effs)
        | _ -> None) cr_funs in
  ()

let compile ppf ({str_items; str_type; str_final_env}) = 
  let typedec_mod = find_typedec_mod str_items in
  let {str_items=type_decs} = structure_of_mod typedec_mod in
  let rtype_decs = filter_record_type_decs type_decs in
  let tables = get_table_types type_decs in
  (*let _ = printf "%d record types and %d tables\n" 
            (len rtype_decs) (len tables) in*)
  let (rtype_decs,db_type_dec) = 
    let (rtds,dbtds) = 
      List.partition 
        (fun {typ_name={txt=rtype_name}} -> 
           List.exists (fun (_,rtype_name') -> 
                          rtype_name=rtype_name') tables) 
        rtype_decs in
    let dbtd = match dbtds with
      | [dbtd] -> dbtd
      | [] -> failwith "Database type declaration not found"
      | _ -> failwith "Type declaration structure contains unknown\
                       \ items!" in
    (rtds,dbtd) in
  (* Map each table to the corresponding recorde typedec *)
  let tr_pairs = List.map 
        (fun (tname, rtype_name) -> 
           let rtype_dec = List.find 
                 (fun ({typ_name={txt=rtype_name'}}) -> 
                   rtype_name=rtype_name') rtype_decs in
           (tname,rtype_dec))
        tables in
  (* Find all table modules *)
  let tmods1 = filter_table_mods tr_pairs str_items in
  (*let _ = printf "%d table modules found\n" (len tmods1)  in*)
  let tmods2 = List.map classify_funs_in_tmod tmods1 in
  let tmods3 = List.map mk_eff_cons_for_tmod tmods2 in
  ()
