open Asttypes
open Path
open Types
open Typedtree
open Speclang
open Rdtspec
open Utils
open Printf

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
 * annotated with the label (ld_id) of the CRDT type it reads/writes.
 *)
type crdt = CRInt | CRSet 

type annot_fun = Fun.t * Ident.t * crdt

type cr_fun = Read of annot_fun
            | Write of annot_fun
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

let classify_fun_in_tmod (({rtype_dec} as tmod):tmod1)
                         (Fun.T {name; body} as fun_t) =
  let fn_name = Ident.name name in
  let get_crtable_fn {exp_desc}= match exp_desc with
    | Texp_ident (Pdot (Pdot (Pident id, 
                              "CRTable",_),crfn,_),_,_) 
      when Ident.name id = "Crdts" -> Some crfn
    | _ -> None in
  let is_crtable_find e = match get_crtable_fn e with
    | Some "find" -> true 
    | _ -> false in
  let is_crtable_update e = match get_crtable_fn e with
    | Some "update" -> true
    | _ -> false in
  let is_crtable_insert_or_delete e = 
    match get_crtable_fn e with
      | Some "insert" | Some "delete" -> true
      | _ -> false in
  let open TypedtreeIter in
  let iter_exp ({exp_desc} as exp) = match exp_desc with
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2); 
                      (Nolabel,Some e3)]) ->
      if is_crtable_find e then printf "%s is read fn\n" fn_name
      else if is_crtable_update e then printf "%s is write fn\n" fn_name
      else ()
    | Texp_apply (e, [(Nolabel,Some e1); 
                      (Nolabel,Some e2)]) 
      when is_crtable_insert_or_delete e ->
        printf "%s is write fn\n" fn_name
    | _ -> ()(*Printtyped.expression 0 Format.str_formatter exp*) in
  let module Iterator = MakeIterator(struct
      include DefaultIteratorArgument
      let enter_expression = iter_exp
    end) in
  let _ = Iterator.iter_expression body in
  ()

let classify_funs_in_tmod ({structure={str_items}} as tmod) = 
  let get_if_val_bind {str_desc} = match str_desc with
    | Tstr_value (Recursive, [val_bind]) -> Some (true, val_bind)
    | Tstr_value (_, [val_bind]) -> Some (false, val_bind)
    | _ -> None in
  let val_binds = List.map_some get_if_val_bind str_items in
  let funs = List.map_some get_fun_if_fun_bind val_binds in
  let _ = printf "%s has %d funs\n" (tmod.name) (len funs) in
  let _ = List.iter (classify_fun_in_tmod tmod) funs in
  {name=tmod.name; tname=tmod.tname; rtype_dec=tmod.rtype_dec; 
   cr_funs=[]}

let compile ppf ({str_items; str_type; str_final_env}) = 
  let typedec_mod = find_typedec_mod str_items in
  let _ = printf "Typedec mod is %s\n" 
            @@ Ident.name typedec_mod.mb_id in
  let {str_items=type_decs} = structure_of_mod typedec_mod in
  let rtype_decs = filter_record_type_decs type_decs in
  let tables = get_table_types type_decs in
  let _ = printf "%d record types and %d tables\n" 
            (len rtype_decs) (len tables) in
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
  let _ = printf "%d table modules found\n" (len tmods1)  in
  let tmods2 = List.map classify_funs_in_tmod tmods1 in
  ()
