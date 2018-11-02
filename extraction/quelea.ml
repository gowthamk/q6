open Types
open Typedtree
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
  ()
