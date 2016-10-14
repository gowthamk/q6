open Typedtree

(* 
 * Extract module paths of TABLE_TYPE signature for which a 
 * store interface exists.
 *)
let rec extract_ttype_paths str_items = 
  let doIt_module_expr_desc = function 
      Tmod_apply (funct,arg,_) -> 
        (match (funct.mod_desc,arg.mod_desc) with 
           | (Tmod_ident (fpath,_), Tmod_ident (apath,_)) ->
               let fstr = Printtyp.string_of_path fpath in
                 if fstr = "Store_interface.Make" then [apath] else []
           |  _ -> [])
    | Tmod_structure struc -> extract_ttype_paths struc.str_items
    | _ -> failwith "AUnimpl." in
  let doIt_item_desc = function Tstr_open open_desc -> []
    | Tstr_include include_decl -> 
        doIt_module_expr_desc include_decl.incl_mod.mod_desc
    | Tstr_module mod_bind -> 
        doIt_module_expr_desc mod_bind.mb_expr.mod_desc
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items

(*
 * Extract module definitions of the given TABLE_TYPEs.
 *)
let rec extract_ttype_mods ttype_names str_items = 
  let doIt_module_expr_desc = function
      Tmod_structure struc -> extract_ttype_mods 
                                ttype_names struc.str_items
    | _ -> [] in
  let doIt_item_desc = function 
      Tstr_module mod_bind ->
        let name = let open Asttypes in mod_bind.mb_name.txt in
        let this_mod = mod_bind.mb_expr in
        let nested_mods = doIt_module_expr_desc 
                            mod_bind.mb_expr.mod_desc in
        let is_ttype_mod = List.mem name ttype_names in
        let _ = Printf.printf "%s is tt? %b\n" name is_ttype_mod in
          if is_ttype_mod then (name,this_mod)::nested_mods 
          else nested_mods 
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items

let rec extract_fun {c_lhs; c_rhs} = 
  let open Asttypes in
  match (c_lhs.pat_desc, c_rhs.exp_desc) with
    | (Tpat_var (_,loc), Texp_function (_,[case],_)) -> 
        let (args,body) = extract_fun case in
          (loc.txt::args,body)
    | (Tpat_var (_,loc), body) -> ([loc.txt], body)
    | _ -> failwith "Unimpl."

let extract_funs (str_items) = 
  let (reads, writes, aux) = (ref [], ref [], ref []) in
  let open Asttypes in
  let doIt_valbind {vb_pat; vb_expr} = 
    match (vb_pat.pat_desc, vb_expr.exp_desc) with 
      | (Tpat_var (_,loc), Texp_function (_,[case],_)) -> 
          if String.length loc.txt >= 4 && 
             Str.string_before loc.txt 4 = "get_" then
            reads := (loc.txt, extract_fun case)::!reads
          else if String.length loc.txt >= 3 && 
                  Str.string_before loc.txt 3 = "do_" then
            writes := (loc.txt, extract_fun case)::!writes
          else aux := (loc.txt, extract_fun case)::!aux
      | _ -> () in
    begin
      List.iter (fun {str_desc} -> match str_desc with
                   | Tstr_value (_,valbinds) -> 
                       List.iter doIt_valbind valbinds
                   | _ -> ()) str_items;
      (!reads, !writes, !aux)
    end

let doIt ppf ({str_items; str_type; str_final_env}) = 
  let ttype_paths = extract_ttype_paths str_items in
  let _ = print_string "Table Type paths:\n" in
  let ttype_names = List.map
            (fun path -> 
               let name = Printtyp.string_of_path path in
               let _ = Printf.printf "%s\n" name in
                  name) ttype_paths in
  let ttype_mods = extract_ttype_mods ttype_names str_items in
  let (reads,writes,aux) = extract_funs str_items in
  let print_fname (name,expr) = Printf.printf "%s\n" name in
    begin
      print_string "Reads:\n";
      List.iter print_fname reads;
      print_string "Writes:\n";
      List.iter print_fname writes;
      print_string "Auxiliary functions:\n";
      List.iter print_fname aux;
      (* Printtyp.signature ppf str_type; *)
    end
