open Types
open Typedtree
open Rdtspec
open Utils
open Speclang

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
        (* let _ = Printf.printf "%s is tt? %b\n" name is_ttype_mod in *)
          if is_ttype_mod then (name,this_mod)::nested_mods 
          else nested_mods 
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items

let schema_of_mod ppf (mod_name: Ident.t) (mod_exp :Typedtree.module_expr) 
      : Tableschema.t = 
  let rec doIt_core_type_desc (ctyp_desc) : Coltype.t = 
    match ctyp_desc with
      | Ttyp_constr (path,longident,_) -> 
          let path_str = Printtyp.string_of_path path in
          let coltype_of_str str = match Str.split (Str.regexp "\.") path_str with
            | ["id"] -> Coltype.Fkey mod_name
            | [table_name;"id"] -> Coltype.Fkey (Ident.create table_name)
            | _ -> failwith ("coltype_of_str ("^str^"): Unimpl.") in
            begin
              match path_str with 
                | "string" -> Coltype.String | "int" -> Coltype.Int
                | "Uuid.t" -> Coltype.UUID 
                | _ -> coltype_of_str path_str
            end
      | Ttyp_poly (_,core_t) -> doIt_core_type_desc core_t.ctyp_desc
      | _ -> failwith "doIt_label_dec: Unimpl." in
      
  let doIt_label_dec ({ld_name; ld_type = {ctyp_desc}}) 
        : (Ident.t*Coltype.t) = 
    let arg_id = let open Asttypes in Ident.create ld_name.txt in
    (* let _ = Printf.printf "arg_id: %s\n" @@ Ident.name arg_id in *)
    let arg_t = doIt_core_type_desc ctyp_desc in
       (arg_id,arg_t) in
  let doIt_cons_decl {cd_name; cd_args} = 
    let name = let open Asttypes in Ident.create cd_name.txt in
    let label_decs = match cd_args with 
      | Cstr_record d -> d
      | Cstr_tuple [] -> []
      | Cstr_tuple _ -> failwith "Efftype cons should take a record" in
    let args_t = List.map doIt_label_dec label_decs in
      Effcons.make ~name:name ~args_t:args_t in
  let doIt_if_id {typ_name; typ_manifest} = 
    let open Asttypes in
      match typ_name.txt with
        | "id" -> 
            let core_t = match typ_manifest with 
              | Some c -> c | None -> failwith "Id type has to manifest"  in
            let (path,long_ident) = match core_t.ctyp_desc with 
              | Ttyp_constr (a,b,_) -> (a,b) 
              | _ -> failwith "doIt_if_id: Unimpl." in
            let id_t = let open Path in match path with
              | Pident id when (Ident.name id = "string") -> Coltype.String 
              | Pident id when (Ident.name id = "int") -> Coltype.Int 
              | Pident id when (Ident.name id = "bool") -> Coltype.Bool 
              | Pident id -> failwith @@ "Unknown id type: "^(Ident.name id)
              | Pdot (Pident id,"t",_) when (Ident.name id = "Uuid") -> Coltype.UUID
              | Pdot (Pident id,"id",_) -> Coltype.Fkey id
              | p -> failwith @@ 
                        "Invalid id type: "^(Printtyp.string_of_path p) in
              [id_t]
        | _ -> [] in
  let doIt_if_eff {typ_name; typ_kind} = 
    let open Asttypes in
      match typ_name.txt with
        | "eff" -> 
            let cons_decls = match typ_kind with
              | Ttype_variant c -> c 
              | _ -> failwith "Efftype kind has to be a variant" in
            let effconss = List.map doIt_cons_decl cons_decls in
              [effconss]
        | _ -> [] in
  let doIt_item_desc f = function 
      Tstr_type (_,type_decls) -> List.concat @@ List.map f type_decls
    | _ -> [] in
  let str_items = match mod_exp.mod_desc with 
    | Tmod_structure struc -> struc.str_items
    | _ -> failwith "Table type definition needs to be a structure" in
  let id_t = List.hd @@ List.concat @@ 
                  List.map (fun item -> doIt_item_desc doIt_if_id item.str_desc) 
                    str_items in 
  let eff_t = List.hd @@ List.concat @@ 
                  List.map (fun item -> doIt_item_desc doIt_if_eff item.str_desc) 
                    str_items in 
    Tableschema.make ~id_t: id_t ~eff_t:eff_t

let extract_funs (str_items) = 
  let (reads, writes, invs, aux) = (ref [], ref [], ref [], ref []) in
  let open Asttypes in
  let doIt_valbind rec_flag {vb_pat; vb_expr} = 
    match (vb_pat.pat_desc, vb_expr.exp_desc) with 
      | (Tpat_var (_,loc), Texp_function (_,[case],_)) -> 
          let mk_fun () = 
            let (args,body) = Misc.extract_lambda case in
            let open Types in
            let arrow_t = vb_expr.exp_type.desc in
            let (arg_ts,res_t) = Misc.uncurry_arrow arrow_t in
            (*VERRRRRRRY DIRTY HACK. FIX IT!*)
            (* For some reason, when a function has > 2 args, arg_ts doesn't get any arguments after the second one*)
            (* Making arg_ts and arg the same length, by appending the type of the last arg to arg_ts*)
            let rec hack_arg_ts arg_ts arg len =
              if List.length arg_ts = len then arg_ts else hack_arg_ts (arg_ts@[arg]) arg len in
            let arg_ts' = if (List.length args) = (List.length arg_ts) then arg_ts else hack_arg_ts arg_ts (List.hd (List.rev arg_ts)) (List.length args) in
            (*DIRTY HACK ENDS*) 
              Fun.make ~name: (Ident.create loc.txt) 
                   ~rec_flag: rec_flag
                   ~args_t: (List.zip args arg_ts') 
                   ~res_t: res_t ~body: body in
            if String.length loc.txt >= 4 && 
               Str.string_before loc.txt 4 = "get_" then
              reads := (mk_fun ())::!reads
            else if String.length loc.txt >= 3 && 
                    Str.string_before loc.txt 3 = "do_" then
              writes := (mk_fun ())::!writes
            else if String.length loc.txt >= 4 && 
                    Str.string_before loc.txt 4 = "inv_" then
              invs := (mk_fun ())::!invs
            else aux := (mk_fun ())::!aux
      | _ -> () in
    begin
      List.iter (fun {str_desc} -> match str_desc with
                   | Tstr_value (rec_flag,valbinds) -> 
                       let open Asttypes in 
                       let rec_flag = match rec_flag with 
                         | Nonrecursive -> false
                         | Recursive -> true in
                         (*let _ = printf "Valbinds:%d\n" (List.length valbinds) in*)
                         List.iter (doIt_valbind rec_flag) valbinds
                   | _ -> ()) str_items;
      (!reads, !writes, !invs, !aux)
    end

let extract_aux_mods str_items ttype_names = 
  let is_table_mod name = 
    let tokens = Str.split (Str.regexp "_") name in
      (List.length tokens >= 2) && (List.hd (List.rev tokens) = "table") in
  let is_ttype_mod name = List.mem name ttype_names in
  let doIt_item_desc = function 
      Tstr_module mod_bind ->
        let name = let open Asttypes in mod_bind.mb_name.txt in
        let this_mod = mod_bind.mb_expr in
          if is_table_mod name || is_ttype_mod name 
          then []
          else [(name,this_mod)]
    | _ -> [] in
      List.concat @@ 
        List.map (fun item -> 
                    doIt_item_desc item.str_desc) str_items

let doIt ppf ({str_items; str_type; str_final_env}) = 
  let ttype_paths = extract_ttype_paths str_items in
  (* let _ = print_string "Table Type paths:\n" in*)
  let ttype_names = List.map
            (fun path -> 
               let name = Printtyp.string_of_path path in
               (* let _ = Printf.printf "%s\n" name in*)
                  name) ttype_paths in
  let ttype_mods = extract_ttype_mods ttype_names str_items in
  let ttype_schemas = List.map 
                        (fun (name,mod_exp) -> 
                           let mod_name = Ident.create name in
                           let schema = schema_of_mod ppf mod_name mod_exp in
                            (mod_name, schema)) 
                        ttype_mods in
  let (reads,writes,invs,aux) = extract_funs str_items in
  let aux_mods = extract_aux_mods str_items ttype_names in
  let new_aux = 
    List.concat @@ List.map
       (fun (mod_name,mod_exp) -> 
          let str_items = match mod_exp.mod_desc with 
            | Tmod_structure struc -> struc.str_items
            | _ -> failwith "Aux mod isn't a structure" in
          let rename_fun (Fun.T fun_t) =  
            Fun.T {fun_t with name = Ident.create @@ 
                              mod_name^"."^(Ident.name fun_t.name)} in
          let (x,y,i,z) = extract_funs str_items in
          let new_funs = List.map rename_fun (x @ y @ i @ z) in
            new_funs) aux_mods in
  let print_fname (name,expr) = Printf.printf "%s\n" name in
  let rdt_spec = Rdtspec.make ~schemas: ttype_schemas ~reads: reads
                   ~writes:writes ~aux:(aux @ new_aux) ~invs:invs in
    begin
      rdt_spec
     (* print_string "Reads:\n";
      List.iter print_fname reads;
      print_string "Writes:\n";
      List.iter print_fname writes;
      print_string "Auxiliary functions:\n";
      List.iter print_fname aux; *)
      (* Printtyp.signature ppf str_type; *)
    end
