open Misc
open Longident
open Path
open Types
open Outcometree
open Genprinti

(* take in the type and its environment and produce an intermediary x_value that
can be serialised and embedded as a lambda term into a compiled program. *)
    let xoutval_of_value env ty =

      let module TypeTbl = Hashtbl.Make(struct
        type t = Types.type_expr
        (* let equal = Ctype.moregeneral env false *)
        let equal = Ctype.matches env
        let hash x =
          try
            Hashtbl.hash x
          with _exn -> 0
      end)
      in
    let printers = [
      ( Predef.type_int, Xval_int );
      ( Predef.type_float, Xval_float );
      ( Predef.type_char, Xval_char );
      ( Predef.type_int32, Xval_int32 );
      ( Predef.type_nativeint, Xval_nativeint );
      ( Predef.type_int64, Xval_int64 );
      ] 
    in

    let tree_of_qualified lookup_fun env ty_path name =
      match ty_path with
      | Pident _ ->
          Oide_ident name
      | Pdot(p, _s, _pos) ->
          if try
               match (lookup_fun (Lident name) env).desc with
               | Tconstr(ty_path', _, _) -> Path.same ty_path ty_path'
               | _ -> false
             with Not_found -> false
          then Oide_ident name
          else Oide_dot (Printtyp.tree_of_path p, name)
      | Papply _ ->
          Printtyp.tree_of_path ty_path
    in
    let tree_of_constr =
      tree_of_qualified
        (fun lid env -> (Env.lookup_constructor lid env).cstr_res)

    and tree_of_label =
      tree_of_qualified (fun lid env -> (Env.lookup_label lid env).lbl_res)
    in
    (* An abstract type *)

    let abstract_type =
      Ctype.newty (Tconstr (Pident (Ident.create "abstract"), [], ref Mnil))
    in


      let types : x_value TypeTbl.t = TypeTbl.create 8 in


      (* let nest f = nest_gen (Oval_stuff "<cycle>") f in *)

      let rec tree_of_val ty : x_value =
        let ty = Ctype.repr ty in

        try 
          TypeTbl.find types ty
        with Not_found->
          let cell= ref Xval_int in
          TypeTbl.add types ty cell;
          let x= tree_of_val' ty in
          cell := x;
          (* TypeTbl.remove types ty; *)
          cell

      and tree_of_val' ty =
        let ty = Ctype.repr ty in

        begin
        try
          find_printer env ty
        with Not_found ->
          match ty.desc with
          | Tvar _ | Tunivar _ ->
              Xval_stuff "<poly>"
          | Tarrow _ ->
              Xval_stuff "<fun>"
          | Ttuple(ty_list) ->
              Xval_tuple (tree_of_val_list 0 ty_list)
          | Tconstr(path, [ty_arg], _)
            when Path.same path Predef.path_list ->

             Xval_list (tree_of_val ty_arg)

          | Tconstr(path, [ty_arg], _)
            when Path.same path Predef.path_array ->

             Xval_array (tree_of_val ty_arg)

          | Tconstr(path, [], _)
              when Path.same path Predef.path_string ->
            Xval_string Ostr_string

          | Tconstr (path, [], _)
              when Path.same path Predef.path_bytes ->
             Xval_string Ostr_bytes

          | Tconstr (path, [ty_arg], _)
            when Path.same path Predef.path_lazy_t ->

             let v=tree_of_val ty_arg in
             Xval_constr ([Oide_ident "lazy", [v]], false)

          | Tconstr(path, ty_list, _) -> begin
              try
                let decl = Env.find_type path env in
                match decl with
                | {type_kind = Type_abstract; type_manifest = None} ->
                    Xval_stuff "<abstr>"
                | {type_kind = Type_abstract; type_manifest = Some body} ->
                    !(tree_of_val
                      (try Ctype.apply env decl.type_params body ty_list with
                         Ctype.Cannot_apply -> abstract_type))
                | {type_kind = Type_variant constr_list; type_unboxed} ->
                   let unbx = type_unboxed.unboxed in

                   let extract {cd_id;cd_args;cd_res} =
                     let type_params =
                       match cd_res with
                         Some t ->
                          begin match (Ctype.repr t).desc with
                            Tconstr (_,params,_) ->
                             params
                          | _ -> assert false end
                       | None -> decl.type_params
                     in
                     let id,args=
                       match cd_args with
                       | Cstr_tuple l ->
                          let ty_args =
                            List.map
                              (function ty ->
                                         try Ctype.apply env type_params ty ty_list with
                                           Ctype.Cannot_apply -> abstract_type)
                              l
                          in
                          tree_of_constr_with_args (tree_of_constr env path)
                            (Ident.name cd_id) false 0
                            ty_args unbx
                       | Cstr_record lbls ->
                          let r =
                            tree_of_record_fields
                              env path type_params ty_list
                              lbls 0 unbx
                          in
                          (tree_of_constr env path
                             (Ident.name cd_id),
                           [ ref r ])
                     in
                     ( id,args )
                   in
                   let constr_list = List.map extract constr_list in
                   Xval_constr (constr_list,unbx)

                | {type_kind = Type_record(lbl_list, rep)} ->
                        let pos =
                          match rep with
                          | Record_extension -> 1
                          | _ -> 0
                        in
                        let unbx =
                          match rep with Record_unboxed _ -> true | _ -> false
                        in
                        tree_of_record_fields
                          env path decl.type_params ty_list
                          lbl_list pos unbx

                | {type_kind = Type_open} ->
                    (* tree_of_extension path depth *)
assert false
              with
                Not_found ->                (* raised by Env.find_type *)
                  Xval_stuff "<abstr>"
              end
          | Tvariant row ->
             let row = Btype.row_repr row in
             let find = fun (l,f) ->
               let h = Btype.hash_variant l in
               match Btype.row_field_repr f with
               | Rpresent(Some ty) | Reither(_,[ty],_,_) ->
                  let args =
                    tree_of_val ty
                  in
                  (h,(l, Some args))
               | _ -> (h,(l,None))
             in
             Xval_variant (List.map find row.row_fields)

          | Tobject (_, _) ->
              Xval_stuff "<obj>"
          | Tsubst ty ->
              !(tree_of_val ty)
          | Tfield(_, _, _, _) | Tnil | Tlink _ ->
              fatal_error "Genprint.outval_of_value"
          | Tpoly (ty, _) ->
              !(tree_of_val ty)
          | Tpackage _ ->
              Xval_stuff "<module>"
        end

      and tree_of_record_fields env path type_params ty_list 
          lbl_list pos unboxed : x_value' =
        let rec tree_of_fields pos = function
          | [] -> []
          | {ld_id; ld_type} :: remainder ->
              let ty_arg =
                try
                  Ctype.apply env type_params ld_type
                    ty_list
                with
                  Ctype.Cannot_apply -> abstract_type in
              let name = Ident.name ld_id in
              (* PR#5722: print full module path only
                 for first record field *)
              let lid =
                if pos = 0 then tree_of_label env path name
                else Oide_ident name
              and v =
                tree_of_val ty_arg
              in
              (lid, v) :: tree_of_fields (pos + 1) remainder
        in
        Xval_record (tree_of_fields pos lbl_list, pos, unboxed)

      and tree_of_val_list _start ty_list : x_value list =
        let rec tree_list = function
          | [] -> []
          | ty :: ty_list ->
              let tree = tree_of_val ty in
              tree :: tree_list  ty_list in
        tree_list ty_list

      and tree_of_constr_with_args
             tree_of_cstr cstr_name inlined start ty_args unboxed =
        let lid = tree_of_cstr cstr_name in
        let args =
          if inlined || unboxed then
            match ty_args with
            | [ty] -> [ tree_of_val ty ]
            | _ -> assert false
          else
            (tree_of_val_list start ty_args : x_value list)
        in
        (lid, args)

    and find_printer env ty =
      let rec find = function
      | [] -> raise Not_found
      | (sch, printer) :: remainder ->
          if Ctype.moregeneral env false sch ty
          then printer
          else find remainder
      in
      find printers


    in tree_of_val ty


let type_to_lambda (ty,env)=
  let x_val=xoutval_of_value env ty in
  let x_serde= Marshal.to_string x_val [] in
(* pp "MARSHAL: %d" (String.length x_serde); *)
  let lam = Lambda.(Lconst(Const_immstring x_serde)) in
  (* return a serialisation of the Xval *)
  lam

let _=
  Translprim.register_typeof_func ~path:"Genprint.prs" type_to_lambda
