(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*  Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt  *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* To print values *)

open Types
open Outcometree
open Genprinti

(* abstracted type for ocaml type representation *)
type t = string

(* let pp fmt = Printf.kfprintf (fun ch-> Printf.fprintf ch "\n"; flush stdout) stdout fmt *)



(* an intermediate repr prior to Outcometree.out_value that allows to eliminate the
type and its environment without yet supplying the obj for decomposing.
a further stage then uses it to guide decomposition of an obj, turns out an outcome for Oprint to
handle as before. 

the value is no longer being used to drive the unfolding of its type structure - the x_value is
doing it and that means it must capture the recursion of the underlying types.
the mutable reference is used to encode cyclicity.

replacing the tree-walking function outval_of_value with a data structure allows its easy embedding
into lambda, in contrast to the toplevel version which more simply records the type/env and stores
a key to it in the program lambda.
 *)

module type OBJ =
  sig
    type t
    val repr : 'a -> t
    val obj : t -> 'a
    val is_block : t -> bool
    val tag : t -> int
    val size : t -> int
    val field : t -> int -> t
    val double_array_tag : int
    val double_field : t -> int -> float
  end



(********************************************************************************)
module Make(O : OBJ) = struct

    (* type t = O.t *)

    module ObjTbl = Hashtbl.Make(struct
        type t = O.t
        let equal = (==)
        let hash x =
          try
            Hashtbl.hash x
          with _exn -> 0
      end)


   
    (* The main printing function *)

    let outval_of_value max_steps max_depth check_depth obj x =

      let printer_steps = ref max_steps in

      let nested_values = ObjTbl.create 8 in
      let nest_gen err f depth obj x =
        let repr = obj in
        if not (O.is_block repr) then
          f depth obj x
        else
          if ObjTbl.mem nested_values repr then
            err
          else begin
            ObjTbl.add nested_values repr ();
            let ret = f depth obj x in
            ObjTbl.remove nested_values repr;
            ret
          end
      in

      let nest f = nest_gen (Oval_stuff "<cycle>") f in

      let rec find_constr tag num_const num_nonconst = function
          [] ->
           raise Not_found
        | _, [] as c  :: rem ->
           if tag = Cstr_constant num_const
           then c
           else find_constr tag (num_const + 1) num_nonconst rem
        | c :: rem ->
           if tag = Cstr_block num_nonconst || tag = Cstr_unboxed
           then c
           else find_constr tag num_const (num_nonconst + 1) rem
      in
      let find_constr_by_tag tag cstrlist =
        find_constr tag 0 0 cstrlist
      in

      let rec tree_of_val depth obj x_val =
        decr printer_steps;
        if !printer_steps < 0 || depth < 0 then Oval_ellipsis
        else begin
            match x_val with
            | Xval_ellipsis -> Oval_ellipsis

            | Xval_int -> Oval_int (O.obj obj)
            | Xval_float -> Oval_float (O.obj obj)
            | Xval_char-> Oval_char (O.obj obj)
            | Xval_int32-> Oval_int32 (O.obj obj)
            | Xval_nativeint -> Oval_nativeint (O.obj obj)
            | Xval_int64 -> Oval_int64 (O.obj obj)

            | Xval_stuff s ->
               Oval_stuff s
            | Xval_tuple(x_val_list) ->
               Oval_tuple (tree_of_val_list 0 depth obj x_val_list)
            | Xval_list x_arg ->
               if O.is_block obj then
                 match check_depth depth obj x_val with
                   Some x -> x
                 | None ->
                    let rec tree_of_conses tree_list depth obj x_arg =
                      if !printer_steps < 0 || depth < 0 then
                        Oval_ellipsis :: tree_list
                      else if O.is_block obj then
                        let tree =
                          nest tree_of_val (depth - 1) (O.field obj 0) x_arg
                        in
                        let next_obj = O.field obj 1 in
                        nest_gen (Oval_stuff "<cycle>" :: tree :: tree_list)
                          (tree_of_conses (tree :: tree_list))
                          depth next_obj x_arg
                      else tree_list
                    in
                    Oval_list (List.rev (tree_of_conses [] depth obj !x_arg))
               else
                 Oval_list []
            | Xval_array x_arg ->
               let length = O.size obj in
               if length > 0 then
                 let rec tree_of_items tree_list i =
                   if !printer_steps < 0 || depth < 0 then
                     Oval_ellipsis :: tree_list
                   else if i < length then
                     let tree =
                       nest tree_of_val (depth - 1) (O.field obj i) !x_arg
                     in
                     tree_of_items (tree :: tree_list) (i + 1)
                   else tree_list
                 in
                 Oval_array (List.rev (tree_of_items [] 0))
               else
                 Oval_array []

            | Xval_string Ostr_string ->
               Oval_string ((O.obj obj : string), !printer_steps, Ostr_string)

            | Xval_string Ostr_bytes ->
               let s = Bytes.to_string (O.obj obj : bytes) in
               Oval_string (s, !printer_steps, Ostr_bytes)

            | Xval_constr ([Oide_ident "lazy",[x_arg]],_) -> 
               let obj_tag = O.tag obj in
               if obj_tag = Obj.lazy_tag then Oval_stuff "<lazy>"
               else begin
                   let forced_obj =
                     if obj_tag = Obj.forward_tag then O.field obj 0 else obj
                   in
                   let v =
                     if obj_tag = Obj.forward_tag
                     then nest tree_of_val depth forced_obj !x_arg
                     else      tree_of_val depth forced_obj !x_arg
                   in
                   Oval_constr (Oide_ident "lazy", [v])
                 end
            | Xval_constr (cl,unbx) ->begin
               let tag =
                 if unbx then Cstr_unboxed
                 else if O.is_block obj
                 then Cstr_block(O.tag obj)
                 else Cstr_constant(O.obj obj)
               in

               try
                 let lid,x_args =
                   find_constr_by_tag tag cl in
                 let o_arg =

                   match x_args with
                   | [{contents=Xval_record (ixl,_,_)}] ->
                      let x = tree_of_record_fields depth ixl 0 obj unbx in
                      Oval_constr (lid, [x])

                   | _->
                      tree_of_constr_with_args
                        lid false 0 depth obj
                        x_args unbx
                 in
                 (* Oval_constr(lid, o_args) *)
                 o_arg
               with
                 Not_found ->
                  Oval_stuff "<unknown constructor>"
              end

            | Xval_record (ixl,pos,unbx) ->
                  tree_of_record_fields depth ixl pos obj unbx

               (*
                | {type_kind = Type_open} ->
                    tree_of_extension path depth obj
                *)

            | Xval_variant vl ->
               try
                 if O.is_block obj then
                   let tag : int = O.obj (O.field obj 0) in
                   let lid,x_arg = List.assoc tag vl in
                   match x_arg with 
                   | Some x_arg ->
                      let o_args =
                        nest tree_of_val (depth - 1) (O.field obj 1) !x_arg
                      in
                      Oval_variant (lid, Some o_args)
                   | None -> assert false

                 else
                   let tag : int = O.obj obj in
                   let lid,x_arg = List.assoc tag vl in
                   assert (x_arg=None);
                   Oval_variant (lid,None)

               with Not_found->
                 Oval_stuff "<variant>"

          end

      and tree_of_record_fields depth x_args pos obj unboxed =
        let rec tree_of_fields pos = function
          | [] -> []
          | (lid, x_arg) :: remainder ->
              let v =
                if unboxed then
                  tree_of_val (depth - 1) obj !x_arg
                else begin
                  let fld =
                    if O.tag obj = O.double_array_tag then
                      O.repr (O.double_field obj pos)
                    else
                      O.field obj pos
                  in
                  nest tree_of_val (depth - 1) fld !x_arg
                end
              in
              (lid, v) :: tree_of_fields (pos + 1) remainder
        in
        Oval_record (tree_of_fields pos x_args)

      and tree_of_val_list start depth obj x_args =
        let rec tree_list i = function
          | [] -> []
          | x_arg :: x_args ->
              let tree = nest tree_of_val (depth - 1) (O.field obj i) !x_arg in
              tree :: tree_list (i + 1) x_args in
      tree_list start x_args

      and tree_of_constr_with_args
             lid _inlined start depth obj x_args _unboxed =
        let o_args = tree_of_val_list start depth obj x_args in
        Oval_constr (lid, o_args)

    in
    nest tree_of_val max_depth obj !x

end


(********************************************************************************)


module LocalPrinter = Make(Obj)

let max_printer_depth = ref 100
let max_printer_steps = ref 300
let ppf= ref Format.std_formatter


(* 2-stages: 1st convert to Xval data structure, 2nd convert Xval to Oval *)
let outval_of_value obj x =
  LocalPrinter.outval_of_value !max_printer_steps !max_printer_depth
    (fun _ _ _ -> None) obj x
let print_value obj ppf x =
  !Oprint.out_value ppf (outval_of_value obj x)


(* the print format is limited and ugly - ideal for dissuading users from actually using this
for anything other than debugging. *)
external prs: string -> 'a -> unit = "%typeof"
(* the above fake primitive gets redirected here (path with [_with_type] tacked on): *)
let prs_with_type x s v =
  let ppf = !ppf in
  let unser= Marshal.from_string x 0 in
  Format.fprintf ppf "%s =>\n" s;
  print_value v ppf unser;
  Format.fprintf ppf "@."

