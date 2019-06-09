(* abstracted type for ocaml type representation *)
type t = int


(* a registry of types and their environments *)
let tyhash=Hashtbl.create 5

(* record the type/env and return the hash for later retrieval *)
let create_key_for_type (ty,env)=
  let h=Hashtbl.hash ty in
  Hashtbl.add tyhash h (ty,env);
  Lambda.(Lconst(Const_pointer h))
  (* now string to be compat with compiler version... but no need, make abstract in mli.*)
  (* Lambda.(Lconst(Const_immstring (string_of_int h))) *)

(*
  let outv = outval_of_value env v ty in
  let pty = Printtyp.tree_of_type_scheme ty in
  let it = Outcometree.Ophr_eval (outv, pty) in
  !Toploop.print_out_phrase ppf it
*)

let max_printer_depth = ref !Toploop.max_printer_depth
let max_printer_steps = ref !Toploop.max_printer_steps
let ppf= ref Format.std_formatter

(* the print format is limited and ugly - ideal for dissuading users from actually using this
for anything other than debugging. *)
external prs: string -> 'a -> unit = "%typeof" (* fake primitive used so as to not slow down the compiler in general. *)
(* the above fake primitive gets redirected here: *)
let prs_with_type tyh s v =
  let ty,env=
    try
      Hashtbl.find tyhash (tyh)
  with Not_found->
    failwith "unknown type key. Cannot use toplevel with the compiler."
  in
  let ppf = ! ppf in
  Format.fprintf ppf "%s =>\n" s;
  Toploop.print_value env v ppf ty;
  Format.fprintf ppf "@."

(* this will overwrite the internal handler of this name if present *)
let _=
  Translprim.register_typeof_func ~path:"Genprint.prs" create_key_for_type

