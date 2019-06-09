val max_printer_depth : int ref
val max_printer_steps : int ref
val ppf : Format.formatter ref

(* [prs msg value] prints an arbitrary value, and <poly> for those parts yet polymorphic *)
external prs : string -> 'a -> unit = "%typeof"
(* abstracted type for ocaml type representation *)
type t
val prs_with_type : t -> string -> Obj.t -> unit
