(* [prs msg value] prints an arbitrary value, and <poly> for those parts yet polymorphic *)
external prs : string -> 'a -> unit = "%typeof"
val prs_with_type : int -> string -> Obj.t -> unit

(* depth/steps initialised from Toploop versions *)
val max_printer_depth : int ref
val max_printer_steps : int ref
(* initialised to std_formatter *)
val ppf : Format.formatter ref
