val max_printer_depth : int ref
val max_printer_steps : int ref
val ppf : Format.formatter ref

external prs : string -> 'a -> unit = "%typeof"
val prs_with_type : string -> string -> Obj.t -> unit
