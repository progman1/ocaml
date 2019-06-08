open Outcometree

type x_value = x_value' ref
and x_value' =
  | Xval_array of x_value
  | Xval_char
  | Xval_constr of (out_ident * x_value list) list * bool
  | Xval_ellipsis
  | Xval_float
  | Xval_int
  | Xval_int32
  | Xval_int64
  | Xval_nativeint
  | Xval_list of x_value
  | Xval_record of (out_ident * x_value) list * int * bool
  | Xval_string of out_string (* string, size-to-print, kind *)
  | Xval_stuff of string
  | Xval_tuple of x_value list
  | Xval_variant of (int * (Asttypes.label * x_value option)) list

