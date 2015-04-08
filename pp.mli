type printer

val nl     : printer
val nil    : printer
val str    : string -> printer
val int    : int -> printer
val float  : float -> printer
val bool   : bool -> printer
val qstr   : string -> printer
val atcol  : printer -> printer
val indent : int -> printer -> printer
val seq    : printer list -> printer
val break  : bool -> printer
val multiline : printer -> bool

val print : printer -> out_channel -> unit 




















