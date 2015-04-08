type id = string
type conid = string 

type op = Plus | Minus | Times | Equal | Lt | Leq | Gt | Geq | And | Or

val print_op : op -> string 

type pos = Lexing.position * Lexing.position 
val dummy_pos : pos 

val print_pos : Format.formatter -> pos -> unit  
val string_of_pos : pos -> string 
val merge : pos * pos -> pos 

exception SyntaxError of pos * string 

val map : ('a -> 'b) -> 'a list -> 'b list
val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list 
val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
val foldr2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val fail_map : ('a -> 'b option) -> 'a list -> 'b list option 
val opt_find : ('a -> 'b option) -> 'a list -> 'b option
val opt_fold : ('a -> 'b) -> 'b -> 'a option -> 'b
val break_list : int -> 'a list -> 'a list * 'a list 
val length : 'a list -> int 

val fmt_id : unit -> string -> string
val fmt_pos : unit -> pos -> string 


module Ids : Set.S with type elt = id 










