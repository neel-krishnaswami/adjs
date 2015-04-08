type result = Success | Failure of string | Crash of exn
type t 

val test : string -> (unit -> bool) -> t
val fulltest : string -> (unit -> result) -> t
val crashtest : string -> (unit -> 'a) -> (exn -> bool) -> t 
val group : string -> t list -> t

val run : Format.formatter -> t -> unit  
