val wellsorted   : Ast.kind -> unit Context.t
val subkind      : Ast.kind -> Ast.kind -> unit Context.t 

val synth_kind   : Ast.tp -> (Ast.tp * Ast.kind) Context.t
val check_kind   : Ast.tp -> Ast.kind -> Ast.tp Context.t

val atomic       : Ast.tp -> bool
val whnf         : Ast.tp -> Ast.tp Context.t
val reduce_spine : Ast.kind -> Ast.tp -> Ast.tp list -> Ast.tp Context.t 




















