val specialize : Ast.pat -> Ast.tp -> unit Context.t
val lspecialize : Ast.pat -> Ast.tp -> unit Context.t
val specialize_set : Ast.pat list -> Ast.tp -> Ast.tp Context.t

val check : Ast.exp -> Ast.tp -> int -> Lambda.term Context.t
val lcheck : Ast.exp -> Ast.tp -> int -> Lambda.term Context.t

val synth : Ast.exp -> int -> (Ast.tp * Lambda.term) Context.t
val lsynth : Ast.exp -> int -> (Ast.tp * Lambda.term) Context.t

val cover : (Ast.exp -> Ast.tp -> int -> Lambda.term Context.t) ->
            (Ast.pat list * Ast.exp) list ->
            Ast.tp -> 
            int -> 
            Context.hyp list -> 
            (Lambda.term * Base.id list) Context.t


