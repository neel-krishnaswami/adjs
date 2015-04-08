type sort = Univ | Exist
type usage = Used | Fresh
type stability = Dyn | Stable

type hyp =
  | Kind of sort * Ast.kind option 
  | Type of sort * Ast.kind * Ast.tp option
  | Hyp of stability * Ast.tp * int
  | Data of Ast.datatype
  | LHyp of Ast.tp * int * usage
  | HideLinear
  | HideDynamic 

type ctx = (Base.id * hyp) list 

type 'a return = Value of 'a | Error of string
type state = {ctx : ctx; sym : int; pos : Base.pos}
type 'a t = Ctx of (state -> ('a * state) return)

val return : 'a -> 'a t
val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
val ( >> ) : unit t -> 'a t -> 'a t

val seq : 'a t list -> 'a list t
val error : ('a, unit, string, 'b t) format4 -> 'a
val orelse : 'a t -> 'a t -> 'a t
val newid : Base.id -> Base.id t
val push : Base.id * hyp -> unit t
val pop : Base.id -> unit t
val before : Base.id -> 'a t -> 'a t


val get : ctx t
val set : ctx -> unit t
val setpos : Base.pos -> unit t
val with_pure_ctx : 'a t -> 'a t
val with_empty_lctx :  'a t -> 'a t
val with_nonlinear : 'a t -> 'a t
val parallel :  'a t list -> 'a list t
val with_hyp :  Base.id * hyp -> 'a t -> 'a t

val lookup :  Base.id -> hyp t

val update_eqn :  Base.id -> ctx -> unit t
val tp_subst : Ast.tp -> Base.id -> Ast.tp -> Ast.tp t

val subst_kind : Ast.kind -> Ast.kind t 
val subst : Ast.tp -> Ast.tp t

val fresh : (Base.id -> Base.id -> 'a -> 'b) -> Base.id -> 'a -> (Base.id * 'b) t

val compatible : ctx -> ctx -> Base.id option

val lookup_datatype :
   Base.id * Ast.tp list -> (Base.conid * Ast.tp) list t
val lookup_datatype_by_con :
   Base.conid -> (Base.id * Base.id list) t
val advance :
   Base.Ids.t -> Lambda.term -> int -> Lambda.term t
val run : 'a t -> ctx -> Base.pos -> ('a * ctx) return













