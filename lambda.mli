type term =
  | Var of Base.id
  | Lam of Base.id * term
  | LitNum of float
  | LitBool of bool
  | LitString of string 
  | App of term * term
  | Oper of Base.op * term * term 
  | If of term * term * term
  | Tuple of term list
  | Project of int * term
  | Let of Base.id * term * term
  | Fix of Base.id * Base.id * term
  | Lazyfix of Base.id * term 
  | Cons of term * term
  | Head of term
  | Tail of term
  | Lazy of term
  | Force of term
  | Thunk of term 
  | Run of term 
  | Con of Base.conid * term
  | Merge of term * term 
  | Case of term * (Base.conid * Base.id * term) list 

val let_tuple : Base.id list -> Base.id -> term -> term
val let_lazy_tuple : Base.id list -> Base.id -> term -> term
val let_stream : Base.id * Base.id -> Base.id -> term -> term
val let_dom : Base.id * Base.id -> Base.id -> term -> term
val rename_term : Base.id -> Base.id -> term -> term 

val print_term : Format.formatter -> term -> unit

val fact : term
val fact_tr : term
val countdown : term














