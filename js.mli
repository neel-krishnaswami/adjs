type exp =
  | Int of int 
  | Num of float
  | Bool of bool
  | Fun of Base.id option * Base.id list * statement list
  | String of string
  | Id of Base.id
  | Apply of exp * exp list
  | Op of Base.op * exp * exp
  | Array of exp list
  | Deref of exp * exp
  | Method of exp * string * exp list
  | New of string * exp list 

and statement =
  | LetNull of Base.id 
  | LetVar of Base.id * exp
  | LetDef of Base.id * exp 
  | Return of exp
  | IfThenElse of exp * statement list * statement list
  | Assign of Base.id * exp
  | WhileTrue of statement list
  | Continue
  | Abort
  | Break 
  | Switch of exp * (Base.conid * statement list) list 


type 'a optree = Leaf of 'a | Node of Base.op * 'a optree * 'a optree
val opify : exp -> exp optree
val precedence : Base.op -> int
val print_operator : ('a -> Pp.printer) -> 'a optree -> Pp.printer 

val print_exp : exp -> Pp.printer
val print_stmt : statement -> Pp.printer
val print_block : statement list -> Pp.printer 
val print_stmts : statement list -> Pp.printer 
