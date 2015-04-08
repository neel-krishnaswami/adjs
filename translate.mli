type dest = CallReturn | Ident of Base.id
type tailcall = Nontail | TailCall of Base.id * Base.id
val option : 'a -> 'a option -> 'a
val return : dest -> Js.exp option -> Js.statement list
val translate : Lambda.term -> Js.statement list * Js.exp
