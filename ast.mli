type kind =
  | Int
  | Lin
  | KVar of Base.id
  | KArrow of kind * kind


type tp =
  | Num
  | Bool
  | String
  | Pure of tp
  | Next of tp
  | Stream of tp
  | G of tp
  | Product of tp list
  | Arrow of tp * tp
  | Forall of Base.id * kind option * tp
  | Exists of Base.id * kind option * tp
  | TApp of tp * tp list
  | F of tp
  | Tensor of tp list
  | Lolli of tp * tp  
  | Dom of tp
  | Frame of tp 
  | Svg of tp
  | TVar of Base.id
  | TAnnot of tp * kind 
  | TLam of Base.id * tp
  | TLet of Base.id * tp * tp 


type pat = Base.pos * pat'
and pat' =
  | PTop 
  | PVar of Base.id
  | PBang of pat 
  | PCon of Base.conid * pat
  | PCons of pat * pat 
  | PNext of pat
  | PTuple of pat list
  | PF of pat 

type exp = Base.pos * exp'
and exp' = 
  | EVar of Base.id
  | EBang of exp
  | ENext of exp 
  | ETuple of exp list
  | ELam of pat * exp
  | EApp of exp * exp
  | EBool of bool 
  | EIf of exp * exp * exp
  | ENum of float
  | EString of string
  | ECons of exp * exp 
  | EAnnot of exp * tp
  | EFix of Base.id * exp
  | ELoop of Base.id * pat * exp  
  | EG of exp
  | EF of exp 
  | EOp of Base.op * exp * exp
  | ECase of exp * branch list
  | ECon of Base.conid * exp 
  | ELet of pat * exp * exp
  | ELetVar of Base.id * Base.id * exp 
  | ERun of exp 
and branch = (pat * exp)

type datatype = kind * (Base.id * kind) list * (Base.conid * tp) list 

type decl = 
  | DataBind of Base.pos * Base.id * datatype
  | ValueBind of (Base.pos * Base.id * exp * tp)
  | ValueDecl of (Base.pos * Base.id * tp)
  | TypeBind of (Base.pos * Base.id * tp * kind)
  | TypeDecl of (Base.pos * Base.id * kind)

type program = decl list * exp 

type signature_elt =
  | DataDecl of Base.pos * Base.id * datatype
  | SigTypeDecl of Base.pos * Base.id * tp

type signature = signature_elt list 

val pat_eq : pat -> pat -> bool
val exp_eq : exp -> exp -> bool

val freevars_kind : kind -> Base.Ids.t
val freevars_tp : tp -> Base.Ids.t 
val pvars : pat -> Base.Ids.t
val freevars_exp : exp -> Base.Ids.t

val rename_kind : Base.id -> Base.id -> kind -> kind
val rename_tp : Base.id -> Base.id -> tp -> tp
val rename_exp : Base.id -> Base.id -> exp -> exp

val string_of_kind : kind -> string 
val string_of_tp : tp -> string
val exp_pos : exp -> Base.pos
val pat_pos : pat -> Base.pos

val fmt_tp : unit -> tp -> string
val fmt_kind : unit -> kind -> string














