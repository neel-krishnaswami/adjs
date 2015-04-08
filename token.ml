type tok =
  | Next
  | Cons
  | RParen
  | LParen
  | Comma
  | Bang
  | F
  | Fun
  | To
  | Plus
  | Minus
  | Ast
  | AndAnd
  | Or
  | Let
  | Colon
  | Equal
  | In
  | G
  | Fix
  | Loop
  | True
  | False
  | If
  | Then
  | Else
  | Num of float
  | String of string
  | Ident of string
  | Run
  | StreamType
  | And
  | StringType
  | NumType
  | BoolType
  | Lolli
  | Window
