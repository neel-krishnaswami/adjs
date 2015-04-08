exception CompileError of string

val process_signature_elt : Ast.signature_elt -> unit Context.t
val process_signature : Ast.signature_elt list -> unit Context.t

val process_binding :
  Ast.decl -> (Base.id * Lambda.term) option Context.t
val process_bindings :
  Ast.decl list -> (Base.id * Lambda.term) list Context.t

val elaborate :
  Ast.decl list * Ast.exp ->
  ((Base.id * Lambda.term) list * Lambda.term) Context.t

val translate_binding : Base.id * Lambda.term -> Js.statement list
val translate_program :
  (Base.id * Lambda.term) list * Lambda.term -> Js.statement list

val signature_environment : Ast.signature_elt list -> Context.ctx
val compile : out_channel -> Context.ctx -> Ast.program -> unit
