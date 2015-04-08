val expand_const :
  Ast.kind ->
  (unit -> Ast.tp * Ast.kind) -> Base.id -> unit Context.t
val expand_one :
  Ast.kind ->
  (Base.id -> Ast.tp * Ast.kind * Ast.kind) ->
  Base.id -> unit Context.t
val expand_two :
  Ast.kind ->
  (Base.id ->
   Base.id -> Ast.tp * Ast.kind * (Ast.kind * Ast.kind)) ->
  Base.id -> unit Context.t
val expand_list :
  Ast.kind ->
  (Base.id list -> Ast.tp * Ast.kind * Ast.kind list) ->
  'a list -> Base.id -> unit Context.t
val expand_num : Ast.kind -> Base.id -> unit Context.t
val expand_string : Ast.kind -> Base.id -> unit Context.t
val expand_bool : Ast.kind -> Base.id -> unit Context.t
val expand_pure : Ast.kind -> Base.id -> unit Context.t
val expand_next : Ast.kind -> Base.id -> unit Context.t
val expand_nextlin : Ast.kind -> Base.id -> unit Context.t
val expand_f : Ast.kind -> Base.id -> unit Context.t
val expand_g : Ast.kind -> Base.id -> unit Context.t
val expand_dom : Ast.kind -> Base.id -> unit Context.t
val expand_frame : Ast.kind -> Base.id -> unit Context.t
val expand_svg : Ast.kind -> Base.id -> unit Context.t
val expand_stream : Ast.kind -> Base.id -> unit Context.t
val expand_arrow : Ast.kind -> Base.id -> unit Context.t
val expand_lolli : Ast.kind -> Base.id -> unit Context.t
val expand_product : 'a list -> Ast.kind -> Base.id -> unit Context.t
val expand_tensor : 'a list -> Ast.kind -> Base.id -> unit Context.t
val expand_app :
  Base.id -> 'a list -> Ast.kind -> Base.id -> unit Context.t
val expand : Base.id -> Ast.tp -> unit Context.t
val mismatch : string -> Ast.tp -> 'a Context.t
val expand_evar :
  Base.id ->
  string -> (Ast.kind -> Base.id -> 'a Context.t) -> 'a Context.t
val ( <== ) : Ast.tp -> Ast.tp -> unit Context.t
val sub : Ast.tp -> Ast.tp -> unit Context.t
