open Base
open Ast
open Poly
open Context
open Kinding
open Subtype

let map = List.map
let mapM f xs = seq (map f xs)

let rec iterM f = function
  | [] -> return ()
  | v :: vs -> f v >> iterM f vs
               

exception CompileError of string

let rec ofilter = function
  | [] -> []
  | None :: xs -> ofilter xs
  | (Some x) :: xs -> x :: (ofilter xs)

let process_binding = function
  | ValueBind(pos, x, e, tp) ->
    setpos pos >>
    check_kind tp Int >>= (fun tp -> 
    check e tp 0 >>= (fun t -> 
    push (x, Hyp(Stable, tp, 0)) >>
    return (Some(x, t))))
  | ValueDecl (pos, x, tp) -> 
    setpos pos >>
    check_kind tp Int >>= (fun tp ->
    push (x, Hyp(Stable, tp, 0)) >>
    return None)
  | TypeBind(pos, a, tp, kind) ->
    setpos pos >>
    check_kind tp kind >>= (fun tp ->
    push (a, Type(Univ, kind, Some tp)) >>
    return None)
  | TypeDecl(pos, a, kind) ->
    setpos pos >>
    push (a, Type(Univ, kind, None)) >>
    return None
  | DataBind (pos, d, (k, bs, cenv)) ->
    setpos pos >>
    mapM (fun (b, k) -> newid b >>= (fun b' -> return (b,k))) bs >>= (fun bs' ->
    push (d, Data(k, bs, cenv)) >>
    let cenv = map (fun (c, tp) -> (c, List.fold_right2 rename_tp (map fst bs) (map fst bs') tp)) cenv in 
    iterM (fun (b, k) -> push (b, Type(Univ, k, None))) bs' >> 
    mapM (fun (c, tp) -> check_kind tp Int >>= (fun tp -> return (c,tp))) cenv >>= (fun cenv ->
    pop d >>
    push (d, Data(k, bs', cenv)) >>
    return None))


let rec process_bindings = function
  | []      -> return []
  | b :: bs -> process_binding b >>= (function
               | None   -> process_bindings bs
               | Some r -> process_bindings bs >>= (fun rs -> 
                           return (r :: rs)))
  
let elaborate (bs, e) =
  process_bindings bs >>= (fun tenv ->
  newid "a" >>= (fun a -> 
  check e (G(Exists(a, Some Int, Dom (TVar a)))) 0 >>= (fun main ->
  return (tenv, main))))
      
let translate_binding (x, t) =
  let (s, e) = Translate.translate t in 
  s @ [Js.LetDef(x, e)]

let translate_program (bs, e) = 
  let s = List.concat (map translate_binding bs) in
  let (mains, mainexp) = Translate.translate e in
  let main_stmt =
    Js.LetDef("$main", Js.Fun(None, [], [Js.Return (Js.Apply(mainexp, []))]))
  in 
  s @ mains @ [main_stmt]

let process_signature_elt = function
  | DataDecl (pos, d, (k, bs, cenv)) ->
    setpos pos >>
    mapM (fun (b, k) -> newid b >>= (fun b' -> return (b,k))) bs >>= (fun bs' ->
    push (d, Data(k, bs, cenv)) >>
    let cenv = map (fun (c, tp) -> (c, List.fold_right2 rename_tp (map fst bs) (map fst bs') tp)) cenv in 
    iterM (fun (b, k) -> push (b, Type(Univ, k, None))) bs' >> 
    mapM (fun (c, tp) -> check_kind tp Int >>= (fun tp -> return (c,tp))) cenv >>= (fun cenv ->
    pop d >>
    push (d, Data(k, bs', cenv))))

  | SigTypeDecl(pos, x, tp) ->
    setpos pos >>
    check_kind tp Int >>= (fun tp ->
    push (x, Hyp(Stable, tp, 0)))

let process_signature sigs =
  iterM process_signature_elt sigs 

let signature_environment sigs =
  match run (process_signature sigs) [] Base.dummy_pos with 
    | Error msg -> raise (CompileError msg)
    | Value((), ctx) -> ctx

let compile out env program =
  match run (elaborate program) env Base.dummy_pos with
    | Error msg -> raise (CompileError msg)
    | Value(result, _) ->
      Pp.print (Js.print_stmts (translate_program result)) out
