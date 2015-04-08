open Ast
open Base

type sort = Univ | Exist
type usage = Used | Fresh
type stability = Dyn | Stable

type hyp =
  | Kind of sort * Ast.kind option 
  | Type of sort * kind * Ast.tp option
  | Hyp of stability * Ast.tp * int
  | Data of Ast.datatype
  | LHyp of Ast.tp * int * usage
  | HideLinear
  | HideDynamic 

type ctx = (id * hyp) list 

type 'a return = Value of 'a | Error of string

type state = {ctx : ctx; sym : int; pos : Base.pos}
type 'a t = Ctx of (state -> ('a * state) return)

let value (v,s) = Value(v, s)

let return v = Ctx(fun state -> (value(v, state)))
 

let (>>=) (Ctx cmd) f =
  Ctx(fun state ->
    match cmd state with
    | Value(v, state) -> let Ctx op = f v in op state
    | Error msg -> Error msg)
  
let (>>) m1 m2 = m1 >>= (fun () -> m2)

let rec seq = function
  | [] -> return []
  | m :: ms -> m >>= (fun x -> seq ms >>= (fun xs -> return (x :: xs)))

let gensym s = fun state ->
  let newname = (try Scanf.sscanf s "%s@$%d" (fun name _ -> Printf.sprintf "%s$%d" name state.sym)
                 with End_of_file -> Printf.sprintf "%s$%d" s state.sym) in
  let newstate = {state with sym = state.sym + 1} in
(* Printf.printf "\nGENSYM %s\n\n" newname); *)
  Value(newname, newstate)

let newid s = Ctx(gensym s)

let fresh rename x term =
  newid x >>= (fun x' ->
  return (x', rename x x' term))


let error fmt = 
  Format.ksprintf (fun msg -> Ctx(fun state ->
    Error (Format.sprintf "%a: %s" fmt_pos state.pos msg))) fmt

let orelse (Ctx cmd) (Ctx cmd') =
  Ctx(fun s ->
    match cmd s with
    | Error _ -> cmd' s
    | Value(a, s) -> Value(a, s))

let get = Ctx(fun s -> Value(s.ctx, s))
let set ctx = Ctx(fun s -> Value((), {s with ctx = ctx}))

let setpos pos = Ctx (fun s -> Value((), {s with pos = pos}))

let print_ids msg ctx = ()
(*
    Printf.printf "%s: " msg; List.iter (fun (x, _) -> Printf.printf "%s " x) ctx; Printf.printf "\n" 
*)

let print_var x = ()
(*  Printf.printf "'%s' " x *)

let push hyp = get >>= (fun ctx -> let ctx' = hyp :: ctx in print_ids (Format.sprintf "push %a" fmt_id (fst hyp)) ctx'; set ctx')

let pop x =
  let rec loop = function
    | []                       -> error "pop: unbound variable '%a'" fmt_id x
    | (y, _) :: ctx when x = y -> return ctx
    | (y, hyp) :: ctx -> loop ctx >>= (fun ctx' -> 
                         return ctx')
  in
  get >>= (fun ctx -> print_ids (Printf.sprintf "pop '%a'" fmt_id x) ctx; loop ctx) >>= set

let used id = 
  let rec used = function
    | [] -> return ()
    | (id', LHyp(_, _, Fresh)) :: _ when id = id' -> error "unused linear variable '%a'" fmt_id id
    | (x', hyp) :: ctx  -> used ctx 
  in
  get >>= used

let with_hyp (x, hyp) cmd =
  push (x, hyp) >> cmd >>= (fun a -> used x >> pop x >> return a) 

let lookup x = 
  let rec lookup hide_linear hide_dynamic ctx =
    match ctx with 
    | [] ->  error "unbound variable '%a'" fmt_id x
    | (x', HideLinear) :: ctx' ->
          lookup true hide_dynamic ctx' >>= (fun (result, ctx') -> 
          return (result, (x', HideLinear) :: ctx'))
    | (x', HideDynamic) :: ctx' ->
          lookup hide_linear true ctx' >>= (fun (result, ctx') -> 
          return (result, (x', HideLinear) :: ctx'))
    | (x', hyp) :: ctx' when x = x' ->
      (match hyp with
      | LHyp(tp,i,Fresh) when hide_linear -> 
	error "unbound linear variable '%a' -- G(-) hides linear variables" fmt_id x
      | LHyp(tp,i,Fresh) -> 
	return (hyp, (x', LHyp(tp, i, Used)) :: ctx')
      | LHyp(tp,i,Used) -> 
        error "repeated use of linear variable '%a'" fmt_id x
      | Hyp(Dyn, _, _) when hide_dynamic -> 
        error "unbound variable '%a' -- ! hides dynamic variables" fmt_id x
      | _ -> return (hyp, (x, hyp) :: ctx'))
    | (x', hyp) :: ctx' -> 
      lookup hide_linear hide_dynamic ctx' >>= (fun (result, ctx') ->
      return (result, (x',hyp) :: ctx'))
  in
  get >>= (fun ctx -> print_var x; print_ids "lookup" ctx; lookup false false ctx) >>= (fun (v, ctx') -> set ctx' >> return v)

let update_eqn x input = 
  let rec update = function
    | [] -> error "Unbound variable '%a'" fmt_id x
    | (y, Type(Exist, Int, Some _)) :: ctx when x = y -> error "Evar '%a' already set" fmt_id x
    | (y, Type(Exist, Int, None)) :: ctx when x = y -> return (List.rev input @ ctx)
    | (y, Kind(Exist, None)) :: ctx when x = y -> return (List.rev input @ ctx)
    | (y, Kind(Exist, Some _)) :: ctx when x = y -> error "Existential kind var '%a' already set" fmt_id x
    | hyp :: ctx -> update ctx >>= (fun ctx' -> return (hyp :: ctx'))
  in
  get >>= update >>= set

let rec kind_subst k kvar = function
  | Int -> Int
  | Lin -> Lin
  | KArrow(k1, k2) -> KArrow(kind_subst k kvar k1,
                             kind_subst k kvar k2)
  | KVar kvar' -> (if kvar = kvar' then k else KVar kvar')

let rec kvar_in_tp_subst k kvar = function 
  | TVar a -> return (TVar a)
  | Forall(a', None, tp_body) ->
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    kvar_in_tp_subst k kvar tp_body >>= (fun tp_result ->
    return (Forall(a'', None, tp_result))))
  | Exists(a', None, tp_body) ->
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    kvar_in_tp_subst k kvar tp_body >>= (fun tp_result ->
    return (Exists(a'', None, tp_result))))
  | Forall(a', Some kbody, tp_body) ->
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    kvar_in_tp_subst k kvar tp_body >>= (fun tp_result ->
    return (Forall(a'', Some(kind_subst k kvar kbody), tp_result))))
  | Exists(a', Some kbody, tp_body) -> 
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    kvar_in_tp_subst k kvar tp_body >>= (fun tp_result ->
    return (Exists(a'', Some(kind_subst k kvar kbody), tp_result))))
  | Num          -> return Num
  | Bool         -> return Bool
  | String       -> return String
  | Pure tbody   -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Pure tbody'))
  | Next tbody   -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Next tbody'))
  | Stream tbody -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Stream tbody'))
  | G tbody      -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (G tbody'))
  | F tbody      -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (F tbody'))
  | Dom tbody    -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Dom tbody'))
  | Frame tbody  -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Frame tbody'))
  | Svg tbody    -> kvar_in_tp_subst k kvar tbody >>= (fun tbody' -> return (Svg tbody'))
  | Arrow(tp1, tp2) ->
      kvar_in_tp_subst k kvar tp1 >>= (fun tp1' -> 
      kvar_in_tp_subst k kvar tp2 >>= (fun tp2' -> 
      return (Arrow(tp1', tp2'))))
  | Lolli(tp1, tp2) ->
      kvar_in_tp_subst k kvar tp1 >>= (fun tp1' -> 
      kvar_in_tp_subst k kvar tp2 >>= (fun tp2' -> 
      return (Lolli(tp1', tp2'))))
  | Product tbodies ->
    seq (map (kvar_in_tp_subst k kvar) tbodies) >>= (fun tbodies -> 
    return (Product tbodies))
  | Tensor tbodies ->
    seq (map (kvar_in_tp_subst k kvar) tbodies) >>= (fun tbodies -> 
    return (Tensor tbodies))
  | TApp(tp, tbodies) ->
    kvar_in_tp_subst k kvar tp >>= (fun tp ->
    seq (map (kvar_in_tp_subst k kvar) tbodies) >>= (fun tbodies -> 
    return (TApp(tp, tbodies))))
  | TLam(b, tbody) ->
      fresh rename_tp b tbody >>= (fun (b, tbody) -> 
      kvar_in_tp_subst k kvar tbody >>= (fun tbody ->
      return (TLam(b, tbody))))
  | TLet(b, tp1, tp2) -> 
      fresh rename_tp b tp2 >>= (fun (b, tp2) ->
      kvar_in_tp_subst k kvar tp1 >>= (fun tp1 ->
      kvar_in_tp_subst k kvar tp2 >>= (fun tp2 ->
      return (TLet(b, tp1, tp2)))))
  | TAnnot(tp1, k1) ->
      let k1 = kind_subst k kvar k1 in
      kvar_in_tp_subst k kvar tp1 >>= (fun tp1 ->
      return (TAnnot(tp1, k1)))


let rec tp_subst (tp : tp)  a = function
  | TVar a' -> if a = a' then return tp else return (TVar a')
  | Forall(a', kopt, tp_body) ->
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    tp_subst tp a tp_body >>= (fun tp_result ->
    return (Forall(a'', kopt, tp_result))))
  | Exists(a', kopt, tp_body) -> 
    newid a' >>= (fun a'' -> 
    let tp_body = rename_tp a' a'' tp_body in
    tp_subst tp a tp_body >>= (fun tp_result ->
    return (Exists(a'', kopt, tp_result))))
  | Num          -> return Num
  | Bool         -> return Bool
  | String       -> return String
  | Pure tbody   -> tp_subst tp a tbody >>= (fun tbody' -> return (Pure tbody'))
  | Next tbody   -> tp_subst tp a tbody >>= (fun tbody' -> return (Next tbody'))
  | Stream tbody -> tp_subst tp a tbody >>= (fun tbody' -> return (Stream tbody'))
  | G tbody      -> tp_subst tp a tbody >>= (fun tbody' -> return (G tbody'))
  | F tbody      -> tp_subst tp a tbody >>= (fun tbody' -> return (F tbody'))
  | Dom tbody    -> tp_subst tp a tbody >>= (fun tbody' -> return (Dom tbody'))
  | Frame tbody  -> tp_subst tp a tbody >>= (fun tbody' -> return (Frame tbody'))
  | Svg tbody    -> tp_subst tp a tbody >>= (fun tbody' -> return (Svg tbody'))
  | Arrow(tp1, tp2) ->
      tp_subst tp a tp1 >>= (fun tp1' -> 
      tp_subst tp a tp2 >>= (fun tp2' -> 
      return (Arrow(tp1', tp2'))))
  | Lolli(tp1, tp2) ->
      tp_subst tp a tp1 >>= (fun tp1' -> 
      tp_subst tp a tp2 >>= (fun tp2' -> 
      return (Lolli(tp1', tp2'))))
  | Product tbodies ->
    seq (map (tp_subst tp a) tbodies) >>= (fun tbodies -> 
    return (Product tbodies))
  | Tensor tbodies ->
    seq (map (tp_subst tp a) tbodies) >>= (fun tbodies -> 
    return (Tensor tbodies))
  | TApp(d, tbodies) -> 
    seq (map (tp_subst tp a) tbodies) >>= (fun tbodies -> 
    return (TApp(d, tbodies)))
  | TLet(b, tp1, tp2) ->
      fresh rename_tp b tp2 >>= (fun (b, tp2) ->
      tp_subst tp a tp1 >>= (fun tp1 ->
      tp_subst tp a tp2 >>= (fun tp2 -> 
      return (TLet(b, tp1, tp2)))))
  | TLam(b, tp1) ->
      fresh rename_tp b tp1 >>= (fun (b, tp1) ->
      tp_subst tp a tp1 >>= (fun tp1 -> 
      return (TLam(b, tp1))))
  | TAnnot(tp1, k1) ->
      tp_subst tp a tp1 >>= (fun tp1 ->
      return (TAnnot(tp1, k1)))

let rec subst_ctx_tp ctx tp =
  match ctx with 
  | []                                     -> return tp
  | (a, Type(sort, k, Some tycon)) :: ctx  -> tp_subst tycon a tp >>= (fun tp -> subst_ctx_tp ctx tp)
  | _ :: ctx                               -> subst_ctx_tp ctx tp

let subst tp = get >>= (fun ctx -> subst_ctx_tp ctx tp)


let rec subst_kind_ctx ctx kind = 
  match ctx with 
  | []                              -> kind
  | (a, Kind(sort, Some k)) :: ctx  -> subst_kind_ctx ctx (kind_subst k a kind)
  | _ :: ctx                        -> subst_kind_ctx ctx kind

let subst_kind k = get >>= (fun ctx -> return (subst_kind_ctx ctx k))


let lookup_datatype (d, tpargs) =
  lookup d >>= (function
    | Data(k, vars, cenv) when length tpargs = length vars ->
       seq (map
              (fun (c, tp) -> 
                foldr2 (fun tparg (a,k') acc -> acc >>= (tp_subst tparg a)) tpargs vars (return tp) >>= (fun tp -> 
                return (c, tp)))
              cenv)
    | Data(k, vars, _) -> error "datatype constructor '%s' has wrong number of arguments" d 
    | _ -> error "variable '%s' not bound to datatype declaration" d)

let lookup_datatype_by_con c =
  let rec loop = function
    | [] -> error "unbound datatype constructor '%s'" c
    | (x, Data(k, bs, cenv)) :: _ when List.mem_assoc c cenv -> return (x, map fst bs)
    | _ :: env -> loop env
  in
  get >>= loop

let before_ctx a = 
  let rec before = function
    | [] -> []
    | (a', Type(Univ, Int, None)) :: ctx when a = a' -> ctx
    | (a', Type(Exist, Int, _)) :: ctx when a = a' -> ctx 
    | _ :: ctx -> before ctx
  in
  get >>= (fun ctx -> return (before ctx))

let before x cmd =
  get >>= (fun current -> 
  before_ctx x >>= (fun old -> 
  set old >>
  cmd >>= (fun v -> 
  set current >>
  return v)))

let with_pure_ctx cmd =
  newid "hidedynamic" >>= (fun x -> 
  with_hyp (x, HideDynamic) cmd)

let with_nonlinear cmd = 
  newid "hidelinear" >>= (fun x -> 
  with_hyp (x, HideLinear) cmd)

let with_empty_lctx cmd = with_nonlinear cmd 
  
let rec update_info old cur = 
  match old, cur with
  | [], [] -> []
  | _, ((x2, (HideLinear as hyp)) :: cur')
  | _, ((x2, (HideDynamic as hyp)) :: cur')
  | _, ((x2, ((Data _) as hyp)) :: cur')
  | _, ((x2, (Type(_, _, _) as hyp)) :: cur') ->
      (x2, hyp) :: update_info old cur'
  | (x1, (Hyp(_, _, _) as hyp)) :: old',  (x2, Hyp(_, _, _)) :: cur' ->
      if x1 = x2 then (x1, hyp) :: update_info old' cur' else assert false 
  | (x1, Hyp(_, _, _)) :: old',  (x2, LHyp(_, _, _)) :: cur' ->
      assert false
  | (x1, (LHyp(_, _, _) as hyp)) :: old', (x2, LHyp(_, _, _)) :: cur' -> 
      if x1 = x2 then (x1, hyp) :: update_info old' cur' else assert false 
  | (x1, LHyp(_, _, _)) :: old', (x2, Hyp(_, _, _)) :: cur' -> 
      assert false
  | (x1, hyp) :: old', _ -> update_info old' cur
  | _ -> assert false 
      
let rec compatible env1 env2 =
  match env1, env2 with
  | [], [] -> None
  | (x1, LHyp(_, _, usage1)) :: env1',
    (x2, LHyp(_, _, usage2)) :: env2' ->
      if x1 = x2 && usage1 = usage2 then
        compatible env1' env2'
      else
        Some x1
  | ((_, LHyp(_, _, _)) :: _), ((_, _) :: env2') -> compatible env1 env2'
  | ((_, _) :: env1'), ((_, LHyp(_, _, _)) :: _) -> compatible env1' env2
  | _ :: env1', _ :: env2'                      ->  compatible env1' env2'
  | _, _ -> assert false 

let par_seq cmd1 cmd2 =
  get >>= (fun old1 -> 
  cmd1 >>= (fun v1 ->
  get >>= (fun cur1 ->
  let old2 = update_info old1 cur1 in 
  set old2 >>
  cmd2 >>= (fun v2 -> 
  get >>= (fun cur2 -> 
  match compatible cur1 cur2 with
  | None -> return (v1, v2)
  | Some x -> error "Branches differ on use of variable '%a'" fmt_id x)))))

let rec parallel = function 
  | [] -> return []
  | [c] -> c >>= (fun v -> return [v])
  | c :: cs -> par_seq c (parallel cs) >>= (fun (v, vs) -> return (v :: vs))

let age x = 
  let rec find ctx = 
    try
	match List.assoc x ctx with
	  | Hyp(_, _, i) 
	  | LHyp(_, i, _)     -> return i 
	  | _                 -> error "can't find age of type variable '%a'" fmt_id x
    with 
	  Not_found -> error "unbound variable '%a' in call to 'age'" fmt_id x
  in
  get >>= find     

let advance free t i =
  let body = 
    Ids.fold
      (fun x acc ->
	  age x >>= (fun j ->
	  if j <= i
	  then acc
	  else acc >>= (fun t -> 
             return (Lambda.Let(x, Lambda.Force(Lambda.Var x), t)))))
      free
      (return t)
  in
  body >>= (fun t -> return (Lambda.Lazy(t)))



let run (Ctx cmd) ctx pos =
  match cmd {sym = 0; ctx = ctx; pos = pos} with
  | Value(v, s) -> Value(v, s.ctx)
  | Error msg   -> Error msg 
