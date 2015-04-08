open Base
open Ast 
open Lambda
open Kinding 
open Subtype
open Context


(* specialize must be called with an intuitionistic evar as an argument *)

(* specialize takes a pattern and a type, and expands evars in the ways that the
   pattern requires *)

exception Higher_kinds of string

let rec specialize p tp =
  subst tp >>= specialize' p

and specialize' ((pos, q) as p) tp =
  setpos pos >>
  (match q, tp with
  | PTop, tp              -> return ()
  | PVar _, tp            -> return ()
  | PBang p', Pure tp'    -> specialize p' tp'
  | PBang p', TVar a      -> expand_pure Int a >> specialize p tp
  | PBang _, _ -> mismatch "pure" tp
  | PCon(c, p), TApp(TVar d, tps) ->
    lookup_datatype (d, tps) >>= (fun cenv -> 
    try specialize p (List.assoc c cenv) with Not_found -> assert false)
  | PCon(c, _), TVar a ->
    lookup_datatype_by_con c >>= (fun (d, bs) -> 
    expand_app d bs Int a >> 
    specialize p tp)
  | PCon(_, _), _ -> mismatch "datatype" tp 
  | PCons(p1, p2), Stream tp' ->
    specialize p1 tp' >> specialize p2 tp
  | PCons(_, _), TVar a -> expand_stream Int a >> specialize p tp
  | PCons(_, _), tp -> mismatch "stream" tp 
  | PNext p1, Next tp1 ->
    specialize p1 tp1       
  | PNext _, TVar a -> expand_next Int a >> specialize p tp
  | PNext _, _ -> mismatch "delay" tp 
  | PTuple ps, Product tps ->
    if length ps = length tps then
      seq (map2 specialize ps tps) >>= (fun _ -> return ())     
    else
      error "tuple pattern %d long, type '%a' is %d long" (length ps) fmt_tp tp (length tps)
  | PTuple ps, TVar a -> expand_product ps Int a >> specialize p tp
  | PTuple _, _ -> mismatch "tuple" tp
  | PF _, _ -> error "linear constructor in nonlinear pattern")

(* lspecialize should be called with a linear evar as an argument *)

let rec lspecialize p tp =
  subst tp >>= specialize' p

and lspecialize' ((pos, q) as p) tp =
  setpos pos >> 
  (match q, tp with
  | PTop, tp        	  -> error "nonlinear pattern" 
  | PBang p', _     	  -> error "nonlinear pattern" 
  | PCon(_, _), _   	  -> error "nonlinear pattern" 
  | PVar _, tp      	  -> return () 
  | PNext p1, Next tp1    -> lspecialize p1 tp1
  | PNext _, TVar a       -> expand_nextlin Lin a >> lspecialize p tp
  | PNext _, _            -> mismatch "next" tp 
  | PF _, F _             -> return ()
  | PF _, TVar a          -> expand_f Lin a >> lspecialize p tp 
  | PF _, _               -> mismatch "F" tp 
  | PCons(p, p'), Dom tp1 -> lspecialize p (Frame tp1) >> lspecialize p' (Dom tp1)
  | PCons(_, _),  TVar a  -> expand_dom Lin a >> lspecialize p tp
  | PTuple ps, TVar a     -> expand_tensor ps Lin a >> specialize p tp
  | PTuple ps, Tensor tps ->
    if length ps = length tps then
      seq (map2 lspecialize ps tps) >>= (fun _ -> return ())     
    else
      error "tensor pattern %d long, type '%a' is %d long" (length ps) fmt_tp tp (length tps)
  | PTuple _, _           -> mismatch "tensor" tp)

(* Before we check a case head, we specialize the type to what all the 
   patterns require *)

let rec specialize_set ps tp =
  match ps, tp with
  | [], tp -> return tp
  | p :: ps, TVar a ->
    specialize p (TVar a) >>
    subst tp >>= 
    specialize_set ps
  | p :: ps, tp -> return tp 

let rec all_tops = function
  | [] -> Some []
  | ([], e) :: env -> assert false 
  | ((_, PTop) :: ps, e) :: env ->
    (match all_tops env with
    | Some branches -> Some((ps, e) :: branches)
    | None -> None)
  | (p :: ps, e) :: env -> None

let varname branches =
  let rec loop = function
    | (optvar, [])                                    -> optvar
    | (_, ([], e) :: _)                               -> assert false 
    | (None, ((pos, PVar x) :: ps, e) :: branches)    -> loop (Some x, branches)
    | (Some x, ((pos, PVar x') :: ps, e) :: branches) -> if x = x' then loop (Some x, branches) else None
    | (optvar, (p :: ps, e) :: branches)              -> loop (optvar, branches)
  in
  loop (None, branches)

let simplify_head xold xnew (ps, e) =
  match ps with
  | [] -> assert false
  | (pos, PVar x) :: ps -> if x = xold
                           then ((pos, PTop) :: ps, rename_exp x xnew e)
                           else ((pos, PTop) :: ps, (pos, ELetVar(x, xnew, e)))
  | p :: ps             -> (p :: ps, e)

let rec name_for_type = function
  | Num        -> "n"
  | Bool       -> "b"
  | String     -> "s"
  | Stream tp  -> name_for_type tp ^ "s"
  | Pure _     -> "st"
  | Next _     -> "d"
  | G _        -> "g"
  | Product _  -> "p"
  | Arrow(_,_) -> "f"
  | TApp(TVar d, _) -> d
  | TApp(TApp(_, _) as tp, _) -> name_for_type tp
  | F _        -> "i"
  | Tensor _   -> "t"
  | Lolli(_,_) -> "h"
  | Dom _      -> "dom"
  | Frame _    -> "r"
  | Svg _      -> "svg"
  | TVar a     -> "u"
  | Forall(_, _, tp) -> name_for_type tp
  | Exists(_, _, tp) -> name_for_type tp
  | tp                -> raise (Higher_kinds (Printf.sprintf "name_for_type -- %a" fmt_tp tp))


let simplify_heads xdefault branches =
  let xold = opt_fold (fun x -> x) xdefault (varname branches) in 
  newid xold >>= (fun xnew ->
  return (xnew, map (simplify_head xold xnew) branches))

let split_tuple tps branches =
  seq (map (function
            | ((pos, PTuple ps1) :: ps, e) ->
              if length ps1 = length tps then
                return (ps1 @ ps, e)
              else 
                error "wrong number of arguments in tuple pattern"
            | (((pos, PTop) as p) :: ps, e) ->
              return ((List.map (fun _ -> p) tps) @ ps, e)
            | ((pos, p) :: ps, e) ->
              error "expected tuple pattern"
            | ([], e) -> assert false)
         branches)
    

let split_pure branches =
  seq (map (function
            | ((pos, (PBang p)) :: ps, e) -> return (p :: ps, e)
            | ((pos, PTop) :: ps, e)      -> return ((pos, PTop) :: ps, e)
            | ((pos, p) :: ps, e)         -> error "expected pure pattern"
            | ([], e)                     -> assert false)
         branches)

let split_next branches = 
  seq (map (function
            | ((pos, (PNext p)) :: ps, e) -> return (p :: ps, e)
            | ((pos, PTop) :: ps, e)      -> return ((pos, PTop) :: ps, e)
            | ((pos, p) :: ps, e)         -> error "expected next pattern"
            | ([], e)                     -> assert false)
         branches)

let split_stream branches = 
  seq (map (function
            | ((pos, PCons(p1, p2)) :: ps, e) -> return (p1 :: p2 :: ps, e)
            | ((pos, PTop) :: ps, e)          -> return ((pos, PTop) :: (pos, PTop) :: ps, e)
            | ((pos, p) :: ps, e)             -> error "expected stream pattern"
            | ([], e)                         -> assert false)
         branches)

let split_dom branches = 
  seq (map (function
            | ((pos, PCons(p1, p2)) :: ps, e) -> return (p1 :: p2 :: ps, e)
            | ((pos, p) :: ps, e)             -> error "expected dom pattern"
            | ([], e)                         -> assert false)
         branches)


let split_f (branches : (pat list * exp) list) = 
  seq (map (function
            | ((pos, (PF p)) :: ps, e) -> return (p :: ps, e)
            | ((pos, p) :: ps, e)      -> error "expected F pattern"
            | ([], e)                  -> assert false)
         branches)

let split_next_lin branches = 
  seq (map (function
            | ((pos, (PNext p)) :: ps, e) -> return (p :: ps, e)
            | ((pos, p) :: ps, e)         -> error "expected linear next pattern"
            | ([], e)                     -> assert false)
         branches)

let split_tensor tps branches =
  seq (map (function
            | ((pos, PTuple ps1) :: ps, e) ->
              if length ps1 = length tps then
                return (ps1 @ ps, e)
              else 
                error "wrong number of arguments in tensor pattern"
            | ((pos, p) :: ps, e) ->
              error "expected tensor pattern"
            | ([], e) -> assert false)
         branches)



let intro (pos, e) =
  match e with 
  | EBang _
  | ENext _
  | ETuple _
  | ELam(_, _)
  | EBool _
  | EIf(_, _, _)
  | ENum _
  | EString _
  | ECons(_, _)
  | EG _
  | EF _
  | ECon(_, _) -> true
  | _ -> false

let checkable (pos, e) =
  match e with 
  | EFix(_, _)
  | ELoop(_, _, _)
  | ECase(_, _)
  | ELetVar(_, _, _) 
  | ELet(_, _, _)    -> true
  | _                -> intro (pos, e)

(* These types can be silently promoted to pure *)
let rec stable = function 
  | Num          
  | String       
  | Bool         
  | Pure _        -> true
  | Forall(_, _, tp) 
  | Exists(_, _, tp) -> stable tp  
  | Product tps   -> List.for_all stable tps 
  | Next _      
  | F _          
  | G _
  | Frame _ 
  | Dom _        
  | Svg _        
  | Stream _     
  | Arrow(_, _)  
  | Lolli(_, _)  
  | Tensor _
  | TApp(_, _)  
  | TVar _       -> false
  | _            -> raise (Higher_kinds "stable")

(* When putting a variable into the context, it's always
   safe to open any existentials, since it is left-invertible. *)

let rec let_exist_elim tp =
  match tp with
    | Exists(a, _, tp) ->
	fresh rename_tp a tp >>= (fun (a, tp) -> 
	push (a, Type(Univ, Int, None)) >>
	let_exist_elim tp)
    | _ -> return tp 

(* This takes a dynamic hypothesis of stable type and promotes it to a stable one *)

let promote_stable = function
  | Hyp(s, tp, i) when stable tp -> 
    let_exist_elim tp >>= (fun tp -> return (Hyp(Stable, tp, i)))
  | Hyp(s, tp, i) -> 
    let_exist_elim tp >>= (fun tp -> return (Hyp(s, tp, i)))
  | LHyp(tp, i, u) ->
    let_exist_elim tp >>= (fun tp -> return (LHyp(tp, i, u)))
  | hyp                           -> return hyp

let oper_type = function
  | Plus  -> (Num, Num, Num)
  | Minus -> (Num, Num, Num)
  | Times -> (Num, Num, Num)
  | Equal -> (Num, Num, Bool)
  | Lt    -> (Num, Num, Bool)
  | Leq   -> (Num, Num, Bool)
  | Gt    -> (Num, Num, Bool)
  | Geq   -> (Num, Num, Bool)
  | And   -> (Bool, Bool, Bool)
  | Or    -> (Bool, Bool, Bool)

let rec expand_for_elim tp =
  subst tp >>= (function
  | Forall(a, Some k, tp) ->
    fresh rename_tp a tp >>= (fun (a, tp) ->
    push (a, Type(Exist, k, None)) >> 
    expand_for_elim tp)
  | Forall(_, None, _) -> assert false 
  | Exists(a, Some k, tp) ->
    fresh rename_tp a tp >>= (fun (a, tp) ->
    push (a, Type(Univ, k, None)) >> 
    expand_for_elim tp)
  | Exists(_, None, _) -> assert false 
  | tp -> return tp)

let rec expand_for_intro tp = 
  match tp with
  | Forall(a, Some k, tp) ->
    fresh rename_tp a tp >>= (fun (a, tp) ->
    push (a, Type(Univ, k, None)) >> 
    expand_for_intro tp)
  | Forall(_, None, _) -> assert false
  | Exists(a, Some k, tp) ->
    fresh rename_tp a tp >>= (fun (a, tp) ->
    push (a, Type(Exist, Int, None)) >> 
    expand_for_intro tp)
  | Exists(_, None, _) -> assert false
  | _ -> return tp


let quantified = function
  | Forall(_, _, _) | Exists(_, _, _) -> true
  | _                                 -> false

let rec check term tp i = 
  subst tp >>= (fun tp' -> check' term tp' i)

and check' ((pos, term) as e) tp i =
  setpos pos >>
  (match term, tp with
  | _, _ when intro e && quantified tp ->
    expand_for_intro tp >>= (fun tp -> check e tp i) 
  | ELam(p, e2), Arrow(tp1, tp2) ->
    			  cover check [[p], e2] tp2 i [Hyp(Dyn, tp1, i)] >>= (function
                          | (t2, [u]) -> return (Lam(u, t2))
                          | _ -> assert false)
  | ELam(_, _), TVar a -> expand_evar a "function" expand_arrow >> 
                          check e tp i 
  | ELam(_, _), _      -> mismatch "function" tp 

  | ETuple es, Product tps when length es = length tps -> 
    seq (map2 (fun e tp -> check e tp i) es tps) >>= (fun ts -> 
    return (Tuple ts))
  | ETuple es, TVar a -> expand_evar a "product" (expand_product es) >> 
                         check e tp i 
  | ETuple _, tp      -> mismatch "product" tp 

  | ENum n, Num    -> return (LitNum n)
  | ENum n, TVar a -> expand_evar a "num" expand_num >>
                      check e tp i 
  | ENum _, _      -> mismatch "number" tp 

  | EBool b, Bool   -> return (LitBool b)
  | EBool _, TVar a -> expand_evar a "bool" expand_bool >>
                       check e tp i 
  | EBool _, _      -> mismatch "boolean" tp

  | ECons(e2, e3), Stream tp' ->
    check e2 tp' i >>= (fun h -> 
    check e3 (Stream tp') (i+1) >>= (fun t ->
    advance (freevars_exp e3) t i >>= (fun t' -> 
    return (Cons(h, t')))))
  | ECons(e2, e3), TVar a -> expand_evar a "stream" expand_stream >>
                             check e tp i 
  | ECons(_, _), tp       -> mismatch "stream" tp

  | EBang e1, Pure tp1 -> with_pure_ctx (check e1 tp1 i) >>= (fun t -> 
                            return (Thunk(t)))
  | EBang _, TVar a    -> expand_evar a "pure" expand_pure >>
                          check e tp i 
  | EBang _, _         -> mismatch "pure" tp

  | ENext e1, Next tp1 -> check e1 tp1 (i+1) >>= (fun t ->
                          advance (freevars_exp e1) t i)
  | ENext _, TVar a -> expand_evar a "next" expand_next >>
                       check e tp i 
  | ENext _, _      -> mismatch "delay" tp

  | EString s, String -> return (LitString s)
  | EString _, TVar a -> expand_evar a "string" expand_string >>
                         check e tp i 
  | EString _, _      -> mismatch "string" tp

  | ECon(c, e1), TApp(TVar d, tps) ->
    lookup_datatype (d, tps) >>= (fun cenv ->
    try
      let tp1 = List.assoc c cenv in
      check e1 tp1 i >>= (fun t1 ->
      return (Con(c, t1)))
    with
      Not_found -> error "constructor '%s' not in datatype '%s'" c d)
  | ECon(c, _), TVar a -> 
    lookup_datatype_by_con c >>= (fun (d, params) -> 
    expand_evar a "datatype" (expand_app d params) >>
    check e tp i)
  | ECon(_, _), _      -> mismatch "datatype" tp

  | EG e1, G tp1 -> with_empty_lctx (lcheck e1 tp1 i) >>= (fun t -> 
                    return (Thunk(t)))
  | EG _, TVar a -> expand_evar a "G" expand_g >>
                    check e tp i 
  | EG _, _      -> mismatch "G" tp

  | EIf(e1, e2, e3), tp ->
    check e1 Bool i >>= (fun t1 -> 
    check e2 tp i >>= (fun t2 -> 
    check e3 tp i >>= (fun t3 ->
    return (If(t1, t2, t3)))))
      
  | ELet(p, e1, e2), tp2 when checkable e1 ->
    newid "_a" >>= (fun a ->
    push (a, Type(Exist, Int, None)) >> 
    specialize p (TVar a) >> 
    check e1 (TVar a) i >>= (fun t1 -> 
    cover check [[p], e2] tp2 i [Hyp(Dyn, (TVar a), i)] >>= (function
    | (t2, [u]) -> return (Let(u, t1, t2))
    | _ -> assert false)))
  | ELet(p, e1, e2), tp2  ->
    synth e1 i >>= (fun (tp1, t1) ->
    cover check [[p], e2] tp2 i [Hyp(Dyn, tp1, i)] >>= (function
    | (t2, [u]) -> return (Let(u, t1, t2))
    | (t2, us) -> (List.iter (fun u -> Printf.printf "%s\n" u) us); flush stdout;  assert false))

  | ELetVar(y, x, e2), tp2 ->
    fresh rename_exp y e2 >>= (fun (y, e2) -> 
    lookup x >>= (fun hyp ->
    promote_stable hyp >>= (fun hyp -> 
    with_hyp (y, hyp) (check e2 tp2 i) >>= (fun t2 -> 
    return (Let(y, Var x, t2))))))

  | ECase(e1, branches), tp2 ->
    synth e1 i >>= (fun (tp1, t1) ->
    cover check (map (fun (p,e) -> [p], e) branches) tp2 i [Hyp(Dyn, tp1, i)] >>= (function
    | (t2, [u]) -> return (Let(u, t1, t2))
    | _ -> assert false))
    
  | EFix(x, e'), tp' ->
    fresh rename_exp x e' >>= (fun (x, e') -> 
    with_pure_ctx (with_hyp (x, Hyp(Stable, tp', i+1)) (check e' tp' i)) >>= (fun t -> 
    return (Lazyfix(x, t))))
  | ELoop(f, p, e'), _ ->
    fresh rename_exp f e' >>= (fun (f, e') -> 
    with_hyp (f, Hyp(Dyn, tp, i))
      (expand_for_intro tp >>= (function 
	  | Arrow(tp1, tp2) -> 
            cover check [[p], e'] tp2 i [Hyp(Dyn, tp1, i)] >>= (function
            | (t', [u]) -> return (Fix(f, u, t'))
            | _ -> assert false)
	  | _ -> mismatch "function" tp)))
  | _, _ ->
    synth e i >>= (fun (tp', t) ->
    (tp' <== tp) >>
    return t))


and synth (pos, e) i =
  setpos pos >> 
  match e with
  | EVar x ->
    lookup x >>= (function
      | Hyp(sort, tp, j) ->
        if sort = Dyn && i = j || sort = Stable && i >= j then
          return (tp, Var x)
        else 
          error "variable '%s' at time %d, used at %d" x j i
      | LHyp(_, _, _) -> error "linear variable '%a' used in nonlinear context" fmt_id x 
      | _ -> error "type variable '%s' used in term context" x)
  | EApp(e1, e2) ->
    synth e1 i >>= (fun (tp1, t1) ->
    expand_for_elim tp1 >>= (function 
    | Arrow(tp2, tp) -> 
      check e2 tp2 i >>= (fun t2 ->
      return (tp, App(t1, t2)))
    | _ -> mismatch "function" tp1))
  | EOp(op, e1, e2) ->
    let (tp1, tp2, tp) = oper_type op in
    check e1 tp1 i >>= (fun t1 ->
    check e2 tp2 i >>= (fun t2 -> 
    return (tp, Oper(op, t1, t2))))
  | EAnnot(e', tp) -> check_kind tp Int >>= (fun tp -> 
                      check e' tp i >>= (fun t -> 
                      return (tp, t)))
  | _ -> error "cannot synthesize type for expression" 


and cover check branches tp i env =
  match env with
  | [] -> (match branches with
           | [] -> assert false
           | ([], e) :: branches' -> (check e tp i) >>= (fun v -> return (v, []))
           | (p :: ps, e) :: _ -> assert false)
  | (Hyp(_, _, _) as h) :: env' ->
    promote_stable h >>= (fun h ->
    let (sort, tp', i') = (match h with 
                           | Hyp(sort, tp', i') -> (sort, tp', i')
                           | _ -> assert false) in 
    simplify_heads (name_for_type tp') branches >>= (fun (u, branches) -> 
    with_hyp (u, h) 
    (match all_tops branches with
    | Some branches' -> cover check branches' tp i env' >>= (fun (v, us) -> return (v, u :: us))
    | None ->
      (* In this branch, we know we have nontrivial patterns *)
      subst tp' >>= (function 
      | Forall(a, Some k, tp1) ->
          fresh rename_tp a tp1 >>= (fun (a, tp1) ->
          let env = Hyp(sort, tp1, i') :: env' in 
          push (a, Type(Exist, k, None)) >>
          (cover check branches tp1 i env))
      | Exists(a, Some k, tp1) -> 
          fresh rename_tp a tp1 >>= (fun (a, tp1) -> 
          let env = Hyp(sort, tp1, i') :: env' in 
          with_hyp (a, Type(Univ, k, None)) (cover check branches tp1 i env))
      | Forall(_, None, _)
      | Exists(_, None, _) -> assert false 
      | TVar a ->
        lookup a >>= (function
          | Type(Exist, Int, None) ->
            specialize_set (map List.hd (map fst branches)) (TVar a) >>= (fun _ -> 
      	    cover check branches tp i env)
          | Type(Exist, Lin, _)   -> assert false
          | Type(_, Lin, Some _)  -> assert false
          | Data(Int, [], _)        -> cover check branches tp i (Hyp(sort, TApp(TVar a, []), i') :: env')
          | _ -> error "'%a' not a type variable of base kind" fmt_id a)
      | Pure tp'' when i = i' || sort = Stable && i' <= i ->
        split_pure branches >>= (fun branches -> 
        cover check branches tp i (Hyp(Stable, tp'', i') :: env') >>= (function
        | (t', u' :: us) -> return (Let(u', Run(Var u), t'), u :: us)
        | _              -> assert false))
      | Next tp'' when i = i' || sort = Stable && i' <= i ->
        split_next branches >>= (fun branches -> 
        cover check branches tp i (Hyp(Dyn, tp'', i' + 1) :: env') >>= (function 
        | (t', u' :: us) -> return (Let(u', Var u, t'), u :: us)
        | _ -> assert false))
      | Stream tp'' when i = i' || sort = Stable && i' <= i ->
        split_stream branches >>= (fun branches ->  
        cover check branches tp i (Hyp(sort, tp'', i') :: Hyp(Dyn, Stream tp'', i' + 1) :: env') >>= (function
        | (t', hd :: tl :: us) -> return (let_stream (hd, tl) u t', u :: us)
        | _ -> assert false))
      | TApp(TVar d, tps) when i = i' || sort = Stable && i' <= i ->
        lookup_datatype (d, tps) >>= (fun cenv ->
        seq (map (fun (c, tp'') ->
                      seq (map (function
                                | ((pos, PCon(c', p)) :: ps, e) when c = c' -> return (Some(p :: ps, e))
                                | ((pos, PCon(c', _)) :: ps, e) when List.mem_assoc c' cenv -> return None
                                | ((pos, PCon(c', _)) :: ps, e) -> error "unknown constructor '%s'" c' 
                                | ((pos, PTop) :: ps, e)        -> return (Some((pos, PTop) :: ps, e))
                                | ((pos, p) :: ps, e)           -> error "expected constructor pattern"
                                | ([], e)                       -> assert false)
                             branches) >>= (fun branches ->
                      let branches = filter_map (fun x -> x) branches in 
                      cover check branches tp i (Hyp(sort, tp'', i') :: env') >>= (function
                      | (t', u' :: us) -> return (c, u', t', us)
                      | _ -> assert false)))
                 cenv) >>= (function
         | [] -> return (Case(Var u, []), [u]) (* Weird, but right...! *)
         | (c, u', t, us) :: rest ->
             let rest = map (fun (c'', u'', t'', xs'') ->
                             let t'' = List.fold_right2 rename_term xs'' us t'' in 
                             (c'', u'', t''))
                            rest in
             let cases = (c, u', t) :: rest in
             return (Case(Var u, cases), u :: us)))
      | Product tps when i = i' || sort = Stable && i' <= i ->
        let hyps = map (fun tp -> Hyp(Dyn, tp, i')) tps in 
        split_tuple tps branches >>= (fun branches -> 
        cover check branches tp i (hyps @ env') >>= (fun (t', us'') -> 
        let (us', us) = break_list (List.length hyps) us'' in 
        return (let_tuple us' u t', u :: us)))
      | Product tps when sort = Dyn && i' = (i+1) ->
        let hyps = map (fun tp -> Hyp(Dyn, tp, i')) tps in 
        split_tuple tps branches >>= (fun branches -> 
        cover check branches tp i (hyps @ env') >>= (fun (t', us'') ->
        let (us', us) = break_list (List.length hyps) us'' in 
        return (let_lazy_tuple us' u t', u :: us)))
      | Pure _
      | Next _
      | Stream _
      | Product _
      | TApp(_, _) -> error "pattern at time %d, argument at time %d" i' i
      | Num         as tp' -> error "no patterns of type %a" fmt_tp tp'
      | String      as tp' -> error "no patterns of type %a" fmt_tp tp'
      | Bool        as tp' -> error "no patterns of type %a" fmt_tp tp'
      | G _         as tp' -> error "no patterns of type %a" fmt_tp tp'
      | Arrow(_, _) as tp' -> error "no patterns of type %a" fmt_tp tp'
      | Dom _
      | Frame _ 
      | Svg _
      | Tensor _
      | F _ 
      | Lolli(_,_)  -> error "Linear type in intuitionistic context"
      | _ -> raise (Higher_kinds "cover") ))))
  | (LHyp(_, _, Fresh) as h) :: env' ->
    promote_stable h >>= (fun h ->
    let (tp', i') = (match h with 
                     | LHyp(tp', i', _) -> (tp', i')
                     | _ -> assert false) in 
    simplify_heads (name_for_type tp') branches >>= (fun (u, branches) -> 
    with_hyp (u, h) 
    (match all_tops branches with
    | Some branches' -> cover check branches' tp i env' >>= (fun (t', us) -> return (t', u :: us))
    | None ->
      lookup u >>= (fun _ ->  (* use up the linear hyp u *)
      (match tp' with
      | Forall(a, Some k, tp1) ->
	  fresh rename_tp a tp1 >>= (fun (a, tp1) -> 
	  let env = LHyp(tp1, i', Fresh) :: env' in 
          push (a, Type(Exist, k, None)) >>
 	  (cover check branches tp1 i env))
      | Exists(a, Some k, tp1) ->
	  fresh rename_tp a tp1 >>= (fun (a, tp1) -> 
	  let env = LHyp(tp1, i', Fresh) :: env' in 
	  with_hyp (a, Type(Univ, k, None)) (cover check branches tp1 i env))
      | Forall(_, None, _)
      | Exists(_, None, _) -> assert false 
      | Tensor tps when i' = i ->
          let hyps = map (fun tp -> LHyp(tp, i', Fresh)) tps in 
          split_tensor tps branches >>= (fun branches -> 
          cover check branches tp i (hyps @ env') >>= (fun (t', us'') ->
          let (us', us) = break_list (length hyps) us'' in 
          return (let_tuple us' u t', u :: us)))
      | Tensor tps when  i' = i + 1 ->
	  let hyps = map (fun tp -> LHyp(tp, i', Fresh)) tps in 
          split_tensor tps branches >>= (fun branches -> 
          cover check branches tp i (hyps @ env') >>= (fun (t', us'') ->
          let (us', us) = break_list (length hyps) us'' in 
          return (let_lazy_tuple us' u t', u :: us)))
      | F tp1 when i' = i -> 
          split_f branches >>= (fun branches -> 
          cover check branches tp i (Hyp(Dyn, tp1, i') :: env') >>= (function
          | (t', u' :: us) -> return (Let(u', Var u, t'), u :: us)
          | _ -> assert false))
      | Next tp1 when i' = i -> 
          split_next_lin branches >>= (fun branches -> 
          cover check branches tp i (LHyp(tp1, i+1, Fresh) :: env') >>= (function
          | (t', u' :: us) -> return (Let(u', Var u, t'), u :: us)
          | _ -> assert false))
      | Dom tp1 when i' = i ->
	  split_dom branches >>= (fun branches -> 
          cover lcheck branches tp i (LHyp(Frame tp1, i', Fresh) :: LHyp(Dom tp1, i' + 1, Fresh) :: env') >>= (function
          | (t', hd :: tl :: us) -> return (let_dom (hd, tl) u t', u :: us)
          | _ -> assert false))

      | Dom _ 
      | Tensor _
      | F _ 
      | Next _ -> error "pattern at time %d, argument at time %d" i' i
      | _ -> error "no patterns at type %a" fmt_tp tp')))))
  |  _ :: _ -> error "matching on non term variable???" 

and lcheck e tp i =
  subst tp >>= (fun tp -> lcheck' e tp i)

and lcheck' ((pos, exp) as e) tp i =
  setpos pos >>
  match exp, tp with
  | _, _ when intro e && quantified tp -> 
    expand_for_intro tp >>= (fun tp -> lcheck e tp i)

  | ELam(p, e), Lolli(tp1, tp2) ->
    cover lcheck [[p], e] tp2 i [LHyp(tp1, i, Fresh)] >>= (function
    | (t2, [u]) -> return (Lam(u, t2))
    | _ -> assert false)
  | ELam(_, _), TVar a -> expand_evar a "lolli" expand_lolli >>
                          lcheck e tp i 
  | ELam(_, _), _      -> mismatch "lolli" tp

  | ENext e1, Next tp1 -> lcheck e1 tp1 (i+1) >>= (fun t1 ->
                          advance (freevars_exp e1) t1 i)
  | ENext _, TVar a -> expand_evar a "next" expand_next >>
                           lcheck e tp i 
  | ENext _, _      -> mismatch "next" tp

  | ETuple es, Tensor tps when length es = length tps ->
    seq (map2 (fun e tp -> lcheck e tp i) es tps) >>= (fun ts -> 
    return (Tuple ts))
  | ETuple es, Tensor tps ->
      error "tuple is length %d, tensor type is length %d" (length es) (length tps)
  | ETuple es, TVar a -> expand_evar a "tensor" (expand_tensor es) >>
                         lcheck e tp i 
  | ETuple _, _       -> mismatch "tensor" tp

  | EF e1, F tp1  -> with_nonlinear (check e1 tp1 i) (* We don't need to do anything to an intuitionistic term *)
  | EF e1, TVar a -> expand_evar a "F" expand_f >>
                     check e tp i
  | EF _, _       -> mismatch "F" tp 

  | ECons(e1, e2), Dom tp1 -> lcheck e1 (Frame tp1) i >>= (fun t1 ->
                              lcheck e2 (Dom tp1) (i+1) >>= (fun t2 ->
                              advance (freevars_exp e2) t2 i >>= (fun t2 -> 
				return (Merge(t1, t2)))))
  | ECons(e1, e2), TVar a -> expand_evar a "dom" expand_dom >>
                             lcheck e tp i 
  | ECons(e1, e2), _      -> mismatch "dom" tp

  | ELetVar(y, x, e2), tp2 ->
    fresh rename_exp y e2 >>= (fun (y, e2) -> 
    lookup x >>= (fun hyp ->
    promote_stable hyp >>= (fun hyp -> 
    with_hyp (y, hyp) (lcheck e2 tp2 i) >>= (fun t2 -> 
    return (Let(y, Var x, t2))))))

  | EIf(e1, e2, e3), tp2 ->
    with_nonlinear (check e1 Bool i) >>= (fun t1 -> 
    parallel [lcheck e2 tp2 i; lcheck e3 tp2 i] >>= (function
	| [t2; t3] -> return (If(t1, t2, t3))
	| _ -> assert false))
  | ELet(p, e1, e2), tp2 when checkable e1 ->
    newid "_alin" >>= (fun a ->
    push (a, Type(Exist, Lin, None)) >> 
    lspecialize p (TVar a) >>= (fun _ ->  
    check e1 (TVar a) i >>= (fun t1 ->
    cover lcheck [[p], e2] tp2 i [LHyp(TVar a, i, Fresh)] >>= (function
    | (t2, [u]) -> return (Let(u, t1, t2))
    | _ -> assert false))))
  | ELet(p, e1, e2), tp2 ->
    lsynth e1 i >>= (fun (tp1, t1) ->
    cover lcheck [[p], e2] tp2 i [LHyp(tp1, i, Fresh)] >>= (function
    | (t2, [u]) -> return (Let(u, t1, t2))
    | _ -> assert false))

  | EFix(x, e1), tp1 ->
    fresh rename_exp x e1 >>= (fun (x, e1) -> 
    with_pure_ctx (with_empty_lctx (with_hyp (x, LHyp(tp1, i+1, Fresh)) (lcheck e1 tp1 i)) >>= (fun t1 -> 
    return (Lazyfix(x, t1)))))

  | _, _ -> lsynth e i >>= (fun (tp', t) -> 
            (tp' <== tp) >>
	      return t)

and lsynth (pos, exp) i =
  setpos pos >> 
  match exp with
  | EVar x ->
    lookup x >>= (function
	| LHyp(tp, j, _) when i = j -> return (tp, Var x)
	| LHyp(tp, j, _) -> error "variable '%s' at time %d, used at %d" x j i
	| _ -> error "'%a' not a linear variable" fmt_id x)

  | EApp(e1, e2) ->
     lsynth e1 i >>= (fun (tp0, t1) ->
     expand_for_elim tp0 >>= (function 
     | Lolli(tp2, tp) -> 
	 lcheck e2 tp2 i >>= (fun t2 ->
	 return (tp, App(t1, t2)))
     | _ -> mismatch "function" tp0))

  | ERun(e1) ->
    synth e1 i >>= (fun (tp1, t) ->
    expand_for_elim tp1 >>= (function 
    | G(tp) -> return (tp, Run t)
    | _     -> mismatch "G" tp1))

  | EAnnot(e1, tp) ->
    check_kind tp Lin >>= (fun tp ->
    lcheck e1 tp i >>= (fun t -> 
    return (tp, t)))
    
  | _ -> error "cannot synthesize type for expression"
















