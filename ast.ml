(* Syntax of the mixed linepar/nonlinear term language *)

open Base

type kind =
  | Int
  | Lin
  | KVar of id
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
  | Forall of id * kind option * tp
  | Exists of id * kind option * tp
  | TApp of tp * tp list
  | F of tp
  | Tensor of tp list
  | Lolli of tp * tp  
  | Dom of tp
  | Frame of tp 
  | Svg of tp
  | TVar of id 
  | TAnnot of tp * kind
  | TLam of id * tp
  | TLet of id * tp * tp 
      
type pat = pos * pat'
and pat' =
  | PTop 
  | PVar of id
  | PBang of pat
  | PCon of conid * pat
  | PCons of pat * pat 
  | PNext of pat
  | PTuple of pat list
  | PF of pat 

type exp = Base.pos * exp'
and exp' = 
  | EVar of id
  | EBang of exp
  | ENext of exp (* * exp *)
  | ETuple of exp list
  | ELam of pat * exp
  | EApp of exp * exp
  | EBool of bool
  | EIf of exp * exp * exp
  | ENum of float
  | EString of string
  | ECons of exp * exp
  | EAnnot of exp * tp
  | EFix of id * exp
  | ELoop of id * pat * exp  
  | EG of exp
  | EF of exp 
  | EOp of op * exp * exp
  | ECase of exp * branch list
  | ECon of conid * exp 
  | ELet of pat * exp * exp
  | ELetVar of id * id * exp 
  | ERun of exp 
and branch = (pat * exp)

type datatype = kind * (id * kind) list * (conid * tp) list 

type decl = 
  | DataBind of pos * id * datatype
  | ValueBind of (pos * id * exp * tp)
  | ValueDecl of (pos * id * tp)
  | TypeBind of (pos * id * tp * kind)
  | TypeDecl of (pos * id * kind)

type program = decl list * exp 

type signature_elt =
  | DataDecl of pos * id * datatype
  | SigTypeDecl of pos * id * tp 

type signature = signature_elt list 

let rec pat_eq (_, p) (_, q) = pat_eq' (p, q)
and pat_eq' = function
  | PTop, PTop                 -> true 
  | PVar x, PVar y             -> x = y 
  | PBang p, PBang q           -> pat_eq p q 
  | PCons(p, p'), PCons(q, q') -> pat_eq p q && pat_eq p' q'
  | PNext p, PNext q           -> pat_eq p q 
  | PF p, PF q                 -> pat_eq p q 
  | PCon(c, p), PCon(c', q) when c = c' -> pat_eq p q 
  | PTuple ps, PTuple qs when List.length ps = List.length qs ->
      List.for_all2 pat_eq ps qs
  | _, _ -> false 	     

let rec exp_eq (_, f) (_, g) = exp_eq' (f, g)
and exp_eq' = function
  | EVar x,          EVar x'           -> x = x'
  | EBang e, 	     EBang e'	       -> exp_eq e e'
  | ENext e,         ENext e'          -> exp_eq e e' 
(*  | ENext(e1,e2),    ENext(e1',e2')    -> exp_eq e1 e1' && exp_eq e2 e2' *)
  | ETuple es, 	     ETuple es'	       -> List.length es = List.length es' && List.for_all2 exp_eq es es'
  | ELam(p,e), 	     ELam(p',e')       -> pat_eq p p' && exp_eq e e'
  | EApp(e1,e2),     EApp(e1',e2')     -> exp_eq e1 e1' && exp_eq e2 e2'
  | EBool b,         EBool b'	       -> b = b'
  | ECons(e1,e2),    ECons(e1',e2')    -> exp_eq e1 e1' && exp_eq e2 e2'
  | EIf(e1,e2,e3),   EIf(e1',e2',e3')  -> exp_eq e1 e1' && exp_eq e2 e2' && exp_eq e3 e3'
  | ENum float,      ENum float'       -> float = float'
  | EString string,  EString string'   -> string = string'
  | EAnnot(e,ftype), EAnnot(e',ftype') -> ftype = ftype' && exp_eq e e'
  | EFix(x,e),       EFix(x',e')       -> x = x' && exp_eq e e'
  | ELoop(x,p,e),    ELoop(x',p',e')   -> x = x' && pat_eq p p' && exp_eq e e'
  | EF e,            EF e'             -> exp_eq e e'
  | EG lexp,         EG lexp'	       -> exp_eq lexp lexp'
  | EOp(op,e1,e2),   EOp(op',e1',e2')  -> op = op' && exp_eq e1 e1' && exp_eq e2 e2'
  | ELet(p,e1,e2),   ELet(p',e1',e2')  -> pat_eq p p' && exp_eq e1 e1' && exp_eq e2 e2'
  | ECase(e, bs),    ECase(e', bs')    -> exp_eq e e' && List.for_all2 branch_eq bs bs'
  | ECon(c, e),      ECon(c', e')      -> c = c' && exp_eq e e'
  | ERun e,          ERun e'           -> exp_eq e e' 
  | _, _                               -> false
 
and branch_eq (p, e) (p', e') = pat_eq p p' && exp_eq e e'

let (singleton, union, empty, add, diff, remove, mem) =
  (Base.Ids.singleton, Base.Ids.union, Base.Ids.empty, Base.Ids.add, Base.Ids.diff, Base.Ids.remove, Base.Ids.mem)

let rec freevars_kind = function
  | Int -> empty
  | Lin -> empty
  | KArrow(k1, k2) -> union (freevars_kind k1) (freevars_kind k2)
  | KVar x -> singleton x 

let rec freevars_tp = function
  | Num
  | Bool
  | String              -> empty
  | Pure tp
  | Next tp
  | Stream tp
  | G tp
  | F tp
  | Frame tp 
  | Dom tp 
  | Svg tp              -> freevars_tp tp
  | Forall (id, None, tp)
  | Exists (id, None, tp)     -> remove id (freevars_tp tp)
  | Forall (id, Some k, tp)
  | Exists (id, Some k, tp)   -> union (freevars_kind k) (remove id (freevars_tp tp))
  | Lolli (tp, tp')     
  | Arrow (tp, tp')     -> union (freevars_tp tp) (freevars_tp tp')
  | Product tps
  | Tensor tps          -> freevars_tp_list tps 
  | TApp (tp, tps)      -> union (freevars_tp tp) (freevars_tp_list tps)
  | TVar id             -> singleton id
  | TAnnot(tp, kind)    -> union (freevars_tp tp) (freevars_kind kind)
  | TLet(a, tp1, tp2)   -> union (freevars_tp tp1)
                                 (remove a (freevars_tp tp2))
  | TLam(a, tp)         -> remove a (freevars_tp tp)

and freevars_tp_list tps = List.fold_left union empty (List.map freevars_tp tps)

let rec rename_kind a b = function
  | Int -> Int
  | Lin -> Lin
  | KArrow(k1, k2) -> KArrow(rename_kind a b k1, rename_kind a b k2)
  | KVar a' -> if a = a' then KVar b else KVar a

let rec rename_tp a a' = function 
  | Num                     -> Num
  | Bool                    -> Bool
  | String                  -> String
  | Pure tp                 -> Pure (rename_tp a a' tp)
  | Next tp                 -> Next (rename_tp a a' tp)
  | Stream tp               -> Stream (rename_tp a a' tp)
  | G tp                    -> G (rename_tp a a' tp)
  | F tp                    -> F (rename_tp a a' tp)
  | Dom tp                  -> Dom (rename_tp a a' tp)
  | Frame tp                -> Frame (rename_tp a a' tp)
  | Svg tp                  -> Svg (rename_tp a a' tp) 
  | Forall (id, None, tp)   -> Forall(id, None, if a = id then tp else rename_tp a a' tp)
  | Exists (id, None, tp)   -> Exists(id, None, if a = id then tp else rename_tp a a' tp)
  | Forall (id, Some k, tp) -> Forall(id, Some (rename_kind a a' k), if a = id then tp else rename_tp a a' tp)
  | Exists (id, Some k, tp) -> Exists(id, Some (rename_kind a a' k), if a = id then tp else rename_tp a a' tp)
  | Lolli (tp, tp')         -> Lolli(rename_tp a a' tp, rename_tp a a' tp')
  | Arrow (tp, tp')         -> Arrow(rename_tp a a' tp, rename_tp a a' tp')
  | Product tps             -> Product (List.map (rename_tp a a') tps)
  | Tensor tps              -> Tensor (List.map (rename_tp a a') tps)
  | TApp (tp, tps)          -> TApp(rename_tp a a' tp,
                                    map (rename_tp a a') tps)
  | TVar id                 -> TVar (if id = a then a' else id)
  | TAnnot(tp, k)           -> TAnnot(rename_tp a a' tp, rename_kind a a' k)
  | TLet(b, tp1, tp2)       -> TLet(b,
                                    rename_tp a a' tp1,
                                    if a = b then tp2 else rename_tp a a' tp2)
  | TLam(b, tp) when a =b   -> TLam(b, tp)
  | TLam(b, tp)             -> TLam(b, rename_tp a a' tp)
      
                                    

let rec pvars (_, p) =
  match p with
  | PTop        -> empty
  | PVar id     -> singleton id
  | PBang p     -> pvars p
  | PCon(c, p)  -> pvars p 
  | PNext p     -> pvars p
  | PF p        -> pvars p
  | PCons(p,p') -> union (pvars p) (pvars p')
  | PTuple ps   -> List.fold_left union empty (List.map pvars ps)

let rec freevars_exp (_, e) =
  match e with 
  | EVar x -> singleton x 
  | ENext e
  | EBang e -> freevars_exp e
  | EAnnot(e, tp) -> union (freevars_exp e) (freevars_tp tp)
  | ETuple es -> List.fold_left union empty (List.map freevars_exp es)
  | ELam(p, e) -> diff (freevars_exp e) (pvars p)
  | EOp(_, e1, e2)
  | ECons(e1, e2)
  | EApp(e1, e2) -> union (freevars_exp e1) (freevars_exp e2)
  | EBool _
  | ENum _
  | EString _ -> empty
  | EIf(e1, e2, e3) -> union (freevars_exp e1) (union (freevars_exp e2) (freevars_exp e3))
  | EFix(x, e) -> remove x (freevars_exp e)
  | ELoop(f, p, e) -> remove f (diff (freevars_exp e) (pvars p))
  | EG lexp -> freevars_exp lexp
  | ELet(p, e1, e2) -> union (freevars_exp e1) (diff (freevars_exp e2) (pvars p))
  | ELetVar(x, y, e) -> union (singleton y) (diff (freevars_exp e) (singleton x))
  | ECase(e, branches) -> union (freevars_exp e) (freevars_branches branches)
  | ECon(c, e) -> freevars_exp e
  | EF e -> freevars_exp e
  | ERun e -> freevars_exp e 

and freevars_branches bs = 
  match bs with 
  | [] -> empty
  | (p, e) :: rest -> union (freevars_branches rest) (diff (freevars_exp e) (pvars p))

let rec rename_exp x x' (pos, e) = (pos, rename' x x' e)
and rename' x x' e = 
  match e with 
  | EVar y             -> if x = y then EVar x' else EVar y
  | EAnnot(e, tp)      -> EAnnot(rename_exp x x' e, rename_tp x x' tp)
  | EBang e            -> EBang (rename_exp x x' e)
  | ENext e            -> ENext (rename_exp x x' e)
  | ETuple es          -> ETuple (List.map (rename_exp x x') es)
  | ELam(p, e)         -> if mem x (pvars p) then ELam(p, e) else ELam(p, rename_exp x x' e)
  | EOp(op, e1, e2)    -> EOp(op, rename_exp x x' e1, rename_exp x x' e2)
  | EApp(e1, e2)       -> EApp(rename_exp x x' e1, rename_exp x x' e2)
  | EBool b            -> EBool b
  | ENum n             -> ENum n 
  | EString s          -> EString s
  | ECons(e1, e2)      -> ECons(rename_exp x x' e1, rename_exp x x' e2)
  | EIf(e1, e2, e3)    -> EIf(rename_exp x x' e1, rename_exp x x' e2, rename_exp x x' e3)
  | EFix(y, e)         -> if x = y then EFix(y, e) else EFix(y, rename_exp x x' e)
  | ELoop(f, p, e)     -> if x = f || mem x (pvars p) then ELoop(f, p, e) else ELoop(f, p, rename_exp x x' e)
  | EG lexp            -> EG (rename_exp x x' lexp)
  | ELet(p, e1, e2)    -> ELet(p, rename_exp x x' e1, if mem x (pvars p) then e2 else rename_exp x x' e2)
  | ELetVar(y, z, e)   -> ELetVar(y, (if x = z then x' else z), if x = y then e else rename_exp x x' e)
  | ECase(e, branches) -> ECase(rename_exp x x' e, rename_branches x x' branches)
  | ECon(c, e)         -> ECon(c, rename_exp x x' e)
  | EF e               -> EF (rename_exp x x' e)
  | ERun e             -> ERun (rename_exp x x' e)

and rename_branches x x' bs =
  List.map (fun (p, e) -> if mem x (pvars p) then (p, e) else (p, rename_exp x x' e)) bs 


let rec string_of_kind = function
  | Int -> "int"
  | Lin -> "lin"
  | KArrow(KArrow(_, _) as k1, k2) ->
      Printf.sprintf "(%s) -> %s" (string_of_kind k1) (string_of_kind k2)
  | KArrow(k1, k2) ->
      Printf.sprintf "%s -> %s" (string_of_kind k1) (string_of_kind k2)
  | KVar x -> x 

let rec self_delimited = function
  | Num
  | Bool
  | String
  | Product _
  | Tensor _
  | TVar _ -> true 
  | TApp(tp, []) -> self_delimited tp
  | _ -> false

let rec string_of_tp = function
  | Num -> "num"
  | Bool -> "bool"
  | String -> "string"
  | Pure tp -> Printf.sprintf "!%s" (string_of_tp tp)
  | Stream tp -> Printf.sprintf "stream(%s)" (string_of_tp tp)
  | Next tp -> Printf.sprintf "next(%s)" (string_of_tp tp)
  | G ltp -> Printf.sprintf "G(%s)" (string_of_tp ltp)
  | Product tps -> Printf.sprintf "(%s)" (String.concat " & " (List.map string_of_tp tps))
  | Arrow(Arrow(_, _) as tp1, tp2) ->
      Printf.sprintf "(%s) -> %s" (string_of_tp tp1) (string_of_tp tp2)
  | Arrow(tp1, tp2) ->
      Printf.sprintf "%s -> %s" (string_of_tp tp1) (string_of_tp tp2)
  | Tensor tps -> Printf.sprintf "(%s)" (String.concat " * " (List.map string_of_tp tps))
  | Dom tp -> Printf.sprintf "dom(%s)" (string_of_tp tp)
  | Frame tp -> Printf.sprintf "frame(%s)" (string_of_tp tp)
  | Svg tp -> Printf.sprintf "svg(%s)" (string_of_tp tp)
  | F ftype -> Printf.sprintf "F(%s)" (string_of_tp ftype)
  | Lolli((Lolli(_, _)) as tp1, tp2) ->
      Printf.sprintf "(%s) -o %s" (string_of_tp tp1) (string_of_tp tp2)
  | Lolli(tp1, tp2) ->
      Printf.sprintf "%s -o %s" (string_of_tp tp1) (string_of_tp tp2)
  | Forall(a, None, tp) -> Printf.sprintf "forall %s:?. %s" a (string_of_tp tp)
  | Forall(a, Some k, tp) -> Printf.sprintf "forall %s:%s. %s" a (string_of_kind k) (string_of_tp tp)
  | Exists(a, None, tp) -> Printf.sprintf "exists %s:?. %s" a (string_of_tp tp)
  | Exists(a, Some k, tp) -> Printf.sprintf "exists %s:%s. %s" a (string_of_kind k) (string_of_tp tp)
  | TVar a -> a
  | TApp(tp, tps) ->
      let pr tp =
        if self_delimited tp
        then Printf.sprintf "%s" (string_of_tp tp)
        else string_of_tp tp
      in 
      String.concat " " (map pr (tp :: tps))
  | TLet(a, tp, tp') -> Printf.sprintf "let %s = %s in %s" a (string_of_tp tp) (string_of_tp tp')
  | TLam(a, tp) -> Printf.sprintf "fun %s -> %s" a (string_of_tp tp)
  | TAnnot(tp, k) -> Printf.sprintf "(%s : %s)" (string_of_tp tp) (string_of_kind k)
      

let rec string_of_kind = function
  | Lin -> "lin"
  | Int -> "int"
  | KVar a -> a
  | KArrow(KArrow(_, _) as k1, k2) -> Printf.sprintf "(%s) -> %s" (string_of_kind k1) (string_of_kind k2)
  | KArrow(k1, k2) -> (string_of_kind k1) ^ " -> " ^ (string_of_kind k2)

let fmt_tp () = string_of_tp
let fmt_kind () = string_of_kind

let exp_pos (pos, _) = pos
let pat_pos (pos, _) = pos







