open Base
open Js
open Lambda

type dest = CallReturn | Ident of id
type tailcall = Nontail | TailCall of id * id 

let option d = function None -> d | Some e -> e
let return tgt r =
  match tgt, r with
  | _, None -> []
  | CallReturn, Some e -> [Return e]
  | Ident x, Some e -> [Assign(x, e)]

let rec translate term =
  let increment = let r = ref 0 in fun () -> (incr r; !r) in
  let newdest () = Printf.sprintf "$d_%d" (increment ()) in
  let freshen x = Printf.sprintf "%s_%d" x (increment()) in 
  let extend x x' rho y = if x = y then x' else rho y in
  let expify f x =
    let d = newdest() in
    let (s, r) = f (Ident d) x in
    (s, option (Id d) r)
  in
  let apply tail e1 e2 =
    match tail, e1 with
    | TailCall(f,x), Id f' when f = f' ->
	([Assign(x, e2); Continue], None)
    | _, _ -> ([], Some (Apply(e1, [e2])))
  in
  let initialize = function
    | CallReturn -> []
    | Ident x -> [LetNull x]
  in 
  let rec loop rho tail d = function
    | Var x -> ([], Some (Id (rho x)))
    | LitString s -> ([], Some (String s))
    | LitNum n -> ([], Some (Num n))
    | LitBool b -> ([], Some (Bool b))
    | App(t1, t2) ->
	let (s1, e1) = expify (loop rho Nontail) t1 in
	let (s2, e2) = expify (loop rho Nontail) t2 in
	let (s3, r3) = apply tail e1 e2 in 
	(s1 @ s2 @ s3, r3)
    | Oper(op, t1, t2) ->
	let (s1, e1) = expify (loop rho Nontail) t1 in 
	let (s2, e2) = expify (loop rho Nontail) t2 in
	(s1 @ s2, Some(Op(op, e1, e2)))
    | Merge(t1, t2) ->
	let (s1, e1) = expify (loop rho Nontail) t1 in 
	let (s2, e2) = expify (loop rho Nontail) t2 in
	(s1 @ s2, Some (Apply(Id "mergePrim", [e1; e2])))
    | Tuple ts ->
	let (stmts, es) = List.split (List.map (expify (loop rho Nontail)) ts) in 
	(List.concat stmts, Some(Array es))
    | Project(i, t) ->
	let (s, e) = expify (loop rho Nontail) t in
	(s, Some(Deref(e, Int i)))
    | If(t1, t2, t3) ->
	let (s1, e1) = expify (loop rho Nontail) t1 in
	let (s2, r2) = loop rho tail d t2 in
	let (s3, r3) = loop rho tail d t3 in
	(s1 @ initialize d @ [IfThenElse(e1, s2 @ return d r2, s3 @ return d r3)], None)
    | Lam(x, t) ->
	let x' = freshen x in
	let rho = extend x x' rho in
	let (s, r) = loop rho Nontail CallReturn t in
	([], Some (Fun(None, [x'], s @ return CallReturn r)))
    | Let(x, t1, t2) ->
	let x' = freshen x in
	let (s1, r1) = loop rho Nontail (Ident x') t1 in
	let rho = extend x x' rho in
	let (s2, r2) = loop rho tail d t2 in
	(match r1 with
	 | None -> (s1 @ s2, r2)
	 | Some e -> (s1 @ [LetVar(x',e)] @ s2, r2))
    | Lazy t -> 
	let (s, r) = loop rho Nontail CallReturn t in
	([], Some (New("Lazy", [Fun(None, [], s @ return CallReturn r)])))
    | Force t ->
	let (s, e) = expify (loop rho Nontail) t in
	(s, Some(Method(e, "force", [])))
    | Thunk t -> 
	let (s, r) = loop rho Nontail CallReturn t in
	([], Some (Fun(None, [], s @ return CallReturn r)))
    | Run t ->
	let (s, e) = expify (loop rho Nontail) t in
	(s, Some(Apply(e, [])))
    | Fix(f, x, t) ->
        let  f' = freshen f in
	let outer = freshen x in
	let inner = freshen x in 
	let rho = extend f f' rho in 
	let rho = extend x inner rho in 
	let rho = extend f f' rho in
	let (s, r) = loop rho (TailCall(f',outer)) CallReturn t in
	let s = [WhileTrue ([LetVar(inner, Id outer)] @ s @ return CallReturn r)] in
	([], Some (Fun(Some f', [outer], s)))
    | Lazyfix(x, t) ->
	let x' = freshen x in
	let rho = extend x x' rho in
	let (s, r) = loop rho Nontail CallReturn t in
	([], Some (Apply(Id "lazyfix", [Fun(None, [x'], s @ return CallReturn r)])))
    | Head t ->
	let (s, e) = expify (loop rho Nontail) t in
	(s, Some(Method(e, "head", [])))
    | Tail t -> 
	let (s, e) = expify (loop rho Nontail) t in
	(s, Some(Method(e, "tail", [])))
    | Cons(t1, t2) ->
	let (s1, e1) = expify (loop rho Nontail) t1 in 
	let (s2, e2) = expify (loop rho Nontail) t2 in
	(s1 @ s2, Some(New("Cons", [e1; e2])))
    | Con(c, t1) ->
        let (s1, e1) = expify (loop rho Nontail) t1 in
	(s1, Some(Array[String c; e1]))
    | Case(t0, arms) ->
        let (s0, e0) = expify (loop rho Nontail) t0 in
	let con = Deref(e0, Int 0) in
	let value = Deref(e0, Int 1) in
	let break d = match d with CallReturn -> [] | Ident _ -> [Break] in  
	let branch (c, x, t) =
	  let x' = freshen x in
	  let rho = extend x x' rho  in 
	  let (s, r) = loop rho tail d t in
	  (c, [LetVar(x', value)] @ s @ return d r @ break d)
	in 
	(s0 @ initialize d @ [Switch(con, map branch arms)], None)
  in
  expify (loop (fun x -> x) Nontail) term 

 			
