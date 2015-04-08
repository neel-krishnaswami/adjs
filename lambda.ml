(* Lambda Calculus 

This module contains a simple dynamically-typed lambda calculus a la Scheme, which
is the intermediate language for our compiler. The compiler workflow is the usual
story of "typecheck the program with fancy types, throw away the types, and generate code".

In this case, the purpose of the IR is to paper over the general insanity involved in 
anything touching Javascript (bizarre scoping, variable semantics, statement/expression 
distinctions, etc). 

*)

open Base 

type term =
  | Var of id
  | Lam of id * term
  | LitNum of float
  | LitBool of bool
  | LitString of string 
  | App of term * term
  | Oper of op * term * term 
  | If of term * term * term
  | Tuple of term list
  | Project of int * term
  | Let of id * term * term
  | Fix of id * id * term
  | Lazyfix of id * term 
  | Cons of term * term
  | Head of term
  | Tail of term
  | Lazy of term
  | Force of term
  | Thunk of term
  | Run of term 
  | Con of conid * term
  | Merge of term * term
  | Case of term * (conid * id * term) list 

let atom = function
  | Var _
  | LitString _
  | LitNum _
  | LitBool _
  | Tuple _ -> true
  | _ -> false

let sameop op = function
  | Oper(op', _, _) -> op = op'
  | _ -> false

let let_tuple xs x e =
  let rec loop i = function
    | [] -> e
    | y :: ys -> Let(y, Project(i, Var x), loop (i+1) ys)
  in
  loop 0 xs

let let_stream (h,t) x e =
  Let(h, Head(Var x), Let(t, Tail(Var x), e))

(* Not sure this is good sw-eng practice --
   split in the runtime should be reified in the lam type,
   just like Merge *)

let frame w = Var w
let future w = Lazy (Var w)

let let_dom (h,t) x e =
  Let(h, frame x, Let(t, future x, e))

let let_lazy_tuple xs x e =
  let lazy_project i x = Lazy(Let(x, Force(Var x), Project(i, Var x))) in
  let rec loop i = function
    | [] -> e
    | y :: ys -> Let(y, lazy_project i x, loop (i+1) ys)
  in
  loop 0 xs

let rename_term x x' term =
  let rec loop = function 
  | Var y -> if x = y then Var x' else Var y
  | Lam(y, t) -> if x = y then Lam(y, t) else Lam(y, loop t)
  | LitNum n -> LitNum n
  | LitBool b -> LitBool b
  | LitString s -> LitString s 
  | App(t1, t2) -> App(loop t1, loop t2)
  | Merge(t1, t2) -> Merge(loop t1, loop t2)
  | If(t1, t2, t3) -> If(loop t1, loop t2, loop t3)
  | Oper(op, t1, t2) -> Oper(op, loop t1, loop t2)
  | Tuple ts -> Tuple (map loop ts)
  | Con(c, t) -> Con(c, loop t)
  | Project(i, t) -> Project(i, loop t)
  | Let(y, t1, t2) -> Let(y, loop t1, if x = y then t2 else loop t2)
  | Fix(f, y, t) -> if x = f || x = y then Fix(f, y, t) else Fix(f, y, loop t)
  | Lazyfix(y, t) -> if x = y then Lazyfix(y, t) else Lazyfix(y, loop t)
  | Cons(t1, t2) -> Cons(loop t1, loop t2)
  | Head t -> Head (loop t)
  | Tail t -> Tail (loop t)
  | Lazy t -> Lazy (loop t)
  | Force t -> Force (loop t)
  | Thunk t -> Thunk (loop t)
  | Run t -> Run (loop t)
  | Case(t, branches) -> Case(loop t, map (fun (c, y, t) -> if x = y then (c, y, t) else (c, y, loop t)) branches)
  in
  loop term

let print = Format.fprintf 

let rec print_term out = function
  | Var x -> print out "%s" x
  | Lam(x, t) -> print out "\\%s. @[<hv>%a@]@," x print_term t 
  | LitNum n -> print out "%f" n
  | LitBool b -> if b then print out "true" else print out "false"
  | LitString s -> print out "\"%s\"" (String.escaped s)
  | App(t1, t2) -> print out "%a@ %a" print_term t1 print_atom t2
  | If(t1, t2, t3) -> print out "@[if@ %a@ then@\n@ @ @[<hv>%a@]@\nelse@\n@ @ @[<hv>%a@]@]" print_term t1 print_term t2 print_term t3
  | Oper(op, t1, t2) -> print out "(%a@ %s@ %a)" print_term t1 (print_op op) print_atom t2
  | Tuple ts -> print out "(%a)" print_seq ts
  | Con(c, t) -> print out "%s(%a)" c print_term t 
  | Project(i, t) -> print out "%a[%d]" print_atom t i
  | Let(x, t1, t2) -> print out "@[<hov>let@ %s@ =@;<1 2>@[<hv>%a@]@ in@\n@[<hv>%a@]@]" x print_term t1 print_term t2 
  | Fix(f, x, t) -> print out "@[<hov 2>loop@ %s@ %s. @[<hv>%a@]@]" f x print_term t 
  | Lazyfix(x, t) -> print out "@[<hov 2>fix@ %s. @[<hv>%a@]@]" x print_term t
  | Cons(t1, t2) -> print out "%a@ ::@ %a" print_atom t1 print_atom t2 
  | Head t -> print out "head@ %a" print_atom t
  | Tail t -> print out "tail@ %a" print_atom t
  | Lazy t -> print out "lazy@ %a" print_atom t
  | Force t -> print out "force@ %a" print_atom t
  | Thunk t -> print out "thunk@ %a" print_atom t
  | Run t   -> print out "run@ %a" print_atom t
  | Merge(t1, t2) -> print out "%a@ ::@ %a" print_term t1 print_atom t2
  | Case(t, branches) -> print out "case(%a, @[%a@])" print_term t print_branches branches

and print_atom out t = 
  if atom t then print_term out t else print out "(%a)" print_term t 

and print_seq out = function
  | [] -> ()
  | [t] -> print_term out t
  | t :: ts -> print out "%a,@ %a" print_term t print_seq ts

and print_branch out (c, x, t) = print out "%s(%s) -> %a" c x print_term t

and print_branches out = function
  | [] -> ()
  | [b] -> print_branch out b 
  | t :: ts -> print out "%a,@ %a" print_branch t print_branches ts

	

let fact =
  Let("fact",
      Fix("fact", "n",
	  If(Oper(Equal, Var "n", LitNum 0.0),
	     LitNum 1.0,
	     Let("v", App(Var "fact", Oper(Minus, Var "n", LitNum 1.0)),
		 Oper(Times, Var "n", Var "v")))),
      App(Var "fact", LitNum 5.0))

let fact_tr =
  Let("fact_tr",
      Fix("fact_tr", "nacc",
	  Let("n", Project(0, Var "nacc"),
	      Let("acc", Project(1, Var "nacc"),
		  If(Oper(Equal, Var "n", LitNum 0.0),
		     LitNum 1.0,
		     Let("m", Oper(Minus, Var "n", LitNum 1.0),
			 Let("acc", Oper(Times, Var "n", Var "acc"),
			     App(Var "fact_tr",
				 Tuple [Var "m"; Var "acc"]))))))),
	Let("fact", Lam("n", App(Var "fact_tr", Tuple [Var "n"; LitNum 1.0])),
	    App(Var "fact", LitNum 5.0)))

let countdown =
  Let("countdown",  Fix("countdown", "n",
			If(Oper(Equal, Var "n", LitNum 0.0),
			   LitNum 0.0,
			   Let("m", Oper(Minus, Var "n", LitNum 1.0),
			       App(Var "countdown", Var "m")))),
      App(Var "countdown", LitNum 5.0))




