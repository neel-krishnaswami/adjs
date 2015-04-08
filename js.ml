(* Abstract Syntax for a fragment of Javascript

   Our goal is to translate terms of our lambda-calculus into Javascript.
   This is slightly complicated since Javascript has a statement/expression
   distinction, and the lambda calculus doesn't. Furthermore, it would be 
   nice if we could generate reasonably natural-looking JS code.

   To address both of these issues, we will use a "destination-passing style"
   translation, which is basically a kind of baby CPS transform. 

*)

open Base 
open Pp 

type exp =
  | Int of int 
  | Num of float
  | Bool of bool
  | Fun of id option * id list * statement list
  | String of string
  | Id of id
  | Apply of exp * exp list
  | Op of op * exp * exp
  | Array of exp list
  | Deref of exp * exp
  | Method of exp * string * exp list
  | New of string * exp list 

and statement =
  | LetNull of id 
  | LetVar of id * exp
  | LetDef of id * exp 
  | Return of exp
  | IfThenElse of exp * statement list * statement list
  | Assign of id * exp
  | WhileTrue of statement list
  | Continue
  | Abort
  | Break 
  | Switch of exp * (Base.conid * statement list) list 
     
type 'a optree =
  | Leaf of 'a
  | Node of op * 'a optree * 'a optree

let rec opify = function
  | Op(op, e1, e2) -> Node(op, opify e1, opify e2)
  | e -> Leaf e

let precedence = function
  | Or -> 1
  | And -> 2
  | Equal -> 3
  | Lt | Leq | Gt | Geq -> 4
  | Plus | Minus -> 5
  | Times -> 6


let print_operator print_leaf optree =
  let rec loop prec = function    (* prec is the current precedence *)
    | Node(op, o1, o2) ->
        let parenthesize printer = seq [str "("; atcol printer; str ")"] in
	let p = precedence op in
        let exp = seq [loop p o1; str " "; str (print_op op); str " "; loop p o2] in
        if prec > p then parenthesize exp else exp 
    | Leaf t -> print_leaf t
  in loop 0 optree


let rec print_exp = function
  | Int n ->                  int n
  | Num x ->                  float x
  | Bool b ->                 bool b
  | String s ->               qstr s 
  | Fun(None, xs, stmts) ->   seq [str "function "; print_args (map str xs); print_block stmts]
  | Fun(Some f, xs, stmts) -> seq [str "function "; str f; print_args (map str xs); print_block stmts]
  | Id x ->                   str x
  | Apply(e, es) ->           seq [print_exp e; print_args (map print_exp es)]
  | Op(_, _, _) as e ->       print_operator print_exp (opify e)
  | New(classname, args) ->   seq [str "new "; str classname; print_args (map print_exp args)]
  | Array es ->               print_array (map print_exp es)
  | Deref(e, e') ->           seq [print_exp e; str "["; print_exp e'; str "]"]
  | Method((Id _) as e, name, args) 
  | Method((Method(_, _, _)) as e, name, args) ->  
                              seq [print_exp e; str "."; str name; print_args (map print_exp args)]
  | Method(e, name, args) ->  seq [str "("; print_exp e; str ")."; str name; print_args (map print_exp args)]

and print_sequence left right sep ps =
  let b = List.exists multiline ps in
  let rec loop = function
    | [] -> nil
    | [p] -> p
    | p :: ps -> seq [p; sep; break b; loop ps]
  in
  seq [left; atcol (loop ps); right]

and print_args (args : Pp.printer list) = print_sequence (str "(") (str ")") (str ",") args
and print_array (args : Pp.printer list) = print_sequence (str "[") (str "]") (str ",") args

and print_stmt (s : statement) : Pp.printer =
  match s with 
  | Abort            -> seq [str "throw "; qstr "Impossible branch -- compiler error"; str ";"]
  | LetNull x        -> seq (map str ["let "; x; "= null;"])
  | LetVar(x, e) 
  | LetDef(x, e)     -> seq [str "let "; str x; str " = "; print_exp e; str ";"]
  | Continue         -> str "continue;"
  | Break            -> str "break;"
  | Return e         -> seq [str "return "; print_exp e; str ";"]
  | IfThenElse(e, s1, s2) -> seq [str "if ("; print_exp e; str ") ";
				  print_block s1;
				  str " else ";
				  print_block s2]
  | Assign(x, e)     -> seq [str x; str " = "; print_exp e; str ";"]
  | WhileTrue stmts  -> seq [str "while (true) "; print_block stmts]
  | Switch(e, cases) -> seq [str "switch ("; print_exp e; str ") "; print_cases cases]
    
and print_block stmts =
  seq [str "{";
       indent 2 (seq (map (fun s -> seq [nl; print_stmt s]) stmts));
       nl;
       str "}"]

and print_case (x, stmts) =
  seq [str "case "; qstr x; str ":";
       indent 2 (seq (map (fun s -> seq [nl; print_stmt s]) stmts));
       nl]

and print_cases cases =
  seq [str "{";
       indent 2 (seq (map (fun case -> seq [nl; print_case case]) cases));
       str "}"]

let print_stmts stmts =
  seq [seq (map (fun s -> seq [nl; print_stmt s]) stmts);
       nl]
       
