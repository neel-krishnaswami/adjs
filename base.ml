(* Some basic types, common to every stage of the compiler *)

type id = string
type conid = string 
type op = Plus | Minus | Times | Equal | Lt | Leq | Gt | Geq | And | Or 

type pos = Lexing.position * Lexing.position
let dummy_pos = (Lexing.dummy_pos, Lexing.dummy_pos)

exception ParseError of Lexing.position * string 

let string_of_pos (beg, fin) =
  let line p = p.Lexing.pos_lnum in
  let col p = (p.Lexing.pos_cnum - p.Lexing.pos_bol) in
  Format.sprintf "%d.%d-%d.%d" (line beg) (col beg) (line fin) (col fin)

let print_op = function
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | Equal -> "==="
  | Lt -> "<"
  | Leq -> "<="
  | Gt -> ">"
  | Geq -> ">="
  | And -> "&&"
  | Or -> "||"



let foldr = List.fold_right
let foldr2 = List.fold_right2 
let map = List.map 
let map2 = List.map2
let length = List.length 
let rec filter_map f = function
  | [] -> []
  | x :: xs ->
    (match f x with
    | None -> filter_map f xs
    | Some y -> y :: filter_map f xs)

let rec fail_map f = function
  | [] -> Some []
  | x :: xs ->
      (match f x with
      | None -> None
      | Some y ->
          (match fail_map f xs with
          | Some ys -> Some (y :: ys)
          | None -> None))

let rec opt_find f = function
  | [] -> None
  | x :: xs -> (match f x with
                | None -> opt_find f xs 
		| Some y -> Some y)
		  
let opt_fold f default = function
  | None -> default
  | Some x -> f x

let rec break_list n xs =
  if n = 0 then
    ([], xs)
  else
    match xs with
    | [] -> assert false
    | x :: xs -> let (l, r) = break_list (n-1) xs in (x :: l, r)



let fmt_id () id = id 
(*
  try
    Scanf.sscanf id "%s@$%d" (fun name n -> name)
  with
    End_of_file -> id 
*)
let fmt_pos () pos = string_of_pos pos

let print_pos out pos = Format.fprintf out "%s" (string_of_pos pos)

let merge ((p, _), (_, q)) = (p,q)

exception SyntaxError of pos * string 

module Ids = Set.Make(struct type t = id let compare = compare end)
