open Base
open Lexing

type 'a parse = (Lexing.lexbuf  -> Parser.token) -> Lexing.lexbuf -> 'a

let wrap p tokenize buf =
  try
    p tokenize buf 
  with
  | Failure msg -> raise (SyntaxError((buf.lex_start_p, buf.lex_curr_p), msg))
  | Parsing.Parse_error -> raise (SyntaxError((buf.lex_start_p, buf.lex_curr_p), "Parse error"))

let string p s = wrap p Lexer.token (Lexing.from_string s)

