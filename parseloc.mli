type 'a parse = (Lexing.lexbuf  -> Parser.token) -> Lexing.lexbuf -> 'a

val wrap : 'a parse -> 'a parse 

val string : 'a parse -> string -> 'a 

