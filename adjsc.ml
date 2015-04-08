open Base

type config = {
    stdlib: string;
    runtime: string;
    source: string;
    target: string;
    title: string;
}

let default = {
  stdlib = "";
  runtime = "";
  target = "a";
  source = "";
  title = ""
}

let process_args argv =
  let len = Array.length argv in 
  let rec loop i acc =
    if i < len then
      let (i, acc) =  
	try (match argv.(i) with
	| "-o" -> (i+2, {acc with target = argv.(i+1)})
	| "-I" -> (i+2, {acc with
			 stdlib = argv.(i+1) ^ "/stdlib.sig";
			 runtime = argv.(i+1) ^ "/runtime.js";
		      })
	| "-t" -> (i+2, {acc with title = argv.(i+1)})
	| filename when i = len - 1 -> (i+1, {acc with source = filename})
	| _ -> Printf.printf "unexpected end of arguments"; exit (-1))
	with
	| e -> Printf.printf "%s" (Printexc.to_string e); exit (-1)
      in
	loop i acc
    else
      acc
  in
  loop 1 default

let template config =
  let out = open_out (config.target ^ ".html") in
  let () = Printf.fprintf out "<html>
<head>
<title>%s</title>
</head>
<body onload=\"$start('app_root', $main)\">
<script type=\"text/javascript;version=1.8\" src=\"%s\"></script>
<script type=\"text/javascript;version=1.8\" src=\"%s.js\"></script>
<div id=\"app_root\"></div>
</body>
</html>" config.title config.runtime config.target in
  let () = close_out out in
  ()

let translate (stdlib, program) = 
  let cmd =  let (>>) = Context.(>>) in
	     Toplevel.process_signature stdlib >> 
	     Toplevel.elaborate program in
  match Context.run cmd [] Base.dummy_pos with
  | Context.Value(lams, _) -> Toplevel.translate_program lams
  | Context.Error msg -> raise (Toplevel.CompileError msg)
    
let parse stdlib_name program_name = 
    let sigparse = Parseloc.wrap Parser.signature Lexer.token  in
    let progparse = Parseloc.wrap Parser.program Lexer.token  in
    let stdlib = sigparse (Lexing.from_channel (open_in stdlib_name)) in 
    let program = progparse (Lexing.from_channel (open_in program_name)) in
    (stdlib, program)

let compile config =
  try
    let out = open_out (config.target ^ ".js") in
    let () = Pp.print (Js.print_stmts (translate (parse config.stdlib config.source))) out in
    let () = template config in
    let () = flush out in 
    let () = close_out out in
    ()
  with
    | Toplevel.CompileError msg -> Printf.printf "%s\n" msg; exit (-1)
    | SyntaxError(loc, msg) -> Printf.printf "%s: %s\n" (string_of_pos loc) msg; exit (-1)
    | e -> Printf.printf "%s\n" (Printexc.to_string e); exit (-1)

let _ = compile (process_args Sys.argv)













