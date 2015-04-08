let ftype s = Parser.test_ftype Lexer.token (Lexing.from_string s)
let ltype s = Parser.test_ltype Lexer.token (Lexing.from_string s)
let fexp s = Parser.test_fexp Lexer.token (Lexing.from_string s)
let lexp s = Parser.test_lexp Lexer.token (Lexing.from_string s)
let toplevel s = Parser.toplevel Lexer.token (Lexing.from_string s)
let sig_list s = Parser.sig_list Lexer.token (Lexing.from_string s)
let pat s = Parser.pat Lexer.token (Lexing.from_string s)
    
let run = Unittest.run Format.std_formatter


let ftype_tests =
  let open Unittest in 
  let open Ast in 
  group
    "Nonlinear types"
    [ test "bool" (fun () ->
        Bool = ftype "bool");
      test "unit" (fun () ->
	Product [] = ftype "unit");
      test "string" (fun () ->
	String = ftype "string");
      test "num" (fun () ->
	Num = ftype "num");
      test "(bool)" (fun () ->
	Bool = ftype "(bool)");
      test "bool & bool" (fun () ->
	Product [Bool; Bool] = ftype "bool & bool");
      test "(bool & bool)" (fun () ->
	Product [Bool; Bool] = ftype "(bool & bool)");
      test "next bool" (fun () -> NextType Bool = ftype "next bool");
      test "next bool & next bool" (fun () ->
	Product [NextType Bool; NextType Bool] = ftype "next bool & next bool");
      test "!bool" (fun () ->
	Pure Bool = ftype "!bool");
      test "!bool & !bool" (fun () ->
	Product [Pure Bool; Pure Bool] = ftype "!bool & !bool");
      test "!next bool" (fun () ->
	Pure (NextType Bool) = ftype "!next bool");
      test "next !bool" (fun () ->
	NextType (Pure Bool) = ftype "next !bool");
      test "num -> num" (fun () ->
	Arrow(Num, Num) = ftype "num -> num");
      test "num -> num -> num" (fun () ->
	Arrow(Num, Arrow(Num, Num)) = ftype "num -> num -> num");
      test "num & num -> num" (fun () ->
	Arrow(Product[Num; Num], Num) = ftype "num & num -> num");
      test "num -> num & num" (fun () ->
	Arrow(Num, Product[Num; Num]) = ftype "num -> num & num");
      test "num -> stream num & num -> num" (fun () ->
	Arrow(Num, Arrow(Product [Stream Num; Num], Num)) = ftype "num -> stream num & num -> num");
      test "alloc" (fun () -> Alloc = ftype "alloc")
    ]
  
let ltype_tests = 
  let open Unittest in 
  let open Ast in 
  group
    "Linear types"
    [ test "I" (fun () -> 
        Tensor [] = ltype "I");
      test "window" (fun () -> 
	Dom = ltype "window");
      test "(window)" (fun () -> 
	Dom = ltype "(window)");
      test "window * window" (fun () -> 
	Tensor [Dom; Dom] = ltype "window * window");
      test "(window * window)" (fun () -> 
	Tensor [Dom; Dom] = ltype "(window * window)");
      test "window -o window" (fun () -> 
	Lolli(Dom, Dom) = ltype "window -o window");
      test "window * window -o window" (fun () -> 
	Lolli(Tensor [Dom; Dom], Dom) = ltype "window * window -o window");
      test "window -o window * window" (fun () -> 
	Lolli(Dom, Tensor [Dom; Dom]) = ltype "window -o window * window");
    ]

let adjoint_tests =
  let open Unittest in 
  let open Ast in
  let open Base in 
  group
    "Adjoint types"
    [ test "G I" (fun () -> 
        G (Tensor []) = ftype "G I");
      test "G window" (fun () ->
	G Dom = ftype "G window");
      test "G (window)" (fun () ->
	G Dom = ftype "G (window)");
      test "G (window -o window)" (fun () -> 
	(G(Lolli(Dom, Dom))) = ftype "G (window -o window)");
      crashtest "G window * window [parse error]"
	(fun () -> ftype "G window * window")
	(function SyntaxError(_, "nonlinear type") -> true | _ -> false);
      test "(G F G window) -> G window" (fun () -> 
	Arrow(G(F(G Dom)), G Dom) = ftype "(G F G window) -> G window");
      test "F unit" (fun () ->
	F (Product []) = ltype "F unit");
      test "F num" (fun () ->
	F Num = ltype "F num");
      test "F(num)" (fun () ->
	F Num = ltype "F(num)");
      test "F(num -> num)" (fun () ->
	F (Arrow(Num, Num)) = ltype "F(num -> num)");
    ]

let parsing_types =
  let open Unittest in
  group "Types" 
    [ ftype_tests;
      ltype_tests;
      adjoint_tests
    ] 
      
let fexp_tests =
  let open Unittest in
  let open Ast in
  let open Base in 
  let eq s1 s2 = fexp_eq (fexp s1) (fexp s2) in
  let eqse s e = fexp_eq (fexp s) e in 
  let d = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let var x = (d, FVar x) in
  let u = var "u" in
  let v = var "v" in 
  let w = var "w" in 
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in 
  let num n = (d, FNum n) in
  let (+) e1 e2 = (d, FOp(Plus, e1, e2)) in
  let ( * ) e1 e2 = (d, FOp(Times, e1, e2)) in
  let tuple es = (d, FTuple es) in 
  let app e1 e2 = (d, FApp(e1, e2)) in
  let pvar x = (d, PVar x) in
  let px = pvar "x" in
  let py = pvar "y" in
  let pz = pvar "z" in 
  let ptuple ps = (d, PTuple ps) in
  let letvar p e1 e2 = (d, FLet(p, e1, e2)) in
  let fn p e = (d, FLam(p, e)) in
  let true' = (d, FTrue) in
  let false' = (d, FFalse) in
  let ifte(e1, e2, e3) = (d, FIf(e1, e2, e3)) in
  let cons e0 e e' = (d, FCons(e0, e, e')) in
  let pcons e e' = (d, PCons(e, e')) in
  let pure e = (d, FBang e) in
  let annot e tp = (d, FAnnot(e, tp)) in 
  let test s v = test s (fun () -> eqse s v) in 
  group "Nonlinear expressions"
    [ Unittest.test "x = (x)" (fun () ->
        eq "x" "(x)");
      Unittest.test "x != y" (fun () ->
	not (eq "x" "y"));
      test "x = FVar x" x;
      test "num 1" (num 1.);
      test "x y" (app x y);
      test "x y z" (app (app x y) z);
      test "x (y z)" (app x (app y z));
      test "x + y" (x + y);
      test "x + y + z" ((x + y) + z);
      test "x + (y + z)" (x + (y + z));
      test "x + y * z" (x + (y * z));
      test "y * z + x" ((y * z) + x);
      test "y  z + x" ((app y z) + x);
      test "x + y  z" (x + (app y z));
      test "()" (tuple []);
      test "(x, y)" (tuple [x; y]);
      test "(u, v, w)" (tuple [u; v; w]);
      test "fun () -> ()" (fn (ptuple []) (tuple []));
      test "fun x -> x" (fn px x);
      test "fun (x,y) -> (u,v)" (fn (ptuple [px;py]) (tuple [u;v]));
      test  "fun ((x, y)) -> (u,v)" (fn (ptuple [px;py]) (tuple [u;v]));
      test "fun x y z -> (x,y,z)" (fn px (fn py (fn pz (tuple [x;y;z]))));
      test "let x = 1 in x" (letvar px (num 1.) x);
      test "let (x,y) = (u,v) in x+y" (letvar (ptuple [px; py]) (tuple [u; v]) (x + y));
      test "let (x,y) = (u,v) in x y" (letvar (ptuple [px; py]) (tuple [u; v]) (app x y));
      test "true" true';
      test "false" false';
      test "if u then v else w" (ifte(u, v, w));
      test "if u then v else if x then y else z" (ifte(u, v, ifte(x,y,z)));
      test "1 + if u then v else if x then y else z" ((num 1.) + ifte(u, v, ifte(x,y,z)));
      test "if u then v else w + 1" (ifte(u, v, (w + num 1.)));
      test "x (if u then v else w + 1)" (app x (ifte(u, v, (w + num 1.))));
      test "cons(w, x, u)" (cons w x u);
      test "let x :: y = v in w" (letvar (pcons px "y") v w);
      test "!w" (pure w);
      test "x (!w)" (app x (pure w));
      test "x : num" (annot x Num);
      test "let x : num = y in z" (letvar px (annot y Num) z);
      test "let (x :: y) : stream num = v in w" (letvar (pcons px "y") (annot v (Stream Num)) w);
    ]
      
let lexp_tests = 
  let open Unittest in
  let open Ast in
  let open Base in 
  let eqse s e = lexp_eq (lexp s) e in 
  let d = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let var x = (d, LVar x) in
  let u = var "u" in
  let v = var "v" in 
  let w = var "w" in 
  let x = var "x" in
  let y = var "y" in
  let z = var "z" in 
  let tuple es = (d, LTuple es) in 
  let app e1 e2 = (d, LApp(e1, e2)) in
  let pvar x = (d, PVar x) in
  let px = pvar "x" in
  let py = pvar "y" in
  let pz = pvar "z" in 
  let ptuple ps = (d, PTuple ps) in
  let letvar p e1 e2 = (d, LLet(p, e1, e2)) in
  let fn p e = (d, LLam(p, e)) in
  let annot e tp = (d, LAnnot(e, tp)) in 
  let test s v = test s (fun () -> eqse s v) in 
  group "Nonlinear expressions"
    [ test "x"       x;
      test "x y"     (app x y);
      test "x y z"   (app (app x y) z);
      test "x (y z)" (app x (app y z));
      test "()" (tuple []);
      test "(x, y)" (tuple [x; y]);
      test "(u, v, w)" (tuple [u; v; w]);
      test "fun () -> ()" (fn (ptuple []) (tuple []));
      test "fun x -> x" (fn px x);
      test "fun (x,y) -> (u,v)" (fn (ptuple [px;py]) (tuple [u;v]));
      test "fun ((x, y)) -> (u,v)" (fn (ptuple [px;py]) (tuple [u;v]));
      test "fun x y z -> (x,y,z)" (fn px (fn py (fn pz (tuple [x;y;z]))));
      test "let (x,y) = (u,v) in x y" (letvar (ptuple [px; py]) (tuple [u; v]) (app x y));
      test "let x : F num = y in z" (letvar px (annot y (F Num)) z);
    ]

let parser_tests = 
  let open Unittest in
  group "Parsing" [parsing_types; group "Expressions" [fexp_tests; lexp_tests]]


let ftyping_tests =
  let open Unittest in
  let open Ast in
  let open Typing in
  let ctx1 = [ ("x", (Num, Dynamic, 0));
	       ("y", (Bool, Dynamic, 1));
	       ("z", (Arrow(String, Num), Dynamic, 0));
	       ("xs", (Stream Num, Dynamic, 1));
	       ("u", (Num, Stable, 0));
	       ("v", (Arrow(Stream Num, String), Stable, 0));
	       ("x", (String, Dynamic, 0)); ] in
  let check succ name ctx i stp se  =
    test name (fun () -> 
      try
	let _ = check_fexp ctx i (ftype stp) (fexp se) in succ
      with 
	TypeError(_, _) -> not succ)
  in 
  let noerr exp i tp = check true (Printf.sprintf "%s : %s [%d]" exp tp i) ctx1 i tp exp in
  let error exp i tp = check false (Printf.sprintf "%s : %s [%d]" exp tp i) ctx1 i tp exp in   
  let variables = 
    group "Variables"
      [ noerr "x" 0 "num";
	noerr "x" 1 "num";
	noerr "xs" 1 "stream num";
	error "xs" 2 "stream num";
	noerr "y" 1 "bool";
	error "y" 0 "bool";
	error "x" 0 "string";
	noerr "u" 0 "num";
	noerr "u" 1 "num";
	noerr "u" 2 "num";
      ] in
  let expressions =
    group "Expressions" 
      [ noerr "fun a -> a" 0 "bool -> bool";
        noerr "fun a -> a" 1 "bool -> bool";
        noerr "fun a -> a" 2 "bool -> bool";
        noerr "!(fun a -> a)" 2 "!(bool -> bool)";
        noerr "next y" 0 "next bool";
        noerr "5." 1 "num";
        noerr "y && true" 1 "bool";
	noerr "(5, true)" 0 "num & bool";
	noerr "let y = x in x + y" 0 "num";
	noerr "let (x,y) : num & num = (3,4) in x + y" 0 "num";
	noerr "let x : num = if true then 3 else 4 in x + x" 0 "num";
	noerr "let f : num -> bool = fun n -> n > 0 in f 15" 0 "bool";
	error "let f = fun n -> n > 0 in f 15" 0 "bool";
	noerr "let f : num & num -> num = fun (x,y) -> x + y in f (3,4)" 0 "num";
	noerr "!x" 0 "!num";
        noerr "let next z : next bool = next y in next (y && z)" 0 "next bool";
        noerr "let next z : next bool = next y in next (u > 5 || (y && z))" 0 "next bool";
      ] in
  let recursive =
    group "Recursive"
      [ noerr "fix xs u -> cons(u, 0, xs u)" 0 "alloc -> stream num";
	noerr "fix ints u n -> cons(u, n, ints u (n+1))" 0 "alloc -> num -> stream num";
	error "fun xs -> fix xss us -> cons(u, xs, xss u)" 0 "stream num -> alloc -> stream stream num";
	noerr "fun !n -> fix ns u -> cons(u, n, ns u)" 0 "!num -> alloc -> stream num";
	noerr "fix unzip u xys ->   let (x,y) :: xys = xys in   let next dxys = next (unzip u xys) in   let next xs = next (let (xs, ys) = dxys in xs) in   let next ys = next (let (xs, ys) = dxys in ys) in  (cons(u, x, xs), cons(u, y, ys))"    0 "alloc -> stream (num & num) -> stream num & stream num";
      ]
  in 
  group "Nonlinear" [variables; expressions; recursive]
       

let ltyping_tests = 
  let open Unittest in
  let open Ast in
  let open Typing in
  let ctx = [ ("x", (Num, Dynamic, 0));
	      ("y", (Bool, Dynamic, 1));
	      ("z", (Arrow(String, Num), Dynamic, 0));
	      ("xs", (Stream Num, Dynamic, 1));
	      ("stack", (G(Lolli(Tensor [Dom;Dom], Dom)), Stable, 0));
	      ("v", (Arrow(Stream Num, String), Stable, 0));
	      ("x", (String, Dynamic, 0)); ] in
  let a_hyp = ("a", (F Num, false, 0)) in
  let v0_hyp = ("v0", (Dom, false, 0)) in
  let w0_hyp = ("w0", (Dom, false, 0)) in
  let w1_hyp = ("w1", (Dom, false, 1)) in
  let w_nohyp = ("w_no", (Dom, true, 0)) in
  let b = ("b", (ltype "F num -o window", false, 0))  in 
  let check succ name lctx i stp se  =
    let no_exn = if succ then Success else Failure "No exception!" in
    let exn s = if succ then Failure s else Success in 
    fulltest name (fun () -> 
      try
	let _ = check_lexp ctx lctx i (ltype stp) (lexp se) in no_exn 
      with 
	TypeError(_, msg) -> exn msg)
  in 
  let noerr exp lctx i tp = check true (Printf.sprintf "%s : %s [%d]" exp tp i) lctx i tp exp in
  let error exp lctx i tp = check false (Printf.sprintf "%s : %s [%d]" exp tp i) lctx i tp exp in   
  let vars =
    group "Variables"
      [ noerr "a" [a_hyp] 0 "F num";
	noerr "a" [a_hyp; w0_hyp] 0 "F num";
	error "w_nohyp" [a_hyp; w0_hyp; w_nohyp] 0 "window";
	noerr "w1" [a_hyp; w1_hyp; w_nohyp] 1 "window";
	error "w1" [a_hyp; w1_hyp; w_nohyp] 0 "window";
      ] in
  let exps =
    group "Expressions"
      [ error "(a, a)" [a_hyp] 0 "F num * F num";
	noerr "(v0, w0)" [w0_hyp; v0_hyp] 0 "window * window";
	error "(v0, v0)" [v0_hyp] 0 "window * window";
	noerr "(run stack) (v0, w0)" [w0_hyp; v0_hyp] 0 "window";
	noerr "fun w -> w" [] 0 "window -o window";
	noerr "F 4" [] 0 "F num";
	noerr "b (F 5)" [b] 0 "window";
	noerr "let F n = a in b (F n)" [b; a_hyp] 0 "window";
	noerr "let F f : F (G (window -o window)) = F (G (fun w -> w)) in (run f) ((run f) v0)" [v0_hyp] 0 "window";
	noerr "F (G (fun w -> w))" [] 0 "F (G (window -o window))";
	noerr "let a = v0 in a" [v0_hyp] 0 "window";
	error "fun a -> (a,a)" [] 0 "window -o window * window";
	noerr "let (a,b) : window * window = (v0, w0) in (b,a)" [v0_hyp; w0_hyp] 0 "window * window";
	noerr "let a = v0 in (let b = w0 in (b,a))" [v0_hyp; w0_hyp] 0 "window * window";
	noerr "let b = w0 in (v0,b)" [v0_hyp; w0_hyp] 0 "window * window";
	noerr "let (a,b) : window * window = (v0, w0) in (a,b)" [v0_hyp; w0_hyp] 0 "window * window";
      ]
  in
  group "Linear Expressions" [vars; exps]
  
