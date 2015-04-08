#load "jscomp.cma";;
#install_printer Base.print_pos;;

module Test = struct
  open Ast
  open Context
  open Subtype
  open Poly

    
  let exp = Parseloc.string Parser.test_exp 
  let tp  = Parseloc.string Parser.test_tp
  let pat =  Parseloc.string Parser.test_pat
  let prog = Parseloc.string Parser.test_program
  let signature = Parseloc.string Parser.test_signature
  let signature_decl = Parseloc.string Parser.test_signature_decl
  let program = Parseloc.string Parser.test_program

  let pos = (Lexing.dummy_pos, Lexing.dummy_pos)

  let check0 e t ctx =
    let cmd = Kinding.check_kind (tp t) Int >>= (fun t -> 
              (check (exp e) t 0)) in
    run cmd ctx Base.dummy_pos
  let synth0 e ctx = run (synth (exp e) 0) ctx Base.dummy_pos

  let check (e, t) = check0 e t []
  let synth e = synth0 e []

  let infer_kind t = run (Kinding.synth_kind (tp t)) [] pos 
  let subtype t t' = run (Subtype.(<==) (tp t) (tp t')) [] pos

  let ctx = ["x$1", Hyp(Dyn, TVar "a$0", 0); ("a$0", Type (Exist, Int, Some Ast.Num))]
  let ctx_u = ["u$2", Hyp(Dyn, tp "num & num", 0)]

  let tests0 = [| "let x = 3 in x", "num";
                  "fun x -> x", "num -> num";
                  "fun x -> x", "forall a. a -> a";
                  "fun x -> x", "exists a. a -> a";
                  "3", "exists a. a";
                  ("val fact : num -> num 
                    let loop fact n = 
                       if n = 0 then 1 else n * fact (n - 1) in 
                    fact 5",
                   "num");
                  ("val fact_iter : num & num -> num
                    let loop fact_iter (n, acc) = 
                      if n = 0 then acc else fact_iter(1, 1)
                    in 
                    fact_iter(5, 1)",
                   "num");
                  ("val fact_iter : num & num -> num
                    let loop fact_iter (n, acc) = 
                      if n = 0 then acc else fact_iter(1, 1)
                    in 
                    fact_iter(5, 1)",
                   "num");
                  ("val ones : alloc -> stream num 
                    let rec ones x = cons(x, 1, ones x) in ones",
                   "alloc -> stream num");
                  ("fun x -> (x, x)",
                   "forall a. a -> (a & a)");
                  ("fun loop f x -> f x",
                   "forall a b. a -> b");
               |] 
  let r0() = Array.map check tests0

  let print_result r i =
    match r.(i) with
    | Value (t, _) -> let (stmts, exp) = Translate.translate t in
                      Pp.print (Js.print_stmts stmts) stdout;
                      Printf.fprintf stdout "---\n";
                      Pp.print (Js.print_exp exp) stdout;
                      Printf.fprintf stdout "\n"
    | Error msg -> Printf.fprintf stdout "%s" msg 



  let ctx_d = ["list", Data(["a"], ["Nil", tp "unit";
                                    "Cons", tp "a & list a"])]

  let checkd (e, t) = check0 e t ctx_d 
  let ds = [|"Nil()", "forall a. list a";
             "val is_empty : forall a. list a -> bool  
                   let is_empty xs = 
                     match xs begin
                       Nil _-> true
                     | Cons _ -> false
                     end
                   in 
                   is_empty (Nil())",
                  "bool";

             "val is_one : forall a. list a -> bool 
              let is_one xs = 
                match xs begin
                 Nil _ -> false
                | Cons(_, Nil _) -> false
                | Cons(_, Cons _) -> true
                end
              in is_one(Cons(1, Nil()))",
             "bool";

             "fun loop length xs -> 
                match xs begin
                 Nil() -> 0 
                | Cons(x, xs) -> 1 + length xs 
                end",
            "forall a. list a -> num";

            ("fix map (!f) u (x :: xs) -> cons(u, f x, map (!f) u xs)",
             "forall a b. !(a -> b) -> alloc -> stream a -> stream b");

            ("fix zip u (x :: xs) (y :: ys) -> cons(u, (x,y), zip u xs ys)",
             "forall a b. alloc -> stream a -> stream b -> stream (a & b)");

            ("fun (next(x,y)) -> (next x, next y)",
             "forall a b. next(a & b) -> next a & next b");

            ("fun (next x, next y) -> next(x, y)",
             "forall a b. next a & next b -> next(a & b)");

            ("fix delay_stream u (d :: ds) ->
                let next x = d in 
                next(let next xs = delay_stream u ds in cons(u, x, xs))",
             "forall a. alloc -> stream (next a) -> next (stream a)");

            ("G(let () = ( () : (exists a. I)) in ())",
             "G(exists a. I)")


           |]
  let r1() = Array.map checkd ds

  let lctx =
    [("mkButton", Hyp(Stable, tp "G(exists a. dom a)", 0));
     ("mkLabel", Hyp(Stable, tp "string -> G(exists a. dom a)", 0));
     ("vstack", Hyp(Stable, tp "G(forall a b. dom a -o dom b -o dom a)", 0));
     ("split", Hyp(Stable, tp "G(forall a. dom a -o frame a * next(dom a))", 0));
     ("merge", Hyp(Stable, tp "G(forall a. frame a * next(dom a) -o dom a)", 0));
    ]

  let lcheck0 e t ctx = run (lcheck (exp e) (tp t) 0) ctx Base.dummy_pos
  let checkl (e, t) = lcheck0 e t lctx
  let lsynth0 e ctx = run (lsynth (exp e) 0) ctx Base.dummy_pos
  let synthl e = lsynth0 e lctx

  let ls = [| ("()", "I"); 
              ("((), ())", "I * I");
              ("fun x -> x", "I -o I");
              ("fun (x, y) -> (y, x)",
               "forall a b. a * b -o b * a");
              ("run mkButton",
               "exists a. dom a");
              ("run (mkLabel \"hi\")",
               "exists a. dom a");
              ("run vstack",
               "forall a b. dom a -o dom b -o dom a");
              ("let b = run mkButton in b",
               "exists a. dom a");
              ("let b1 = run mkButton in 
                let b2 = run mkButton in 
                (b1, b2)",
               "(exists a1. dom a1) * (exists a2. dom a2)");
              ("let b1 = run mkButton in 
                let b2 = run mkButton in 
                (b1, b2)",
               "(exists a1 a2. dom a1 * dom a2)");
              ("let b = run mkButton in
                let l = run (mkLabel \"hi\") in 
                (run vstack) b l",
               "exists a. dom a");
              ("fun error -> (error, error)",
               "F(num) -o F(num) * F(num)");
              ("fix foo w -> 
                  let (f, next w1) = (run split) w in 
                  (run merge) (f, next(foo w1))",
               "forall a. dom a -o dom a");
           |]
  let lr1() = Array.map checkl ls

  let sig0 =  "val toString : num -> string

               val mkText : stream string -> G(exists a. dom a)
               val mkButton : G(exists a. dom a)
               val vbox : G(exists a. dom a)
               val hbox : G(exists a. dom a)

               val attach : G(forall a b. dom a * dom b -o dom a)
               val cat : string & string -> string

               val div : G(exists a. dom a)

               val color : string -> G(forall a. dom a -o dom a)
               val font  : string & num -> G(forall a. dom a -o dom a)
               val width : string -> G(forall a. dom a -o dom a)
               val setText : string -> G(forall a. dom a -o dom a)

               val clicks : alloc -> G(forall a. dom a -o dom a * F (stream bool))
               val mouseover : alloc -> G(forall a. dom a -o dom a * F (stream bool))
               val split : G(forall a. dom a -o frame a * next(dom a))
               val merge :  G(forall a. frame a * next(dom a) -o dom a)
               type list a = 
                    | Nil of unit
                    | Cons of a & list a
               type option a = None of unit | Some of a
               type event = Foo | Bar 
               val event_to_bool : event -> bool "

  let runsig string =
    let s = signature string in
    run (Toplevel.process_signature s) [] Base.dummy_pos

  let programs = [|
    "val map : forall a b. (a -> b) -> list a -> list b
     let map f = 
       fun loop recur xs -> 
         match xs begin
         | Nil() -> Nil()
         | Cons(y, ys) -> Cons(f y, recur ys)
         end

     val main : alloc -> G(exists a. dom a)
     let main u = mkButton
     
     in main";

    "val ints : alloc -> num -> stream num
     let rec ints u n = cons(u, n, ints u (n+1))

     val map : forall a b. !(a -> b) -> alloc -> stream a -> stream b
     let rec map (!f) u ns =
       let x :: xs = ns in
       cons(u, f x, map (!f) u xs)

     val main : alloc -> G(exists a. dom a)
     let main u = 
       let labels : stream string = map (!toString) u (ints u 0) in
       G(let w1 = run (mkText labels) in w1)

     in main";


    "val toBool : event -> bool
     let toBool e = 
       match e begin
         Foo -> true
       | Bar -> false
       end

     val main : alloc -> G(exists a. dom a)
     let main u = mkButton

     in main";

     "type window : int
    let window = G(exists a. dom a)
    
     val mkText : string -> G(exists a. dom a)

    val map : forall a b. !(a -> b) -> alloc -> stream a -> stream b 
    let rec map (!f) u (x :: xs) =
      cons(u, f x, map (!f) u xs)
    
    val zip : forall a b. alloc -> stream a & stream b -> stream (a & b)
    let rec zip u ((x :: xs), (y :: ys)) =
      cons(u, (x,y), zip u (xs, ys))
    
    val always : forall a. alloc -> !a -> stream a
    let rec always u (!x) = cons(u, x, always u (!x))
    
    val join : alloc -> stream bool -> stream bool -> stream bool
    let join u bs1 bs2 = map (!(fun (b1, b2) -> b1 || b2)) u (zip u (bs1, bs2))
    
    val dynbutton : alloc -> window
    let dynbutton acap =
      G(val grow : forall a. dom a -o F(stream bool) -o dom a 
        let rec grow w0 (F (b :: bs1)) =
          if b then
            let wbutton = run mkButton in
            let wlabel = run (mkText \"Click me\") in
            let (wlabel, F (_ :: bs2)) = run (clicks acap) wlabel in
            let wbutton = run attach (wbutton, wlabel) in
            let wjoin = run attach (w0, wbutton) in 
            let (wnow, next wrest) = run split wjoin in
            run merge (wnow, next (grow wrest (F (join acap bs1 bs2))))
          else
            let (wnow, next wrest) = run split w0 in
            run merge (wnow, next (grow wrest (F bs1)))
          in
        let w = run vbox in
        grow w (F(always acap (!false))))
    
    in
    
    dynbutton" ;

    "// val blah : G(forall a. dom a -o exists b. dom b)
     // let blah = G(fun w -> w)

     val mkText : string -> G(exists a. dom a)

     val main : alloc -> G(exists a. dom a)
     let main u = 
       G(val blah : forall a. dom a -o exists b. dom b
         let blah w = w in 
         let wroot = run (mkText \"\") in 
         blah wroot)

     in main";

|]

  let run_program' s p =
    run (Toplevel.process_signature (signature s) >> 
         Toplevel.elaborate (program p)) [] Base.dummy_pos


  let run_program string =
    run_program' sig0 string 
end 

