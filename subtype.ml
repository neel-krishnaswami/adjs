open Base
open Ast 
open Context
open Kinding 

let fmt_tp () tp = string_of_tp tp 

let rec with_hyps hyps cmd =
  match hyps with
  | [] -> cmd
  | h :: hs -> with_hyp h (with_hyps hs cmd)

let swizzle h1 h2 cmd =
  orelse (with_hyps [h1; h2] cmd)
         (with_hyps [h2; h1] cmd)

let rec subtype s t k =
  subst_kind k >>= subtype' s t
    
and subtype' s t = function
  | KArrow(k1, k2) ->
      newid "a" >>= (fun a -> 
      with_hyp (a, Type(Univ, k1, None))
      (subtype (TApp(s, [TVar a])) (TApp(t, [TVar a])) k2))
  | (Int as k) | (Lin as k) -> base_subtype s t k 
  | KVar _ -> assert false

and base_subtype s t k =
  whnf s >>= (fun s -> 
  whnf t >>= (fun t -> 
  base_subtype' s t k))

and base_subtype' s t k = 
  match k, s, t with
  | KArrow(_, _), _, _ -> assert false
  | KVar _, _, _ -> assert false
  | Int, Num, Num
  | Int, Bool, Bool
  | Int, String, String   -> return ()
  | Int, Pure s1, Pure t1 -> base_subtype s1 t1 Int
  | Lin, F s1, F t1       -> base_subtype s1 t1 Int
  | Int, G s1, G t1       -> base_subtype s1 t1 Lin 
  | k, Next s1, Next t1   -> base_subtype s1 t1 k 
  | Int, Arrow(s1, s2), Arrow(t1, t2) -> base_subtype t1 s1 Int >>
                                         base_subtype s2 t2 Int
  | Lin, Lolli(s1, s2), Lolli(t1, t2) -> base_subtype t1 s1 Lin >>
                                         base_subtype s2 t2 Lin 
  | Lin, Frame s, Svg t 
  | Lin, Svg s, Svg t  
  | Lin, Dom s, Dom t     -> base_subtype s t Int 
  | Int, Product ss, Product ts ->
      seq (map2 (fun s1 t1 -> base_subtype s1 t1 Int) ss ts) >>= (fun (_ : unit list) -> return ())
  | Lin, Tensor ss, Tensor ts ->
      seq (map2 (fun s1 t1 -> base_subtype s1 t1 Lin) ss ts) >>= (fun (_ : unit list) ->  return ())
  | k, s, Forall(b, Some k2, t) ->
      fresh rename_tp b t >>= (fun (b, t) -> 
      with_hyp (b, Type(Univ, k2, None)) (base_subtype s t k))
  | k, Exists(a, Some k1, s), t ->
      fresh rename_tp a s >>= (fun (a, s) -> 
      with_hyp (a, Type(Univ, k1, None)) (base_subtype s t k))
  | k, Forall(a, Some k1, s), Exists(b, Some k2, t) ->
      subkind k1 k2 >>
      fresh rename_tp a s >>= (fun (a, s) -> 
      fresh rename_tp b t >>= (fun (b, t) -> 
      let h1 = (a, Type(Exist, k1, None)) in
      let h2 = (b, Type(Exist, k1, None)) in
      swizzle h1 h2 (base_subtype s t k)))
  | k, Forall(a, Some k1, s), t ->
      fresh rename_tp a s >>= (fun (a, s) -> 
      with_hyp (a, Type(Exist, k1, None)) (base_subtype s t k))
  | k, s, Exists(b, Some k2, t) ->
      fresh rename_tp b t >>= (fun (b, t) -> 
      with_hyp (b, Type(Exist, k2, None)) (base_subtype s t k))




let expand_kind tp k kexpect =
  orelse
    (subkind k kexpect >> subst_kind k)
    (error "Expected type of kind %a, got type %a" fmt_kind kexpect fmt_tp tp)

let expand_const kexpect f a =
  let (tp, k) = f() in
  expand_kind tp k kexpect >>= (fun k' -> 
  update_eqn a [a, Type(Exist, k', Some tp)])

let expand_one kexpect f a =
  newid "b" >>= (fun b ->
  let (tp, k, k') = f b in 
  expand_kind tp k kexpect >>= (fun k0 -> 
  update_eqn a [b, Type(Exist, k', None); a, Type(Exist, k0, Some tp)]))

let expand_two kexpect f a =
  newid "b" >>= (fun b -> 
  newid "c" >>= (fun c ->
  let (tp, k, (kb, kc)) = f b c in 
  expand_kind tp k kexpect >>= (fun k' -> 
  update_eqn a [b, Type(Exist, kb, None);
      	        c, Type(Exist, kc, None); 
                a, Type(Exist, k', Some tp)])))

let expand_list kexpect f xs a =
  seq (map (fun _ -> newid "x") xs) >>= (fun bs -> 
  let (tp, k, ks) = f bs in 
  let decls = map2 (fun b k -> (b, Type(Exist, k, None))) bs ks in
  expand_kind tp k kexpect >>= (fun k' -> 
  let tp' = Type(Exist, k', Some tp) in 
  update_eqn a (decls @ [a, tp'])))


let expand_num      k = expand_const k (fun a -> (Num, Int))
let expand_string   k = expand_const k (fun a -> (String, Int))
let expand_bool     k = expand_const k (fun a -> (Bool, Int))
let expand_pure     k = expand_one k (fun a -> (Pure(TVar a), Int, Int))
let expand_next     k = expand_one k (fun a -> (Next(TVar a), Int, Int))
let expand_nextlin  k = expand_one k (fun a -> (Next(TVar a), Lin, Lin))
let expand_f        k = expand_one k (fun a -> (F(TVar a), Lin, Int))
let expand_g        k = expand_one k (fun a -> (G(TVar a), Int, Lin))
let expand_dom      k = expand_one k (fun a -> (Dom(TVar a), Lin, Int))
let expand_frame    k = expand_one k (fun a -> (Frame(TVar a), Lin, Int))
let expand_svg      k = expand_one k (fun a -> (Svg(TVar a), Lin, Int))
let expand_stream   k = expand_one k (fun a -> (Stream(TVar a), Int, Int))
let expand_arrow    k = expand_two k (fun a b -> (Arrow(TVar a, TVar b), Int, (Int, Int)))
let expand_lolli    k = expand_two k (fun a b -> (Lolli(TVar a, TVar b), Lin, (Lin, Lin)))
let expand_product  ts k a = expand_list k (fun bs -> (Product (map (fun a -> TVar a) bs), Int, map (fun _ -> Int) bs)) ts a 
let expand_tensor   ts k a = expand_list k (fun bs -> (Tensor (map (fun a -> TVar a) bs), Lin, map (fun _ -> Lin) bs)) ts a 
let expand_app d xs k a = expand_list k (fun bs -> (TApp(TVar d, map (fun a -> TVar a) bs), Int, map (fun _ -> Int) bs)) xs a 
  
let rec expand a tp =
  synth_kind tp >>= (fun (_, k) ->
  match tp with 
  | Num               -> expand_num k a 
  | String            -> expand_string k a 
  | Bool              -> expand_bool k a 
  | Pure _            -> expand_pure k a 
  | Next _            -> expand_next k a
  | F t               -> expand_f k a 
  | G t               -> expand_g k a 
  | Dom t             -> expand_dom k a
  | Frame t           -> expand_frame k a 
  | Svg t             -> expand_svg k a
  | Stream t          -> expand_stream k a 
  | Arrow(_, _)       -> expand_arrow k a 
  | Lolli(_, _)       -> expand_lolli k a 
  | Product ts        -> expand_product ts k a 
  | Tensor ts         -> expand_tensor ts k a
  | TApp(TVar d, ts)  -> expand_app d ts k a
  | TApp(_, ts)       -> assert false 
  | TVar b            -> before a (synth_kind (TVar b)) >>= (fun (tp, k') ->
                         expand_kind tp k' k >>= (fun k'' -> 
        	         update_eqn a [a, Type(Exist, k'', Some (TVar b))]))
  | TAnnot(tp, k)     -> expand a tp 
  | Forall(_, _, _)   -> assert false
  | Exists(_, _, _)   -> assert false
  | TLet(_, _, _)     -> assert false
  | TLam(_, _)        -> assert false)

let mismatch msg tp = 
  subst tp >>= (fun tp -> error "expected %s type, got %a" msg fmt_tp tp)
    
let expand_evar a error_type expander  =
  lookup a >>= (function 
    | Type(Exist, k, None) -> expander k a 
    | Type(_, k, Some _)   -> assert false
    | Type(Univ, k, _)     -> mismatch error_type (TVar a)
    | _                    -> error "'%a' is not a type variable" fmt_id a)

let rec (<==) s t =
  subst s >>= (fun s' -> 
  subst t >>= (fun t' ->
  sub s' t'))

and sub s t =
  match s, t with
  | Num, Num                     
  | Bool, Bool                   
  | String, String               -> return ()
  | Stream s', Stream t'
  | Frame s', Frame t'
  | Dom s', Dom t'
  | Svg s', Svg t'         
  | Pure s', Pure t'             
  | Next s', Next t' 
  | G s', G t'
  | F s', F t'                   -> (s' <== t') 
  | Arrow(s1, s2), Arrow(t1, t2)
  | Lolli(s1, s2), Lolli(t1, t2) -> (t1 <== s1) >> (s2 <== s2) 
  | Product ss, Product ts when length ss = length ts -> 
    seq (map2 (fun s t -> (s <== t)) ss ts) >>= (fun _ -> return ())
  | Tensor ss, Tensor ts when length ss = length ts -> 
    seq (map2 (fun s t -> (s <== t )) ss ts) >>= (fun _ -> return ())
  | TApp(TVar d, ss), TApp(TVar d', ts) when d = d' && length ss = length ts -> 
    seq (map2 (fun s t -> (s <== t)) ss ts) >>= (fun _ -> return ())
  | Forall(a, Some k, s), Exists(b, Some k', t) ->
    expand_kind s k k' >>= (fun k'' -> 
    fresh rename_tp a s >>= (fun (a,s) -> 
    fresh rename_tp b t >>= (fun (b,t) -> 
    let cmd1 = with_hyp (a, Type(Exist, k'', None)) 
              (with_hyp (b, Type(Exist, k'', None))
              ((s <== t))) in 
    let cmd2 = with_hyp (b, Type(Exist, k'', None)) 
              (with_hyp (a, Type(Exist, k'', None))
              ((s <== t))) in
    orelse cmd1 cmd2)))
  | Forall(a, _, s), Exists(b, _, t) -> assert false 
  | Exists(a, Some k, s), Exists(b, Some k', t) -> 
    expand_kind s k k' >>= (fun k'' -> 
    fresh rename_tp a s >>= (fun (a,s) -> 
    fresh rename_tp b t >>= (fun (b,t) -> 
    let cmd1 = with_hyp (a, Type(Univ,  k'', None)) 
              (with_hyp (b, Type(Exist, k'', None))
              ((s <== t))) in 
    let cmd2 = with_hyp (b, Type(Exist, k'', None)) 
              (with_hyp (a, Type(Univ,  k'', None))
              ((s <== t))) in
    orelse cmd1 cmd2)))
  | Exists(a, _, s), Exists(b, _, t) -> assert false
  | Forall(a, Some k, s), Forall(b, Some k', t) ->
    expand_kind s k k' >>= (fun k'' -> 
    fresh rename_tp a s >>= (fun (a,s) -> 
    fresh rename_tp b t >>= (fun (b,t) -> 
    let cmd1 = with_hyp (a, Type(Exist, k'', None)) 
              (with_hyp (b, Type(Univ,  k'', None))
              ((s <== t))) in 
    let cmd2 = with_hyp (b, Type(Univ,  k'', None)) 
              (with_hyp (a, Type(Exist, k'', None))
              ((s <== t))) in
    orelse cmd1 cmd2)))
  | Forall(a, _, s), Forall(b, _, t) -> assert false
  | Exists(a, Some k, s), Forall(b, Some k', t) ->
    expand_kind s k k' >>= (fun k'' -> 
    fresh rename_tp a s >>= (fun (a,s) -> 
    fresh rename_tp b t >>= (fun (b,t) -> 
    let cmd1 = with_hyp (a, Type(Univ, k'', None)) 
              (with_hyp (b, Type(Univ, k'', None))
              ((s <== t))) in 
    let cmd2 = with_hyp (b, Type(Univ, k'', None)) 
              (with_hyp (a, Type(Univ, k'', None))
              ((s <== t))) in
    orelse cmd1 cmd2)))
  | Exists(a, _, s), Forall(b, _, t) -> assert false 
  | s, Forall(a, Some k, t) ->
    fresh rename_tp a t >>= (fun (a, t) -> 
    with_hyp (a, Type(Univ, k, None)) ((s <== t)))
  | s, Forall(a, None, t) -> assert false 
  | Exists(a, Some k, s), t -> 
    fresh rename_tp a s >>= (fun (a, s) -> 
    with_hyp (a, Type(Univ, k, None)) ((s <== t)))
  | Exists(a, None, s), t -> assert false
  | Forall(a, Some k, s), t ->
    fresh rename_tp a s >>= (fun (a, s) -> 
    push (a, Type(Exist, k, None)) >>    (* Change to with_hyp? *)
    (s <== t))
  | Forall(a, None, s), t -> assert false
  | s, Exists(a, Some k, t) -> 
    fresh rename_tp a t >>= (fun (a, t) -> 
    push (a, Type(Exist, k, None)) >>    (* Change to with_hyp? *)
    (s <== t))
  | s, Exists(a, None, t) -> assert false
  | TVar a, u 
  | u, TVar a ->
    lookup a >>= (function
      | Type(_, _, Some _) -> assert false 
      | Type(Univ, k, None) ->
        (match u with
        | TVar b when a = b -> return () 
        | TVar b ->
          lookup b >>= (function
            | Type(Univ, _, _) ->
              error "'%a' is not an instance of '%a'" fmt_id a fmt_id b
            | Type(Exist, _, Some _) -> assert false 
            | Type(Exist, k', None) ->
              expand_kind u k k' >>= (fun k'' -> 
              before b (check_kind (TVar a) k'') >>= (fun tpa -> 
              update_eqn b [b, Type(Exist, k'', Some tpa)]))
            | _ -> error "variable '%a' is not a type variable" fmt_id b)
        | _ -> error "'%a' is not an instance of '%a'" fmt_id a fmt_tp u)
      | Type(Exist, k, None) ->
        (match u with
        | TVar b when a = b -> return () 
        | TVar b ->
          lookup b >>= (function
            | Type(_, _, Some _) -> assert false 
            | Type(Exist, k', None) ->
              expand_kind u k k' >>= (fun k'' -> 
              let cmd1 = before b (check_kind (TVar a) k'') >>= (fun tpa -> 
                         update_eqn b [b, Type(Exist, k'', Some tpa)]) in
              let cmd2 = before a (check_kind (TVar b) k'') >>= (fun tpb -> 
                         update_eqn a [a, Type(Exist, k'', Some tpb)]) in 
              orelse cmd1 cmd2)
            | Type(Univ, k', None) ->
              expand_kind u k k' >>= (fun k'' -> 
              before a (synth_kind (TVar b)) >>= (fun _ -> 
              update_eqn a [a, Type(Exist, k'', Some(TVar b))]))
            | _ -> error "variable '%a' is not a type variable" fmt_id b)             
        | _ ->
          before a (synth_kind u) >>= (fun _ -> 
          expand a u >>
          (s <== t)))
      | _ -> error "variable '%a' is not a type variable" fmt_id a)
  | _, _ -> error "'%a' is not an instance of '%a'" fmt_tp s fmt_tp t 















