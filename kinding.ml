open Base
open Ast
open Context

let rec wellsorted = function
  | Int -> return ()
  | Lin -> return ()
  | KArrow(k1, k2) -> wellsorted k1 >> wellsorted k2
  | KVar x -> lookup x >>= (function
      | Kind(_, _) -> return ()
      | _ -> error "Variable '%s' is not a kind" x)

let rec subkind k1 k2 =
  subst_kind k1 >>= (fun k1 -> 
  subst_kind k2 >>= (fun k2 ->
  subkind' k1 k2))

and subkind' k1 k2 =
  match k1, k2 with
  | Int, Int          -> return ()
  | Lin, Lin          -> return ()
  | KArrow(k1', k1''),
    KArrow(k2', k2'') -> subkind k2' k1' >> subkind k1'' k2''
  | KVar x, KVar y    -> if x = y
                         then return ()
                         else  orelse (wellsorted_before x (KVar y)) 
                                      (wellsorted_before y (KVar x))
  | KVar x, k
  | k, KVar x         -> wellsorted_before x k
  | _, _ -> error "kind mismatch -- %a and %a incompatible" fmt_kind k1 fmt_kind k2 

and wellsorted_before a k = 
  before a (wellsorted k) >>
  update_eqn a [a, Kind(Exist, Some k)]


let rec expand_karrow kvar =
  lookup kvar >>= (function
  | Kind(Exist, None) ->
      newid "k1" >>= (fun k1 -> 
      newid "k2" >>= (fun k2 ->
      update_eqn kvar [k1, Kind(Exist, None);
                       k2, Kind(Exist, None);
                       kvar, Kind(Exist, Some (KArrow(KVar k1, KVar k2)))]))
  | Kind(Exist, Some _) -> assert false
  | _ -> assert false)

let rec checkable_tycon = function
  | TLam(_, _) -> true
  | TLet(_, _, tp) -> checkable_tycon tp
  | _ -> false 

let rec tapp hd args =
  match hd, args with
  | TApp(hd', args'), _ -> tapp hd' (args' @ args)
  | _, _                -> TApp(hd, args)

let rec synth_kind tp =
  match tp with
  | String
  | Num
  | Bool            -> return (tp, Int)
  | Pure tp         -> check_kind tp Int >>= (fun tp -> return (Pure tp, Int))
  | Stream tp       -> check_kind  tp Int >>= (fun tp -> return (Stream tp, Int))
  | Next tp         -> synth_kind tp >>= (fun (tp, k) -> return (Next tp, k))
  | G tp            -> check_kind tp Lin >>= (fun tp -> return (G tp, Int))
  | Arrow(tp1, tp2) -> check_kind tp1 Int >>= (fun tp1 ->
                       check_kind tp2 Int >>= (fun tp2 ->
                       return (Arrow(tp1, tp2), Int)))
  | Product tps     -> seq (map (fun tp -> check_kind tp Int) tps) >>= (fun tps ->
                       return (Product tps, Int))
  | Forall(a, Some k0, tp) ->
      wellsorted k0 >>
      fresh rename_tp a tp >>= (fun (a, tp) -> 
      with_hyp (a, Type(Univ, k0, None))
        (synth_kind tp >>= (fun (tp, k) ->
         return (Forall(a, Some k0, tp), k))))
  | Forall(a, None, tp) ->
      fresh rename_tp a tp >>= (fun (a, tp) -> 
      newid "k" >>= (fun kvar -> 
      (with_hyp  (kvar, Kind(Exist, None)) 
      (with_hyp (a, Type(Univ, KVar kvar,  None))
        (synth_kind tp >>= (fun (tp, k) ->
         subst_kind (KVar kvar) >>= (fun karg -> 
         (orelse (before kvar (wellsorted karg)) 
                 (error "Could not infer kind for '%s'" a)) >>
         return (Forall(a, Some karg, tp), k))))))))
  | Exists(a, Some k0, tp)   ->
      wellsorted k0 >>
      fresh rename_tp a tp >>= (fun (a, tp) -> 
      with_hyp (a, Type(Univ, k0, None)) 
        (synth_kind tp >>= (fun (tp, k) ->
         return (Exists(a, Some k0, tp), k))))
  | Exists(a, None, tp) ->
      fresh rename_tp a tp >>= (fun (a, tp) -> 
      newid "k" >>= (fun kvar -> 
      (with_hyp (kvar, Kind(Exist, None)) 
      (with_hyp (a, Type(Univ, KVar kvar,  None)) 
        (synth_kind tp >>= (fun (tp, k) ->
         subst_kind (KVar kvar) >>= (fun karg -> 
         (orelse (before kvar (wellsorted karg)) 
                 (error "Could not infer kind for '%s'" a)) >>
         return (Exists(a, Some karg, tp), k))))))))
  | F tp            -> check_kind tp Int >>= (fun tp -> return (F tp, Lin))
  | Dom tp          -> check_kind tp Int >>= (fun tp -> return (Dom tp, Lin))
  | Frame tp        -> check_kind tp Int >>= (fun tp -> return (Frame tp, Lin))
  | Svg tp          -> check_kind tp Int >>= (fun tp -> return (Svg tp, Lin))
  | Tensor tps      -> seq (map (fun tp -> check_kind tp Lin) tps) >>= (fun tps ->
                       return (Tensor tps, Lin))
  | Lolli(tp1, tp2) -> check_kind tp1 Lin >>= (fun tp1 ->
                       check_kind tp2 Lin >>= (fun tp2 ->
                       return (Lolli(tp1, tp2), Lin)))
  | TVar a          -> lookup a >>= (function
                       | Type(_, k, _) -> subst_kind k >>= (fun k -> return (TVar a, k))
                       | Data(k, _, _) -> subst_kind k >>= (fun k -> return (tapp (TVar a) [], k))
                       | _             -> error "variable '%a' not a type variable" fmt_id a)
  | TApp(tp0, tps)  -> synth_kind tp0 >>= (fun (tp0, k0) -> 
                       synth_spine k0 tps >>= (fun (tps, k) -> 
                       return (tapp tp0 tps, k)))
  | TAnnot(tp1, k1)  -> wellsorted k1 >>
                        check_kind tp1 k1 >>= (fun tp1 -> 
                        subst_kind k1 >>= (fun k1 -> 
                        return (tp1, k1)))
  | tp               -> error "Cannot synthesize kind for type expression"

and synth_spine kin tps =
  match (kin, tps) with
  | (k, []) -> return ([], k)
  | (KArrow(k, kin'), tp0 :: tps') ->
      check_kind tp0 k >>= (fun tp0 -> 
      synth_spine kin' tps' >>= (fun (tps', kresult) -> 
      return (tp0 :: tps', kresult)))
  | (k, tp :: tps) -> error "Expected type-level function, got %a" fmt_kind k 

and check_kind tp k =
  subst_kind k >>= check_kind' tp 

and check_kind' tp k =
  match tp, k with
  | TLam(a, tp2), KArrow(k1, k2)->
      fresh rename_tp a tp2 >>= (fun (a, tp2) ->
      with_hyp (a, Type(Univ, k1, None))
        (check_kind tp2 k2 >>= (fun tp2 ->
         return (TLam(a, tp2)))))
  | TLam(a, tp2), KVar kvar ->
      fresh rename_tp a tp2 >>= (fun (a, tp2) -> 
      expand_karrow kvar >>
      check_kind tp k >>= (fun tp -> 
      subst_kind k >>= (fun k -> 
      return (TAnnot(tp, k)))))
  | TLam(_, _), _ -> error "Kind mismatch, expected function kind, got %a" fmt_kind k 
  | TLet(a, tp1, tp2), k when checkable_tycon tp1 ->
      fresh rename_tp a tp2 >>= (fun (a, tp2) -> 
      newid "k" >>= (fun kvar -> 
      (with_hyp  (kvar, Kind(Exist, None)) 
      (with_hyp (a, Type(Univ, KVar kvar,  None))
        (check_kind tp1 (KVar kvar) >>= (fun tp1 -> 
         subst_kind (KVar kvar) >>= (fun karg -> 
         (orelse (wellsorted_before kvar karg)
                 (error "Could not infer kind for '%s'" a)) >>
         check_kind tp2 k >>= (fun tp2 ->
         return (TLet(a, TAnnot(tp1, karg), tp2))))))))))
  | TLet(a, tp1, tp2), k ->
      synth_kind tp1 >>= (fun (tp1, k1) -> 
      fresh rename_tp a tp2 >>= (fun (a, tp2) ->
      with_hyp (a, Type(Univ, k1, None)) 
        (check_kind tp2 k >>= (fun tp2 -> 
         return (TLet(a, tp1, tp2))))))
  | _, _ -> synth_kind tp >>= (fun (tp, k') -> 
            subkind k' k >>
            return tp)

let rec atomic = function
  | TVar _ 
  | TAnnot(_, _) -> true
  | TApp(tp, ts) -> atomic tp
  | _            -> false 
  


let rec whnf tp =
  subst tp >>= whnf' 

and whnf' tp = 
  match tp with
  | Num
  | Bool
  | String
  | Pure _ 
  | Next _ 
  | Stream _ 
  | G _ 
  | Product _ 
  | Arrow (_, _)  
  | Forall (_, _, _) 
  | Exists (_, _, _) 
  | F _ 
  | Tensor _ 
  | Lolli (_, _)    
  | Dom _ 
  | Frame _  
  | Svg _ 
  | TLam (_, _)  
  | TVar _                     -> return (TApp(tp, []))
  | TLet (a, tp1, tp2)         -> tp_subst tp1 a tp2 >>= whnf 
  | TAnnot(tp, k)              -> whnf tp >>= (fun tp ->
                                  return(if atomic tp then tp else TAnnot(tp, k)))
  | TApp(tp, [])               -> whnf tp
  | TApp(tp, tps)              ->
      whnf tp >>= (fun tp ->
      match tp with 
      | TAnnot(tp, k)   -> reduce_spine k tp tps
      | TVar _          -> return (TApp(tp, tps))
      | TApp(tp', tps') -> return (TApp(tp', tps' @ tps))
      | _ -> assert false)


and reduce_spine k hd args =
  match k, hd, args with
  | _, _, []              -> return hd
  | _, TAnnot(hd', k'), _ -> reduce_spine k' hd' args 
  | KArrow(k1, k2), TLam(a, tbody), arg :: args' ->
      tp_subst (TAnnot(arg, k1)) a tbody >>= whnf >>= (fun tbody' -> 
      if atomic tbody' then
        return (tapp tbody' args')
      else
        reduce_spine k2 tbody' args')
  | _ -> assert false 






















