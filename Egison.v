(* Copyright (c) Akira Kawata All rights reserved. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.
From Egison Require Import Maps.

Module Egison.

  Definition varid := string.

   Inductive exp : Type :=
  | evar : varid -> exp
  | eint : nat -> exp
  (* | tlmb : varid -> exp -> exp *)
  (* | tapp : exp -> exp -> exp *)
  | etpl : exp -> exp -> exp
  | ecll : list exp -> exp
  | epair : exp -> exp -> exp
  | emal : exp -> exp -> (ptn * exp) -> exp
  | esm : exp
  | emtc : (list (pptn * exp * (list (dptn * exp)))) -> exp
  | etplmtc : exp -> exp -> exp
  with ptn : Type :=
  | pwld : ptn
  | pvar : varid -> ptn
  | pval : exp -> ptn
  | ppair : ptn -> ptn -> ptn
 with pptn : Type :=
  | ppdol : pptn
  | ppvar : varid -> pptn
  | pppair : pptn -> pptn -> pptn
  with dptn : Type :=
  | dpvar :  varid -> dptn
  | dppair :  dptn -> dptn -> dptn.

   Inductive ty : Type :=
   | tint : ty
   | ttpl : ty -> ty -> ty
   | tcll : ty -> ty
   | tpair : ty -> ty -> ty
   | tmtc : ty -> ty
   | tptn : ty -> ty
   | tpptn : ty -> list ty -> ty
   | tdptn : ty -> ty.

  (* Definition ppex1 := ppdol : pptn. *)

  Definition env := partial_map exp.
  Definition tenv := partial_map ty.

  (* Definition mlcssize (f : exp -> nat) (mcl : pptn * exp * (list (dptn * exp))) : nat := *)
  (*   let '(_, m1, l) := mcl in *)
  (*   max (f m1) (fold_left max (map (compose f snd) l) 0). *)

  (* Fixpoint expsize (m: exp) : nat := *)
  (*   match m with *)
  (*   | evar _ => 1 *)
  (*   | eint _ => 1 *)
  (*   (* | tlmb _ n => 1 + expsize n *) *)
  (*   (* | tapp n1 n2 => 1 + max (expsize n1) (expsize n2) *) *)
  (*   | etpl ms => 1 + fold_left max (map expsize ms) 0 *)
  (*   | ecll ms => 1 + fold_left max (map expsize ms) 0 *)
  (*   | epair m1 m2 => 1 + max (expsize m1) (expsize m2) *)
  (*   | emal m1 m2 pts => 1 + max (max (expsize m1) (expsize m2)) (fold_left max (map (compose expsize snd) pts) 0) *)
  (*   | esm => 1 *)
  (*   | emtc mcl => 1 + fold_left max (map (mlcssize expsize) mcl) 0 *)
  (*   end. *)

  Definition mclsvalue (f : exp -> Prop) (mcl : pptn * exp * (list (dptn * exp))) :=
    let '(_, m1, l) := mcl in (f m1) /\ (List.Forall (fun m => f (snd m))) l.

  Definition mclsexps (mcl : pptn * exp * (list (dptn * exp))) : list exp :=
    let '(_, m1, l) := mcl in
    m1 :: map (fun m => snd m) l.

  Inductive value : exp -> Prop :=
  | V_Var : forall i, value (evar i)
  | V_Int : forall i, value (eint i)
  | V_Tpl : forall m1 m2, value m1 -> value m2 -> value (etpl m1 m2)
  | V_Cll : forall ms, Forall value ms -> value (ecll ms)
  | V_Pair : forall m1 m2, value m1 /\ value m2 -> value (epair m1 m2)
  | V_Mal : forall m1 m2 pt, value m1 -> value m2 -> value (snd pt) -> value (emal m1 m2 pt)
  | V_Mtc : forall mcls, Forall value (concat (map mclsexps mcls)) -> value (emtc mcls)
  | V_Tplmtc : forall m1 m2, value m1 -> value m2 -> value (etplmtc m1 m2).
  (* | V_Lmb : forall i m, value (tlmb i m) *)

  Import ListNotations.

  Definition ms : Type := ((list (ptn * exp * env * exp)) * env * env).
  Definition ma : Type := (ptn * exp * env * exp).

  Fixpoint filtersome {A: Type} (l: list (option A)) : list A :=
    match l with
    | [] => []
    | (Some v)::r => v::filtersome r
    | None::r => filtersome r
    end.

  Inductive same_length_list {A B: Type} : (list A) -> (list B) -> Prop :=
  | sll_nil : same_length_list [] []
  | sll_cons : forall h1 h2 l1 l2, same_length_list l1 l2 -> same_length_list (h1::l1) (h2::l2).

  Inductive same_length_list3 {A B C: Type} : (list A) -> (list B) -> (list C) -> Prop :=
  | sll_nil3 : same_length_list3 [] [] []
  | sll_cons3 : forall h1 h2 h3 l1 l2 l3, same_length_list3 l1 l2 l3 -> same_length_list3 (h1::l1) (h2::l2) (h3::l3).

  Fixpoint zip {A B: Type} (l1:list A)  (l2: list B) : (list (A*B)) :=
    match (l1, l2) with
    | ([], _) => []
    | (_, []) => []
    | (h1::r1, h2::r2) => (h1,h2) :: zip r1 r2
    end.

  Fixpoint zip3 {A B C: Type} (l1:list A)  (l2: list B) (l3: list C) : (list (A*B*C)) :=
    match (l1, l2, l3) with
    | ([], _, _) => []
    | (_, [], _) => []
    | (_, _, []) => []
    | (h1::r1, h2::r2, h3::r3) => (h1,h2,h3) :: zip3 r1 r2 r3
    end.

  Fixpoint zip4 {A B C D: Type} (l1:list A)  (l2: list B) (l3: list C) (l4: list D) : (list (A*B*C*D)) :=
    match (l1, l2, l3, l4) with
    | ([], _, _, _) => []
    | (_, [], _, _) => []
    | (_, _, [], _) => []
    | (_, _, _, []) => []
    | (h1::r1, h2::r2, h3::r3, h4::r4) => (h1,h2,h3,h4) :: zip4 r1 r2 r3 r4
    end.

  Definition is_epair (t: exp) : Prop :=
    match t with
    | (epair _ _) => True
    | _ => False
    end.

  Definition is_pval (p: ptn) : Prop :=
    match p with
    | (pval _) => True
    | _ => False
    end.

  Definition is_ppair (p: ptn) : Prop :=
    match p with
    | (ppair _ _) => True
    | _ => False
    end.

  Inductive type : (tenv * exp * ty * tenv) -> Prop :=
  | T_Var : forall Gamma s T, Gamma s = Some T -> type (Gamma, (evar s), T, Gamma)
  | T_Int : forall Gamma i, type (Gamma, (eint i), tint, Gamma)
  | T_Pair : forall Gamma e1 T1 e2 T2, type (Gamma, e1, T1, Gamma) ->
                                  type (Gamma, e2, T2, Gamma) ->
                                  type (Gamma, (epair e1 e2), (tpair T1 T2), Gamma)
  | T_Cll : forall Gamma es T, Forall type (map (fun e => (Gamma,e,T,Gamma)) es) ->
                          type (Gamma, (ecll es), (tcll T), Gamma)
  | T_Sm : forall Gamma T, type (Gamma, esm, (tmtc T), Gamma)
  | T_TplMtc : forall Gamma e1 T1 e2 T2, type (Gamma, e1, (tmtc T1), Gamma) ->
                                    type (Gamma, e2, (tmtc T2), Gamma) ->
                                    type (Gamma, (etplmtc e1 e2), (tmtc (ttpl T1 T2)), Gamma)
  | T_Mal : forall Gamma e1 e2 e3 T1 T2 Gamma1 p,
      type (Gamma, e1, T1, Gamma) ->
      type (Gamma, e2, (tmtc T1), Gamma) ->
      typeptn (Gamma, p, (tptn T1), Gamma1) ->
      type (Gamma1, e3, T2, Gamma1) ->
      type (Gamma, emal e1 e2 (p, e3), tcll T2, Gamma)
  with typeptn : (tenv * ptn * ty * tenv) -> Prop :=
  | TP_Wld : forall Gamma T, typeptn (Gamma, pwld, T, Gamma)
  | TP_Var : forall Gamma s T, typeptn (Gamma, (pvar s), (tptn T), s |-> T ; Gamma)
  | TP_Val : forall Gamma e T, type (Gamma, e, T, Gamma) -> typeptn (Gamma, pval e, tptn T, Gamma)
  | TP_Pair : forall Gamma p1 T1 p2 T2 Gamma1 Gamma2,
      typeptn (Gamma, p1, tptn T1, Gamma1) ->
      typeptn (Gamma, p2, tptn T2, Gamma2) ->
      typeptn (Gamma, ppair p1 p2, tptn (tpair T1 T2), Gamma2)
  with typepptn : (tenv * pptn * ty * tenv) -> Prop :=
  | TPP_Dol : forall Gamma T, typepptn (Gamma, ppdol, tpptn T [T], Gamma)
  | TPP_Var : forall Gamma s T, typepptn (Gamma, ppvar s, tpptn T [], Gamma)
  | TPP_Pair : forall Gamma pp1 T1 S1 pp2 T2 S2 S12,
      typepptn (Gamma, pp1, tpptn T1 S1, Gamma) ->
      typepptn (Gamma, pp2, tpptn T2 S2, Gamma) ->
      S12 = S1 ++ S2 ->
      typepptn (Gamma, pppair pp1 pp2, tpptn (tpair T1 T2) S12, Gamma)
  with typedptn : (tenv * dptn * ty * tenv) -> Prop :=
  | TDP_Var : forall Gamma s T, typedptn (Gamma, (dpvar s), (tdptn T), s |-> T ; Gamma)
  | TDP_Pair : forall Gamma dp1 T1 Gamma1 dp2 T2 Gamma2,
      typedptn (Gamma, dp1, tdptn T1, Gamma1) ->
      typedptn (Gamma, dp2, tdptn T2, Gamma2) ->
      typedptn (Gamma, dppair dp1 dp2, tdptn (tpair T1 T2), Gamma1 @@ Gamma2).

  Theorem T_Int_example : type (empty, (eint 10), tint, empty).
  Proof.
    econstructor.
  Qed.

  Inductive eval : (env * exp * exp)-> Prop :=
  | E_VarIn : forall i Gamma t, (Gamma i) = Some t -> eval (Gamma, (evar i), t)
  | E_VarOut : forall i Gamma, (Gamma i) = None -> eval (Gamma, (evar i), (evar i))
  | E_Int : forall i e, eval (e, (eint i), (eint i))
  | E_Tpl : forall Gamma t1 t2 v1 v2, eval (Gamma, t1, v1) -> eval (Gamma, t2, v2) -> eval (Gamma, etpl t1 t2, etpl v1 v2)
  | E_Cll : forall e ts vs, same_length_list ts vs ->
                      Forall eval (map (fun tpl => let '(t,v) := tpl in (e,t,v)) (zip ts vs)) -> eval (e, (ecll ts), (ecll vs))
  | E_Pair : forall e t1 t2 v1 v2, eval (e, t1, v1) -> eval (e, t2, v2) -> eval (e, (epair t1 t2), (epair v1 v2))
  | E_Sm : forall Gamma, eval (Gamma, esm, esm)
  (* | emtc : forall Gamma (ts: (list (pptn * exp * (list (dptn * exp))))), eval Gamma ((emtc ts), (emtc vs)) *)
  | E_Tplmtc : forall Gamma t1 t2 v1 v2, eval (Gamma, t1, v1) -> eval (Gamma, t2, v2) -> eval (Gamma, etplmtc t1 t2, etplmtc v1 v2)
  | E_Emal : forall Gamma M N p L v_v v m_m m_e Delta_v, same_length_list Delta_v v_v -> eval (Gamma, M,v) -> evalmtc Gamma N [(m_m, m_e)] -> evalms3 [[([(p,m_m,m_e,v)], Gamma, empty)]] Delta_v ->
                                                  Forall eval (map (fun t => let '(d,v) := t in (Gamma @@ d, L, v)) (zip Delta_v v_v)) ->
                                                  eval (Gamma, (emal M N (p, L)), ecll v_v)

  with evalmtc : env -> exp -> list (exp * env) -> Prop :=
  | Emtc_Sm : forall Gamma, evalmtc Gamma esm [(esm, Gamma)]
  | Emtc_Mtc : forall Gamma l, evalmtc Gamma (emtc l) [((emtc l), Gamma)]
  | Emtc_Tpl : forall Gamma m1 m2 n1 n2, eval (Gamma, (etplmtc m1 m2), (etplmtc n1 n2)) -> evalmtc Gamma (etplmtc m1 m2) [(n1, Gamma); (n2, Gamma)]

  with evaldp : dptn -> exp -> option env -> Prop :=
  | Edp_Var : forall z v, value v -> evaldp (dpvar z) v (Some (z |-> v))
  | Edp_Pair : forall p1 p2 v1 v2 g1 g2,
      value v1 -> value v2 -> evaldp p1 v1 (Some g1) -> evaldp p2 v2 (Some g2) ->
      evaldp (dppair p1 p2) (epair v1 v2) (Some (g1 @@ g2))
  | Edp_Fail : forall t p1 p2, not (is_epair t) -> evaldp (dppair p1 p2) t None

  with evalpp : pptn -> env -> ptn -> option ((list ptn) * env) -> Prop :=
  | Epp_Dol : forall g p, evalpp ppdol g p (Some ([p], empty))
  | Epp_Var : forall i g m v, eval (g, m, v) -> evalpp (ppvar i) g (pval m) (Some ([], (i |-> v)))
  | Epp_Pair : forall pp1 pp2 p1 p2 g pv1 pv2 g1 g2,
                evalpp pp1 g p1 (Some (pv1,g1)) -> evalpp pp2 g p2 (Some (pv2,g2)) ->
                evalpp (pppair pp1 pp2) g (ppair p1 p2) (Some ((pv1 ++ pv2), (g1 @@ g2)))
  | Epp_VarFail : forall y g p, not (is_pval p) -> evalpp (ppvar y) g p None
  | Epp_PairFail : forall pp1 pp2 p g, not (is_ppair p) -> evalpp (pppair pp1 pp2) g p None

  with evalms1 : ((list ms) * option env * option (list ms)) -> Prop :=
  | Ems1_Nil : evalms1 ([], None, None)
  | Ems1_ANil : forall sv g d, evalms1 ((([],g,d)::sv), (Some d), (Some sv))
  | Ems1 : forall p m mg v av g d sv avv d1,
        evalma (g @@ d) (p,m,mg,v) avv d1 ->
        evalms1 ((((p,m,mg,v)::av, g, d)::sv), None, (Some ((map (fun ai => (ai ++ av, g, d @@ d1)) avv) ++ sv)))

  with evalms2 : (list (list ms)) -> (list env) -> (list (list ms)) -> Prop :=
  | Ems2 : forall svv gvv svv1 gvv1 svv2,
      same_length_list3 svv gvv svv1 ->
      Forall evalms1 (zip3 svv gvv svv1) ->
      (filtersome gvv) = gvv1 ->
      (filtersome svv1) = svv2 ->
      evalms2 svv gvv1 svv2

  with evalms3 : (list (list ms)) -> (list env) -> Prop :=
  | Ems3_nil : evalms3 [[]] []
  | Ems3 : forall svv gv svv1 dv gdv, evalms2 svv gv svv1 -> evalms3 svv1 dv -> gdv = gv ++ dv ->
                             evalms3 svv gdv

  with evalma : env -> ma -> list (list ma) -> env -> Prop :=
  | Ema_Some : forall x g v d, evalma g (pvar x, esm, d, v) [[]] (x |-> v)
  | Ema_Ppfail : forall p g pp m sv pv d v avv g1,
      evalpp pp g p None -> evalma g (p,(emtc pv),d,v) avv g1 ->
      evalma g (p,emtc ((pp,m,sv)::pv),d,v) avv g1
  | Ema_Dpfail : forall p g pp m dp n sv pv d v pv1 d1 avv g1,
      evalpp pp g p (Some (pv1, d1)) -> evaldp dp v None ->
      evalma g (p, emtc ((pp,m,sv)::pv),d,v) avv g1 ->
      evalma g (p, emtc ((pp,m,(dp,n)::sv)::pv),d,v) avv g1
  | Ema : forall p Gamma pp M dp N sigma_v Delta v phi1_v p1_v Delta1 Delta2 v1_vv m1_v,
      evalpp pp Gamma p (Some (p1_v, Delta1)) ->
      evaldp dp v (Some Delta2) ->
      eval (Delta @@ Delta1 @@ Delta2, N, ecll v1_vv) ->
      evalmtc Gamma M m1_v ->
      evalma Gamma (p, emtc ((pp,M,(dp,N)::sigma_v)::phi1_v), Delta, v)
             ((map (fun tpl => match tpl with
                              | (etpl v11 v12) => map (fun t => let '(v1, (m1, Gamma1), p1) := t in (p1,m1,Gamma1,v1)) (zip3 [v11;v12] m1_v p1_v)
                              | v11 => map (fun t => let '(v1, (m1, Gamma1), p1) := t in (p1,m1,Gamma1,v1)) (zip3 [v11] m1_v p1_v)
                              end
                   ) v1_vv)) empty.

  (* Following Egison code is translated into Coq as follows. *)
  (* (define $unordered-pair *)
  (*   (matcher *)
  (*     {[<pair $ $> [something something] *)
  (*       {[[$x $y] {[x y] [y x]}]}] *)
  (*      [$ something *)
  (*       {[$tgt {tgt}]}]})) *)

  (* (match-all [1 2] unordered-pair {[<pair $a $b> [a b]]}) ===> {[1,2] [2,1]} *)

  Open Scope string_scope.
  Definition unordered_pair: exp :=
    (emtc [(pppair ppdol ppdol, etplmtc esm esm,
            [(dppair (dpvar "x") (dpvar "y"), (ecll [(etpl (evar "x") (evar "y")); etpl (evar "y") (evar "x")]))]);
           (ppdol, esm,
            [(dpvar "tgt", ecll [evar "tgt"])])]).

  Definition match_all_example: exp :=
    (emal (epair (eint 1) (eint 2)) unordered_pair (ppair (pvar "a") (pvar "b"),etpl (evar "a") (evar "b"))).
  Theorem unordered_pair_example : eval (empty, match_all_example, ecll [etpl (eint 1) (eint 2);etpl (eint 2) (eint 1)]).
  Proof.
    econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - repeat econstructor.
    - econstructor.
      + econstructor.
        * repeat econstructor.
        * econstructor.
          -- econstructor.
             eapply Ema.
             --- repeat econstructor.
             --- repeat econstructor.
             --- repeat econstructor.
             --- repeat econstructor.
          -- repeat constructor.
        * repeat constructor.
        * repeat constructor.
      + repeat econstructor.
      + repeat econstructor.
    - repeat econstructor.
 Qed.
End Egison.
