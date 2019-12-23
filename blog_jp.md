# 概要
Egisonのパターンマッチの動作を定理証明支援系Coq上で定義し、「Egisonの処理系が項Mを値vに評価する」という命題をCoq上で表現できるようにしました。

# 動機
Egisonの中核的な機能はユーザが拡張可能なパターンマッチ機構です。例えば以下に示すように、ペアに対してその順序を無視してパターンマッチすることが可能です。
```
(define $unordered-pair
  (matcher
    {[<pair $ $> [something something]
      {[[$x $y] {[x y] [y x]}]}]
     [$ something
      {[$tgt {tgt}]}]}))

(match-all [1 2] unordered-pair {[<pair $a $b> [a b]]})
; ===> {[1 2] [2 1]}
```
しかし、その拡張性のためにこのパターンマッチの動作は大変複雑です。[Egi, Nishiwaki (2018)](https://arxiv.org/abs/1808.10603)はEgisonのパターンマッチの動作をbig-step styleの操作的意味論として次のように定義しています。
![Egisonの操作的意味論](https://raw.githubusercontent.com/akawashiro/formalized-egison/master/semantics.png)

型健全性などのEgisonの性質を証明する際はこの操作的意味論を使うことになりますが、規則の種類、数が多いので証明を手で書くと間違えてしまいそうです。そこで今回の記事では[Egi, Nishiwaki (2018)](https://arxiv.org/abs/1808.10603)の操作的意味論をCoqに書き直しました。

# formalized-egison
[formalized-egison](https://github.com/akawashiro/formalized-egison)は[Egi, Nishiwaki (2018)](https://arxiv.org/abs/1808.10603)によるEgisonの操作的意味論をCoqに書き直したものです。意味論を定義している部分は[Egison.v](https://github.com/akawashiro/formalized-egison/blob/master/Egison.v)の以下の部分です。
```Coq
Inductive eval : (env * tm * tm)-> Prop :=
  | evarin : forall i Gamma t, (Gamma i) = Some t -> eval (Gamma, (tvar i), t)
  | evarout : forall i Gamma, (Gamma i) = None -> eval (Gamma, (tvar i), (tvar i))
  | eint : forall i e, eval (e, (tint i), (tint i))
  | etpl : forall Gamma t1 t2 v1 v2, eval (Gamma, t1, v1) -> eval (Gamma, t2, v2) -> eval (Gamma, ttpl t1 t2, ttpl v1 v2)
  | ecll : forall e ts vs, same_length_list ts vs ->
                      Forall eval (map (fun tpl => let '(t,v) := tpl in (e,t,v)) (zip ts vs)) -> eval (e, (tcll ts), (tcll vs))
  | epair : forall e t1 t2 v1 v2, eval (e, t1, v1) -> eval (e, t2, v2) -> eval (e, (tpair t1 t2), (tpair v1 v2))
  | esm : forall Gamma, eval (Gamma, tsm, tsm)
  (* | emtc : forall Gamma (ts: (list (pptn * tm * (list (dptn * tm))))), eval Gamma ((tmtc ts), (tmtc vs)) *)
  | etplmtc : forall Gamma t1 t2 v1 v2, eval (Gamma, t1, v1) -> eval (Gamma, t2, v2) -> eval (Gamma, ttplmtc t1 t2, ttplmtc v1 v2)
  | etmal : forall Gamma M N p L v_v v m_m m_e Delta_v, same_length_list Delta_v v_v -> eval (Gamma, M,v) -> evalmtc Gamma N [(m_m, m_e)] -> evalms3 [[([(p,m_m,m_e,v)], Gamma, empty)]] Delta_v ->
                                                  Forall eval (map (fun t => let '(d,v) := t in (Gamma @@ d, L, v)) (zip Delta_v v_v)) ->
                                                  eval (Gamma, (tmal M N (p, L)), tcll v_v)

  with evalmtc : env -> tm -> list (tm * env) -> Prop :=
  | emtcsm : forall Gamma, evalmtc Gamma tsm [(tsm, Gamma)]
  | emtcmtc : forall Gamma l, evalmtc Gamma (tmtc l) [((tmtc l), Gamma)]
  | emtctpl : forall Gamma m1 m2 n1 n2, eval (Gamma, (ttplmtc m1 m2), (ttplmtc n1 n2)) -> evalmtc Gamma (ttplmtc m1 m2) [(n1, Gamma); (n2, Gamma)]

  with evaldp : dptn -> tm -> option env -> Prop :=
  | edpvar : forall z v, value v -> evaldp (dpvar z) v (Some (z |-> v))
  | edppair : forall p1 p2 v1 v2 g1 g2,
      value v1 -> value v2 -> evaldp p1 v1 (Some g1) -> evaldp p2 v2 (Some g2) ->
      evaldp (dppair p1 p2) (tpair v1 v2) (Some (g1 @@ g2))
  | edpfail : forall t p1 p2, not (is_tpair t) -> evaldp (dppair p1 p2) t None

  with evalpp : pptn -> env -> ptn -> option ((list ptn) * env) -> Prop :=
  | eppdol : forall g p, evalpp ppdol g p (Some ([p], empty))
  | eppvar : forall i g m v, eval (g, m, v) -> evalpp (ppvar i) g (pval m) (Some ([], (i |-> v)))
  | epppair : forall pp1 pp2 p1 p2 g pv1 pv2 g1 g2,
                evalpp pp1 g p1 (Some (pv1,g1)) -> evalpp pp2 g p2 (Some (pv2,g2)) ->
                evalpp (pppair pp1 pp2) g (ppair p1 p2) (Some ((pv1 ++ pv2), (g1 @@ g2)))
  | eppvarfail : forall y g p, not (is_pval p) -> evalpp (ppvar y) g p None
  | epppairfail : forall pp1 pp2 p g, not (is_ppair p) -> evalpp (pppair pp1 pp2) g p None

  with evalms1 : ((list ms) * option env * option (list ms)) -> Prop :=
  | ems1nil : evalms1 ([], None, None)
  | ems1anil : forall sv g d, evalms1 ((([],g,d)::sv), (Some d), (Some sv))
  | ems1 : forall p m mg v av g d sv avv d1,
        evalma (g @@ d) (p,m,mg,v) avv d1 ->
        evalms1 ((((p,m,mg,v)::av, g, d)::sv), None, (Some ((map (fun ai => (ai ++ av, g, d @@ d1)) avv) ++ sv)))

  with evalms2 : (list (list ms)) -> (list env) -> (list (list ms)) -> Prop :=
  | ems2 : forall svv gvv svv1 gvv1 svv2,
      same_length_list3 svv gvv svv1 ->
      Forall evalms1 (zip3 svv gvv svv1) ->
      (filtersome gvv) = gvv1 ->
      (filtersome svv1) = svv2 ->
      evalms2 svv gvv1 svv2

  with evalms3 : (list (list ms)) -> (list env) -> Prop :=
  | ems3nil : evalms3 [[]] []
  | ems3 : forall svv gv svv1 dv gdv, evalms2 svv gv svv1 -> evalms3 svv1 dv -> gdv = gv ++ dv ->
                             evalms3 svv gdv

  with evalma : env -> ma -> list (list ma) -> env -> Prop :=
  | emasome : forall x g v d, evalma g (pvar x, tsm, d, v) [[]] (x |-> v)
  | emappfail : forall p g pp m sv pv d v avv g1,
      evalpp pp g p None -> evalma g (p,(tmtc pv),d,v) avv g1 ->
      evalma g (p,tmtc ((pp,m,sv)::pv),d,v) avv g1
  | emadpfail : forall p g pp m dp n sv pv d v pv1 d1 avv g1,
      evalpp pp g p (Some (pv1, d1)) -> evaldp dp v None ->
      evalma g (p, tmtc ((pp,m,sv)::pv),d,v) avv g1 ->
      evalma g (p, tmtc ((pp,m,(dp,n)::sv)::pv),d,v) avv g1
  | ema : forall p Gamma pp M dp N sigma_v Delta v phi1_v p1_v Delta1 Delta2 v1_vv m1_v,
      evalpp pp Gamma p (Some (p1_v, Delta1)) ->
      evaldp dp v (Some Delta2) ->
      eval (Delta @@ Delta1 @@ Delta2, N, tcll v1_vv) ->
      evalmtc Gamma M m1_v ->
      evalma Gamma (p, tmtc ((pp,M,(dp,N)::sigma_v)::phi1_v), Delta, v)
             ((map (fun tpl => match tpl with
                              | (ttpl v11 v12) => map (fun t => let '(v1, (m1, Gamma1), p1) := t in (p1,m1,Gamma1,v1)) (zip3 [v11;v12] m1_v p1_v)
                              | v11 => map (fun t => let '(v1, (m1, Gamma1), p1) := t in (p1,m1,Gamma1,v1)) (zip3 [v11] m1_v p1_v)
                              end
                   ) v1_vv)) empty.
```
最も重要なのは`eval (Gamma, M, v)`で「環境Gammaのもとで項Mが値vに評価される」という命題です。例えば、冒頭のプログラム中の`(match-all [1 2] unordered-pair {[<pair $a $b> [a b]]})`が`{[1 2] [2 1]}`に評価される、というのは次のようなCoqの命題として表すことができます。
```Coq
Definition unordered_pair: tm :=
    (tmtc [(pppair ppdol ppdol, ttplmtc tsm tsm,
            [(dppair (dpvar "x") (dpvar "y"), (tcll [(ttpl (tvar "x") (tvar "y")); ttpl (tvar "y") (tvar "x")]))]);
           (ppdol, tsm,
            [(dpvar "tgt", tcll [tvar "tgt"])])]).

Definition match_all_example: tm :=
    (tmal (tpair (tint 1) (tint 2)) unordered_pair (ppair (pvar "a") (pvar "b"),ttpl (tvar "a") (tvar "b"))).

Theorem unordered_pair_example : eval (empty, match_all_example, tcll [ttpl (tint 1) (tint 2);ttpl (tint 2) (tint 1)]).
```
また、Egisonの操作的意味論上でこの評価結果が正しいということも証明できます。 つまり`unordered_pair_example`を証明することができます。証明は長くなるので省略しますが、[Egison.v](https://github.com/akawashiro/formalized-egison/blob/master/Egison.v)の230行目以降にあります。

# 今後の課題
動機の項で述べたようにformalized-egisonの最終的な目標はEgisonの型安全性の証明です。Coqで表現すると
```coq
Theorem type_soundness:
    forall Gamma M T, is_typed Gamma M T => exists v, eval Gamma M v /\ is_typed Gamma v T.
```
となります。ただし`is_typed Gamma M T`は環境`Gamma`の下で項`M`に型`T`がつくと読みます。
今後は[typed-egison](https://github.com/egison/typed-egison)の型付け規則をCoqで書き直して`is_typed`を定義した上で`type_soundness`を証明する予定です。
