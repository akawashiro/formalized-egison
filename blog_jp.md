# 概要
Egisonのパターンマッチの動作をCoq上で定義し、「Egisonの処理系が項Mを値vに評価する」という命題をCoq上で表現できるようにしました。

# 動機
Egisonの中核的な機能はユーザが拡張可能なパターンマッチ機構です。例えば以下に示すように、ペアに対してその順序を無視してパターンマッチすることが可能です。
```lisp
(define $unordered-pair
  (matcher
    {[<pair $ $> [something something]
      {[[$x $y] {[x y] [y x]}]}]
     [$ something
      {[$tgt {tgt}]}]}))

(match-all [1 2] unordered-pair {[<pair $a $b> [a b]]})
; ===> {[1 2] [2 1]}
```
しかし、その拡張性のためにこのパターンマッチの動作は大変複雑です。
[Egi, Nishiwaki (2018)](https://arxiv.org/abs/1808.10603)はEgisonのパターンマッチの動作をbig-step styleの操作的意味論として次のように定義しています。
![Egisonの操作的意味論](https://raw.githubusercontent.com/akawashiro/formalized-egison/master/semantics.png)
型健全性などのEgisonの性質を証明する際はこの操作的意味論を使うことになりますが、規則の種類、数が多いので証明を手で書くと間違えてしまいそうです。
そこで今回の記事ではEgi, Nishiwaki (2018)の操作的意味論をCoqに書き直しました。

# formalized-egison
[formalized-egison](https://github.com/akawashiro/formalized-egison) はEgi, Nishiwaki (2018)によるEgisonの操作的意味論をCoqに書き直したものです。
主要な定義は[Egison.v](https://github.com/akawashiro/formalized-egison/blob/master/Egison.v)にあります。
`eval (Gamma, M, v)`は「環境Gammaのもとで項Mが値vに評価される」という命題です。
例えば、冒頭のプログラム中の`(match-all [1 2] unordered-pair {[<pair $a $b> [a b]]})`が`{[1 2] [2 1]}`に評価される、というのは次のようなCoqの命題として表すことができます。
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
Egisonの操作的意味論上でこの評価結果が正しいということも証明できます。
つまり`unordered_pair_example`を証明することができます。
証明は長くなるので省略します。
詳しくは[Egison.v](https://github.com/akawashiro/formalized-egison/blob/master/Egison.v)の230行目以降を見てください。

# 今後の課題
動機の項で述べたようにformalized-egisonの最終的な目標はEgisonの型安全性の証明です。Coqで表現すると
```coq
Theorem type_soundness:
    forall Gamma M T, is_typed Gamma M T => exists v, eval Gamma M v /\ is_typed Gamma v T.
```
となります。ただし`is_typed Gamma M T`は環境`Gamma`の下で項`M`に型`T`がつくと読みます。
今後は[typed-egison](https://github.com/egison/typed-egison)の型付け規則をCoqで書き直して`is_typed`を定義した上で`type_soundness`を証明する予定です。
