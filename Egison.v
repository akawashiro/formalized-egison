Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.
From Coq Require Import Program.Basics.
From Egison Require Import Maps.

Module Egison.

  Definition varid := string.

   Inductive tm : Type :=
  | tvar : varid -> tm
  | tint : nat -> tm
  | tlmb : varid -> tm -> tm
  | tapp : tm -> tm -> tm
  | ttpl : list tm -> tm
  | tcll : list tm -> tm
  | tctr : varid -> list tm -> tm
  | tmal : tm -> tm -> (list (ptn * tm)) -> tm
  | tsm : tm
  | tmtc : (list (pptn * tm * (list (dptn * tm)))) -> tm
  with ptn : Type :=
  | pwld : ptn
  | pvar : varid -> ptn
  | pval : tm -> ptn
  | pctr : varid -> list tm -> ptn
 with pptn : Type :=
  | ppdol : pptn
  | ppvar : varid -> pptn
  | ppctr : varid -> (list pptn) -> pptn
  with dptn : Type :=
  | dpvar :  varid -> dptn
  | dpctr :  varid -> (list dptn) -> dptn.

  Open Scope string_scope.
  Definition x :=  "x".
  Definition y := "y".
  Definition z := "z".

  Definition ppex1 := ppdol : pptn.

  Definition environment := partial_map tm.

  Definition mlcssize (f : tm -> nat) (mcl : pptn * tm * (list (dptn * tm))) : nat :=
    let '(_, m1, l) := mcl in
    max (f m1) (fold_left max (map (compose f snd) l) 0).

  Fixpoint tmsize (m: tm) : nat :=
    match m with
    | tvar _ => 1
    | tint _ => 1
    | tlmb _ n => 1 + tmsize n
    | tapp n1 n2 => 1 + max (tmsize n1) (tmsize n2)
    | ttpl ms => 1 + fold_left max (map tmsize ms) 0
    | tcll ms => 1 + fold_left max (map tmsize ms) 0
    | tctr _ ms => 1 + fold_left max (map tmsize ms) 0
    | tmal m1 m2 pts => 1 + max (max (tmsize m1) (tmsize m2)) (fold_left max (map (compose tmsize snd) pts) 0)
    | tsm => 1
    | tmtc mcl => 1 + fold_left max (map (mlcssize tmsize) mcl) 0
    end.

  Definition mclsvalue (f : tm -> Prop) (mcl : pptn * tm * (list (dptn * tm))) :=
    let '(_, m1, l) := mcl in (f m1) /\ (List.Forall (fun m => f (snd m))) l.

  Definition mclstms (mcl : pptn * tm * (list (dptn * tm))) : list tm :=
    let '(_, m1, l) := mcl in
    m1 :: map (fun m => snd m) l.

  Inductive value : tm -> Prop :=
  | vvar : forall i, value (tvar i)
  | vint : forall i, value (tint i)
  | vlmb : forall i m, value (tlmb i m)
  | vtpl : forall ms, Forall value ms -> value (ttpl ms)
  | vcll : forall ms, Forall value ms -> value (tcll ms)
  | vctr : forall c ms, Forall value ms -> value (tctr c ms)
  | vmal : forall m1 m2 pts, value m1 -> value m2 -> Forall (fun t => value (snd t)) pts -> value (tmal m1 m2 pts)
  | vmtc : forall mcls, Forall value (concat (map mclstms mcls)) -> value (tmtc mcls).

  Definition mlcsvalue (f : tm -> nat -> Prop) (mcl : pptn * tm * (list (dptn * tm))) (s: nat) :=
    match s with
      | (S ss) => (let '(_, m1, l) := mcl in (f m1 ss) /\ (List.Forall (fun m => f (snd m) ss)) l)
      | _ => False
    end.


  Fixpoint value_inside (m: tm) (s: nat) {struct s} : Prop :=
    match m, s with
    | tvar _, _ => True
    | tint _, _ => True
    | tlmb _ _, _ => True
    | ttpl ts, (S ss) => (List.Forall (fun t => value_inside t ss) ts)
    | tcll ts, (S ss) => (List.Forall (fun t => value_inside t ss) ts)
    | tctr _ ts, (S ss) => (List.Forall (fun t => value_inside t ss) ts)
    | tmal m1 m2 pts, (S ss) => value_inside m1 ss /\ value_inside m2 ss /\ List.Forall (fun t => value_inside (snd t) ss) pts
    | tsm, _ => True
    | tmtc mcl, (S ss) => Forall (fun m => mlcsvalue value_inside m ss) mcl
    | _, _ => False
    end.

  Definition value m := value_inside m (tmsize m).

  Fixpoint eval_dptn (p: dptn) (v: tm) : option environment :=

End Egison.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
| String: ty
| Integer : ty
  | Bool  : ty
  | Arrow : ty -> ty -> ty
  | Tuple : list ty -> ty
  | Collection : ty -> ty
  | Pattern : ty -> ty
  | PPPattern : ty -> ty -> ty
  | PDPattern : ty -> ty
  | Matcher : ty -> ty.



(** Note that an abstraction [\x:T.t] (formally, [abs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference here. *)

(** Some examples... *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (abs x Bool (var x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (abs x (Arrow (Arrow Bool Bool)
                      (Arrow Bool Bool))
    (var x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (abs x Bool (abs y Bool (var x))).

(** [notB = \x:Bool. test x then fls else tru] *)

Notation notB := (abs x Bool (test (var x) fls tru)).

(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)

(* ################################################################# *)
(** * Operational Semantics *)

(** To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)

(* ================================================================= *)
(** ** Values *)

(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [tru] and [fls] are the only values.  A [test] expression
    is never a value. *)

(** Second, an application is not a value: it represents a function
    being invoked on some argument, which clearly still has work left
    to do. *)

(** Third, for abstractions, we have a choice:

      - We can say that [\x:T. t] is a value only when [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T. t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Coq makes the first
    choice -- for example,

         Compute (fun x:bool => 3 + 4)

    yields:

          fun x:bool => 7

    Most real-world functional programming languages make the second
    choice -- reduction of a function's body only begins when the
    function is actually applied to an argument.  We also make the
    second choice here. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.

Hint Constructors value.

(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program is _closed_ -- that is, it
    contains no free variables.

    (Conversely, a term with free variables is often called an _open
    term_.) *)

(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms.  *)

(* ================================================================= *)
(** ** Substitution *)

(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool. test x then tru else x) fls

    to

       test fls then tru else fls

    by substituting [fls] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].  In
    informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [s] for [x] in [t]." *)

(** Here are some examples:

      - [[x:=tru] (test x then x else fls)]
           yields [test tru then tru else fls]

      - [[x:=tru] x] yields [tru]

      - [[x:=tru] (test x then x else y)] yields [test tru then tru else y]

      - [[x:=tru] y] yields [y]

      - [[x:=tru] fls] yields [fls] (vacuous substitution)

      - [[x:=tru] (\y:Bool. test y then x else fls)]
           yields [\y:Bool. test y then tru else fls]

      - [[x:=tru] (\y:Bool. x)] yields [\y:Bool. tru]

      - [[x:=tru] (\y:Bool. y)] yields [\y:Bool. y]

      - [[x:=tru] (\x:Bool. x)] yields [\x:Bool. x]

    The last example is very important: substituting [x] with [tru] in
    [\x:Bool. x] does _not_ yield [\x:Bool. tru]!  The reason for
    this is that the [x] in the body of [\x:Bool. x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T11. t12)   = \x:T11. t12
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12     if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]tru             = tru
       [x:=s]fls             = fls
       [x:=s](test t1 then t2 else t3) =
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

(** ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on _closed_ terms (i.e., terms like [\x:Bool. x] that include
    binders for all of the variables they mention), we can sidestep this
    extra complexity, but it must be dealt with when formalizing
    richer languages. *)

(** For example, using the definition of substitution above to
    substitute the _open_ term [s = \x:Bool. r], where [r] is a _free_
    reference to some global resource, for the variable [z] in the
    term [t = \r:Bool. z], where [r] is a bound variable, we would get
    [\r:Bool. \x:Bool. r], where the free reference to [r] in [s] has
    been "captured" by the binder at the beginning of [t].

    Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let [t' = \w:Bool. z], then
    [[x:=s]t'] is [\w:Bool. \x:Bool. r], which does not behave the
    same as [[x:=s]t = \r:Bool. \x:Bool. r].  That is, renaming a
    bound variable changes how [t] behaves under substitution. *)

(** See, for example, [Aydemir 2008] (in Bib.v) for further discussion
    of this issue. *)

(** **** Exercise: 3 stars, standard (substi_correct)  

    The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  | s_var2 : forall y,
      not (is_true (eqb_string x y)) ->
      substi s x (var y) (var y)
  | s_abs1 : forall T t,
      substi s x (abs x T t) (abs x T t)
  | s_abs2 : forall y T t t',
      not (is_true (eqb_string x y)) ->
      substi s x t t' ->
      substi s x (abs y T t) (abs y T t')
  | s_app : forall t1 t2 t1' t2',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x (app t1 t2) (app t1' t2')
  | s_tru :
      substi s x tru tru
  | s_fal :
      substi s x fls fls
  | s_test : forall t1 t2 t3 t1' t2' t3',
      substi s x t1 t1' ->
      substi s x t2 t2' ->
      substi s x t3 t3' ->
      substi s x (test t1 t2 t3) (test t1' t2' t3')
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  intros.
  split.
  - generalize t'.
    induction t; intros t'0 H.
    + unfold subst in H.
      remember (eqb_string x0 s0) as b.
      destruct b; subst; symmetry in Heqb.
      * apply eqb_string_true_iff in Heqb.
        subst.
        apply s_var1.
      * apply eqb_string_false_iff in Heqb.
        apply s_var2.
        unfold not.
        intros.
        unfold is_true in H.
        apply eqb_string_true_iff in H.
        unfold not in Heqb.
        apply Heqb in H.
        destruct H.
    + simpl in H.
      subst.
      apply s_app.
      * apply IHt1. reflexivity.
      * apply IHt2. reflexivity.
    + simpl in H.
      subst.
      remember (eqb_string x0 s0) as b.
      destruct b; subst; symmetry in Heqb.
      * apply eqb_string_true_iff in Heqb.
        subst.
        apply s_abs1.
      * apply eqb_string_false_iff in Heqb.
        apply s_abs2.
        unfold is_true.
        apply Bool.not_true_iff_false.
        apply eqb_string_false_iff.
        assumption.
        apply IHt.
        reflexivity.
    + subst.
      apply s_tru.
    + subst.
      apply s_fal.
    + subst.
      apply s_test.
      * apply IHt1.
        reflexivity.
      * apply IHt2.
        reflexivity.
      * apply IHt3.
        reflexivity.
  - generalize t'.
    induction t; intros t'0 H.
    + inversion H.
      * subst. simpl.
        assert (eqb_string s0 s0 = true).
        symmetry.
        apply eqb_string_refl.
        rewrite H0.
        reflexivity.
        * unfold is_true in H1.
          apply Bool.not_true_iff_false in H1.
          unfold subst.
          rewrite H1.
          reflexivity.
    + inversion H.
      apply IHt1 in H2.
      apply IHt2 in H4.
      unfold subst.
      fold subst.
      rewrite H2.
      rewrite H4.
      reflexivity.
    + inversion H.
      * subst.
      unfold subst.
      fold subst.
         assert (eqb_string s0 s0 = true).
        symmetry.
        apply eqb_string_refl.
        rewrite H0.
        reflexivity.
      * subst.
      unfold subst.
      fold subst.
        unfold is_true in H4.
        apply Bool.not_true_iff_false in H4.
        rewrite H4.
        apply IHt in H5.
        rewrite H5.
        reflexivity.
    + inversion H.
      simpl.
      reflexivity.
    + inversion H.
      simpl.
      reflexivity.
    + inversion H.
      subst.
      unfold subst.
      fold subst.
      apply IHt1 in H3.
      apply IHt2 in H5.
      apply IHt3 in H6.
      rewrite H3, H5, H6.
      reflexivity.
      Qed.

(* ================================================================= *)
(** ** Reduction *)

(** The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

      (\x:T.t12) v2 --> [x:=v2]t12

    is traditionally called _beta-reduction_. *)

(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 --> [x:=v2]t12

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

    ... plus the usual rules for conditionals:

                    --------------------------------               (ST_TestTru)
                    (test tru then t1 else t2) --> t1

                    ---------------------------------              (ST_TestFls)
                    (test fls then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_Test)
      (test t1 then t2 else t3) --> (test t1' then t2 else t3)
*)

(** Formally: *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1  t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(** ** Examples *)

(** Example:

      (\x:Bool->Bool. x) (\x:Bool. x) -->* \x:Bool. x

    i.e.,

      idBB idB -->* idB
*)

Lemma step_example1 :
  (app idBB idB) -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            -->* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  (app idBB (app idBB idB)) -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x)
         (\x:Bool. test x then fls else tru)
         tru
            -->* fls

    i.e.,

       (idBB notB) tru -->* fls.
*)

Lemma step_example3 :
  app (app idBB notB) tru -->* fls.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_TestTru. apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool. x)
         ((\x:Bool. test x then fls else tru) tru)
            -->* fls

    i.e.,

      idBB (notB tru) -->* fls.

    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

Lemma step_example4 :
  app idBB (app notB tru) -->* fls.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_TestTru.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(** We can use the [normalize] tactic defined in the [Smallstep] chapter
    to simplify these proofs. *)

Lemma step_example1' :
  app idBB idB -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  app idBB (app idBB idB) -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  app (app idBB notB) tru -->* fls.
Proof. normalize.  Qed.

Lemma step_example4' :
  app idBB (app notB tru) -->* fls.
Proof. normalize.  Qed.

(** **** Exercise: 2 stars, standard (step_example5)  

    Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  normalize.
  Qed.

Lemma step_example5_with_normalize :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  normalize.
  Qed.
(** [] *)

(* ################################################################# *)
(** * Typing *)

(** Next we consider the typing relation of the STLC. *)

(* ================================================================= *)
(** ** Contexts *)

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

(** Following the usual notation for partial maps, we write [(X |->
    T11, Gamma)] for "update the partial function [Gamma] so that it
    maps [x] to [T]." *)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** Typing Relation *)

(** 
                              Gamma x = T
                            ----------------                            (T_Var)
                            Gamma |- x \in T

                   (x |-> T11 ; Gamma) |- t12 \in T12
                   ----------------------------------                   (T_Abs)
                    Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                         ----------------------                         (T_App)
                         Gamma |- t1 t2 \in T12

                         ---------------------                          (T_Tru)
                         Gamma |- tru \in Bool

                         ---------------------                          (T_Fls)
                         Gamma |- fls \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------------   (T_Test)
                  Gamma |- test t1 then t2 else t3 \in T

    We can read the three-place relation [Gamma |- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in Arrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- app t1 t2 \in T12
  | T_Tru : forall Gamma,
       Gamma |- tru \in Bool
  | T_Fls : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(** ** Examples *)

Example typing_example_1 :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(** Note that, since we added the [has_type] constructors to the hints
    database, [auto] can actually solve this one immediately. *)

Example typing_example_1' :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. auto.  Qed.

(** More examples:

       empty |- \x:A. \y:A->A. y (y x)
             \in A -> (A->A) -> A.
*)

Example typing_example_2 :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(** **** Exercise: 2 stars, standard, optional (typing_example_2_full)  

    Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)

Example typing_example_2_full :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof.
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
  apply T_Var.
  reflexivity.
  eapply T_App.
  apply T_Var.
  reflexivity.
  apply T_Var.
  reflexivity.
  Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (typing_example_3)  

    Formally prove the following typing derivation holds: 

    
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)

Example typing_example_3 :
  exists T,
    empty |-
      (abs x (Arrow Bool Bool)
         (abs y (Arrow Bool Bool)
            (abs z Bool
               (app (var y) (app (var x) (var z)))))) \in
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We can also show that some terms are _not_ typable.  For example, 
    let's check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,

    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y \in T.
*)

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (abs x Bool
            (abs y Bool
               (app (var x) (var y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.  Qed.

(** **** Exercise: 3 stars, standard, optional (typing_nonexample_3)  

    Another nonexample:

    ~ (exists S T,
          empty |- \x:S. x x \in T).
*)

Example typing_nonexample_3 :
  ~ (exists S T,
        empty |-
          (abs x S
             (app (var x) (var x))) \in
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End STLC.

(* Thu Feb 7 20:09:24 EST 2019 *)
