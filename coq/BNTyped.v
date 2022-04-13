Ltac inv H := inversion H; subst; clear H.
Create HintDb bntDB.

Inductive tm :=
  | true
  | false
  | ITE : tm -> tm -> tm -> tm
  | O
  | S : tm -> tm
  | P : tm -> tm
  | IZ : tm -> tm.

Notation "'if' c 'then' u 'else' v" :=
  (ITE c u v)
  (at level 200).

Inductive typ := Bool | Nat.

Inductive has_typ : tm -> typ -> Prop :=
  | ttrue : has_typ true Bool
  | tfalse : has_typ false Bool
  | tif : forall t1 t2 t3 T
      (t1t: has_typ t1 Bool)
      (t2t: has_typ t2 T)
      (t3t: has_typ t3 T),
    has_typ (ITE t1 t2 t3) T
  | tzero : has_typ O Nat
  | tsucc : forall t
      (tt: has_typ t Nat),
    has_typ (S t) Nat
  | tpred : forall t
      (tt: has_typ t Nat),
    has_typ (P t) Nat
  | tiszero : forall t
      (tt: has_typ t Nat),
    has_typ (IZ t) Bool.
#[export] Hint Resolve ttrue tfalse tzero
tsucc tpred tiszero tif : bntDB.

Notation "a ;; b" := (has_typ a b) (at level 5).

Inductive nval : tm -> Prop :=
  | zeroisnval : nval O
  | succisnval : forall n, nval n -> nval (S n).
Inductive val : tm -> Prop :=
  | tisval : val true
  | fisval : val false
  | nvsareval : forall n, nval n -> val n.
Lemma val_O : val O. Proof (nvsareval _ zeroisnval).
#[export] Hint Resolve zeroisnval succisnval
tisval fisval nvsareval val_O: bntDB.

Inductive step : tm -> tm -> Prop :=
  | eiftrue : forall t2 t3,
      step (if true then t2 else t3) t2
  | eiffalse : forall t2 t3,
      step (if false then t2 else t3) t3
  | eif : forall t t' t2 t3
        (IH: step t t'),
      step (if t then t2 else t3) (if t' then t2 else t3)
  | esucc : forall t t'
        (IH: step t t'),
      step (S t) (S t')
  | epredzero :
      step (P O) O
  | epredsucc : forall n
        (IH: nval n),
      step (P (S n)) n
  | epred : forall t t'
        (IH: step t t'),
      step (P t) (P t')
  | eiszerozero :
      step (IZ O) true
  | eiszerosucc : forall n
        (IH: nval n),
      step (IZ (S n)) false
  | eiszero : forall t t'
        (IH: step t t'),
      step (IZ t) (IZ t')
  .

Notation "a --> b" := (step a b) (at level 5).

Inductive stepstar : tm -> tm -> Prop :=
  | zerosteps : forall t, stepstar t t
  | oneormoresteps : forall t1 t2 t3,
      step t1 t2 -> stepstar t2 t3 -> stepstar t1 t3.
Notation "a -->* b" := (stepstar a b) (at level 5).
#[export] Hint Resolve zerosteps
eiftrue eiffalse: bntDB.


Theorem t__unique_typ : forall t T T'
  (tT: t;;T) (tT': t;;T'), T = T'.
Proof with eauto with bntDB.
  induction t; intros;
  inv tT; inv tT'...
Qed.

Theorem v_val_Bool__tof : forall v
    (valv: val v) (vBool: v;;Bool),
  v = true \/ v = false.
Proof with eauto with bntDB.
  intros. inv valv...
  inv H; inv vBool.
Qed.

Theorem v_val_Nat__nval : forall v
    (valv: val v) (vNat: v;;Nat),
  nval v.
Proof with auto.
  intros. inv valv; try solve [inv vNat]...
Qed.



Theorem Progress : forall t
    (twt: exists T, t;;T),
  val t \/ exists t', t --> t'.
Proof with eauto with bntDB.
  intros * [T twt].
  induction twt...
  - destruct IHtwt1;[
    | right; destruct H; eexists; econstructor]...
    inv H. 1,2: right; eexists; econstructor.
    inv twt1; inv H0.
  - destruct IHtwt as [| [t' ?]];[left|right].
    + inv H. 1,2: inv twt. do 2 econstructor...
    + eexists. econstructor...
  - destruct IHtwt as [| [t' ?]];[
    | right;eexists; econstructor]...
    inv H. 1,2: inv twt.
    inv H0; right; eexists; econstructor...
  - destruct IHtwt as [| [t' ?]];[
    | right; eexists; econstructor]...
    inv H. 1,2: inv twt.
    inv H0; right; eexists; econstructor...
Qed.

Theorem Preservation : forall t t' T
    (thtT : t ;; T)
    (Ex: t --> t'),
  t' ;; T.
Proof with eauto with bntDB.
  intros * ? ?. revert dependent T.
  induction Ex; intros; inv thtT...
  all: try econstructor...
  inv tt...
Qed.

Goal (* Preservation redux *) forall t T
    (thtT : t ;; T) t'
    (Ex: t --> t'),
  t' ;; T.
Proof with eauto with bntDB.
  induction 1; try solve [inversion 1].
  - inversion 1; subst...
  - inversion 1; subst.
    econstructor. apply IHthtT...
  - inversion 1; subst; [
    | inv thtT
    | econstructor; apply IHthtT ]...
  - inversion 1; subst...
Qed.

