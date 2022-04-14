Ltac inv H := inversion H; subst; clear H.
Create HintDb bnDB.
Require Import Lia.

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

Inductive nval : tm -> Prop :=
  | zeroisnval : nval O
  | succisnval : forall n, nval n -> nval (S n).
Inductive val : tm -> Prop :=
  | tisval : val true
  | fisval : val false
  | nvsareval : forall n, nval n -> val n.
#[export] Hint Resolve zeroisnval succisnval
tisval fisval nvsareval : bnDB.

(* Tolmach *)
Lemma nval_dec : forall tm, {nval tm} + {~ nval tm}.
Proof. (* Tolmach *)
  intros.
  induction tm0; try (right; intro H; inv H; fail).  
  - left; constructor.
  - destruct IHtm0. 
    + left; constructor; auto.
    + right.  intro. apply n. inv H.  auto.
Qed.

Lemma val_dec : forall t, {val t} + {~ val t}.
Proof with auto with bnDB.
  induction t; try solve
  [ left; auto with bnDB
  | right; intros X; inv X; inv H ].
  - destruct IHt as [V|V];
    [ | right; intros X; inv X; inv H; apply V]...
    destruct (nval_dec t) as [N|N];
    [ left
    | right; intros X; inv X; inv H]...
Qed.

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
eiftrue eiffalse: bnDB.

Inductive leap : tm -> tm -> Prop := (* for big step, ha ha. *)
  | bvalue : forall v, val v -> leap v v
  | biftrue : forall t1 t2 t3 v2
        (IH1: leap t1 true)
        (IH2: leap t2 v2),
      leap (if t1 then t2 else t3) v2
  | biffalse : forall t1 t2 t3 v3
        (IH1: leap t1 false)
        (IH2: leap t3 v3),
      leap (if t1 then t2 else t3) v3
  | bsucc : forall t v
        (IH1: nval v)
        (IH2: leap t v),
      leap (S t) (S v)
  | bpredzero : forall t
        (IH: leap t O),
      leap (P t) O
  | bpredsucc : forall t v
        (IH1: nval v)
        (IH2: leap t (S v)),
      leap (P t) v
  | biszerozero : forall t
        (IH: leap t O),
      leap (IZ t) true
  | biszerosucc : forall t v
        (IH1: nval v)
        (IH2: leap t (S v)),
      leap (IZ t) false
  .

Notation "a || b" := (leap a b).
#[export] Hint Resolve bvalue: bnDB.

Ltac bntriv :=
  try match goal with
  | H: O --> ?x |- _ => inv H
  | H: true --> ?x |- _ => inv H
  | H: false --> ?x |- _ => inv H
  | H: (S ?x) --> ?y |- _ => inv H; bntriv
  | H: nval (S ?x) |- _ => inv H; bntriv
  | H: nval (P ?x) |- _ => inv H
  | H: nval (IZ ?x) |- _ => inv H
  | H: nval true |- _ => inv H
  | H: nval false |- _ => inv H
  | H: nval (if ?x then ?y else ?z) |- _ => inv H
  | H: val (if ?x then ?y else ?z) |- _ => inv H; bntriv
  end.

Definition normal_form t := forall t', ~ t --> t'.

Definition stuck t := normal_form t /\ ~ val t.

Fixpoint size t : nat :=
  match t with
  | true | false | O => 1
  | ITE t1 t2 t3 => 1 + size t1 + size t2 + size t3
  | S t | P t | IZ t => 1 + size t
  end.

Corollary val_LEM : forall t, val t \/ ~ val t.
Proof with auto with bnDB; bntriv.
  induction t.
  - left... - left... - right; intro...
  - left...
  - destruct IHt.
    + inversion H... all: right; inversion 1...
    + right; inversion 1; subst. inv H1.
      apply H. constructor 3...
  - right. inversion 1. inv H0.
  - right. inversion 1. inv H0.
Qed.


Corollary nf__val_or_stuck : forall t,
  normal_form t -> val t \/ stuck t.
Proof with auto.
  unfold stuck. intros.
  destruct (val_LEM t);
  [ left
  | right ]...  
Qed.

Corollary val__not_stuck : forall t, val t -> ~ stuck t.
Proof ltac:(intros ** []; auto).

Lemma star_star_star : forall t1 t2 t3,
    t1 -->* t2 ->
    t2 -->* t3 ->
  t1 -->* t3.
Proof with auto.
  induction 1...
  intros. eright;
  [ exact H
  | exact (IHstepstar H1)].
Qed.

Lemma val__nf : forall t
    (valt: val t),
  normal_form t.
Proof with eauto with bnDB; bntriv.
  induction t; intros ** ? ?;
  try solve [inv valt; inv H0]...

  inv valt. inv H. edestruct IHt...
Qed.

(* 3.5.14 *)
Lemma step_deterministic : forall t t' t'',
    t --> t' ->
    t --> t'' ->
  t' = t''.
Proof with eauto with bnDB; bntriv.
  induction t; try solve [inversion 1]; intros.
  - inv H; inv H0...
    rewrite (IHt1 _ _ IH IH0)...
  - inv H; inv H0. rewrite (IHt _ _ IH IH0)...
  - inv H; inv H0...
    + edestruct (val__nf t')...
    + edestruct (val__nf t'')...
    + rewrite (IHt _ _ IH IH0)...
  - inv H; inv H0...
    + edestruct (val__nf n)...
    + edestruct (val__nf n)...
    + rewrite (IHt _ _ IH IH0)...
Qed.

Corollary normal_forms_unique : forall t u v
    (nfu: normal_form u)
    (nfv: normal_form v)
    (Exu: t -->* u)
    (Exv: t -->* v),
  u = v.
Proof with eauto with bnDB; bntriv.
  induction 3; destruct 1...
  - destruct (nfu t2)...
  - destruct (nfv t2)...
  - rewrite (step_deterministic _ _ _ H H0) in *.
    rewrite IHExu...
Qed.


Lemma step_leap__leap : forall t t' v
    (Ex1: t --> t')
    (Lp1: t' || v),
  t || v.
Proof with eauto with bnDB; bntriv.
  induction t; try solve [inversion 1]; intros.
  - inv Ex1.
    + constructor...
    + constructor 3...
    + inv Lp1...
      * constructor...
      * constructor 3...
  - inv Ex1. inv Lp1;
    [|constructor]...
    assert (nval t'0). { inv H; inv H0... }
    pose proof (nvsareval _ H0).
    constructor...
  - inv Ex1.
    + inv Lp1. constructor...
    + assert (nval v). { inv Lp1... }
      constructor... constructor...
    + inv Lp1.
      * inv H...
      * constructor. eapply IHt...
      * constructor...
  - inv Ex1.
    * inv Lp1. do 2 constructor...
    * inv Lp1. econstructor 8...
    * inv Lp1;
      [ inv H
      | constructor
      | econstructor]...
Qed.

Lemma step_irrefl: forall t, ~ t --> t.
Proof with auto.
  induction t; inversion 1; subst...
  - apply IHt2. rewrite H0...
  - apply IHt3. rewrite H0...
  - inv IH.
Qed.

Lemma step__uneq : forall t t',
  t --> t' -> t <> t'.
Proof.
  intros ** <-. eapply step_irrefl; eauto.
Qed.
  

Lemma bobo: forall t t', t -->* t' ->
  t = t' \/
  exists t2, t -->* t2 /\ t2 --> t'.
Proof with eauto.
  induction 1; subst; [left|right]...
  destruct IHstepstar as [->|].
  - exists t1;split;[left|]...
  - destruct H1 as [t []].
    exists t;split...
    eright...
Qed.


Lemma stepstar_trans_ind : forall (Q : tm -> tm -> Prop)
    (C_refl: forall t, Q t t)
    (C_star_star_star: forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> Q t1 t2 -> Q t1 t3)   t t',
  t -->* t' -> Q t t'.
Proof with eauto.
  intros. induction H...
  apply (C_star_star_star t1 t2 t3)...
  - eright;[|left]...
  - apply (C_star_star_star t1 t1 t2)...
    + left. + eright;[|left]...
Qed.


Lemma stepstar_trans_ind' : forall (Q : tm -> tm -> Prop)
    (C_refl: forall t, Q t t)
    (C_star_star_star: forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 ->  Q t2 t3 -> Q t1 t3)   t t',
  t -->* t' -> Q t t'.
Proof with eauto.
  intros. induction H...
  apply (C_star_star_star t1 t2 t3)...
  - eright;[|left]...
Qed.


Lemma stepstar_rev_ind : forall (Q : tm -> tm -> Prop)
    (C_refl: forall t, Q t t)
    (C_star_one_star: forall t1 t2 t3, t1 -->* t2 -> t2 --> t3 -> Q t1 t2 -> Q t1 t3)   t t',
  t -->* t' -> Q t t'.
Proof with eauto.
Admitted.


Lemma stepstar_leap__leap :
    forall t t' v
    (Ex1: t -->* t')
    (Lp1: t' || v),
  t || v.
Proof with eauto.
  intros * ?.
  pose proof (stepstar_rev_ind
    (fun t t' => t' || v -> t || v)).
  simpl in H. apply H...

  - intros. apply H2.
  eapply step_leap__leap...
Qed.

(* 578 HOMEWORK -- auxillary material*)
Lemma if_evals_test : forall  t t' t2 t3,
    t -->* t' ->
  (if t then t2 else t3) -->* (if t' then t2 else t3).
Proof with eauto with bnDB; bntriv.
  induction 1...
  eright;[|exact IHstepstar].
  econstructor...
Qed.

Lemma succ_evals_arg : forall t t',
    t -->* t' ->
  (S t) -->* (S t').
Proof with auto with bnDB.
  induction 1...
  eright;[|exact IHstepstar].
  constructor...
Qed.

Lemma pred_evals_arg : forall t t',
    t -->* t' ->
  (P t) -->* (P t').
Proof with auto with bnDB.
  induction 1...
  eright;[|exact IHstepstar].
  constructor...
Qed.

Lemma pred_evals_arg_to_0 : forall t,
    t -->* O ->
  (P t) -->* O.
Proof with auto with bnDB.
  intros.
  pose proof (pred_evals_arg _ _ H).
  eapply (star_star_star _ _ _ H0).
  eright;[|left]. constructor.
Qed.

Lemma pred_evals_arg_to_succ : forall t n,
    nval n ->
    t -->* (S n) ->
  (P t) -->* n.
Proof with auto with bnDB.
  intros.
  pose proof (pred_evals_arg _ _ H0).
  eapply (star_star_star _ _ _ H1).
  eright;[constructor|left]...
Qed.

Lemma IZ_evals_arg : forall t t',
    t -->* t' ->
  (IZ t) -->* (IZ t').
Proof with auto with bnDB.
  induction 1...
  eright;[|exact IHstepstar].
  constructor...
Qed.

Lemma IZ_evals_arg_to_0 : forall t,
    t -->* O ->
  (IZ t) -->* true.
Proof with auto with bnDB.
  intros. apply IZ_evals_arg in H.
  eapply star_star_star;[exact H|].
  eright;[|left]. constructor.
Qed.

Lemma IZ_evals_arg_to_succ : forall t n,
    nval n ->
    t -->* (S n) ->
  (IZ t) -->* false.
Proof with auto with bnDB.
  intros. apply IZ_evals_arg in H0.
  eapply star_star_star;[exact H0|].
  eright;[|left]. constructor...
Qed.

(* 578 HOMEWORK -- auxillary material*)
(* 3.5.17 *)
Lemma small_big_coincide : forall t v
    (valv: val v),
  t -->* v <-> t || v.
Proof with eauto with bnDB; bntriv.
  split.
  - induction 1... eapply step_leap__leap...
  - induction 1...
    + eapply (star_star_star _ (if true then t2 else t3));
      [ apply if_evals_test
      | eright;[|apply IHleap2]]...
    + eapply (star_star_star _ (if false then t2 else t3));
      [ apply if_evals_test
      | eright;[|apply IHleap2]]...
    + apply succ_evals_arg, IHleap...
    + apply pred_evals_arg_to_0...
    + apply pred_evals_arg_to_succ...
    + apply IZ_evals_arg_to_0...
    + eapply IZ_evals_arg_to_succ...
Qed.


(* 3.5.12 *)
Lemma step_terminates : forall t, exists t',
  normal_form t' /\ t -->* t'.
Proof with eauto with bnDB; bntriv.
  induction t.
  - exists true. split;[apply val__nf|left]...
  - exists false. split;[apply val__nf|left]...
  - destruct IHt1 as [nf [NFnf Ext1]].
    apply nf__val_or_stuck in NFnf. destruct NFnf.
    + inv H.
      * destruct IHt2 as [v []].
        exists v; split...
        eapply star_star_star;
        [ eapply if_evals_test, Ext1
        | eright; [constructor|]]...
      * destruct IHt3 as [v []].
        exists v; split...
        eapply star_star_star;
        [ eapply if_evals_test, Ext1
        | eright; [constructor|]]...
      * exists (if nf then t2 else t3). {
        split.
        - intros ? ?. inv H...
          edestruct (val__nf nf)...
        - apply if_evals_test... }
    + exists (if nf then t2 else t3).
        split. 
        * intros ? ?. inv H0...
          all: try destruct H...
          eapply H...
        * apply if_evals_test...
  - exists O; split... intro. inversion 1.
  - destruct IHt as [nf [NFnf]].
    exists (S nf). split;
    [ intro; inversion 1; subst; eapply NFnf
    | apply succ_evals_arg]...
  - destruct IHt as [nf [NFnf]],
      (nf__val_or_stuck _ NFnf).
    + inv H0.
      * exists (P true); split.
        intro. inversion 1...
        eapply pred_evals_arg...
      * exists (P false); split.
        intro. inversion 1...
        eapply pred_evals_arg... *{ inv H1.
      * exists O;split...
        eapply pred_evals_arg_to_0...
      * exists n;split.
        - intros ? ?. eapply NFnf.
          constructor...
        - eapply pred_evals_arg_to_succ... }
    + exists (P nf); split;
      [|eapply pred_evals_arg]...
       intro. inversion 1; subst.
       * destruct H0...
       * destruct H0...
       * eapply NFnf...
  - destruct IHt as [nf [NFnf]],
      (nf__val_or_stuck _ NFnf).
    + inv H0.
      * exists (IZ true);split;
        [ intro; inversion 1
        | eapply IZ_evals_arg]...
      * exists (IZ false);split;
        [ intro; inversion 1
        | eapply IZ_evals_arg]... *{ inv H1.
      * exists true; split;
        [ intros ? ?
        | eapply IZ_evals_arg_to_0]...
      * exists false; split;
        [ intros ? ?
        | eapply IZ_evals_arg_to_succ]... }
    + exists (IZ nf); (split;[|eapply IZ_evals_arg])...
      intros ?; inversion 1; subst.
      3:{ eapply NFnf... }
      all: destruct H0...
Qed.

(* Tolmach *)
(* Lemma A.8 *) 
Lemma if_v : forall t1 t2 t3 v
    (valv: val v),
    (if t1 then t2 else t3) -->* v  ->
    (t1 -->* true /\ t2 -->* v)
    \/ (t1 -->* false /\ t3 -->* v). 
Proof.
  intros t1 t2 t3 v valv. 
  remember (if t1 then t2 else t3) as t. 
  intro.
  generalize dependent t1. 
  induction H; intros. 
  - rewrite Heqt in valv. inv valv. inv H. 
  - rewrite Heqt in H.  inv H. 
    + left. split. constructor. auto.
    + right. split. constructor.  auto.
    + destruct (IHstepstar valv t' eq_refl) as [[P1 P2]| [P1 P2]]. 
      * left. split; auto.
        econstructor; eauto.
      * right. split; auto.
        econstructor; eauto.
Qed.

(* Tolmach *)
Lemma S_v: forall t v
          (valv: val v),
    (S t) -->* v ->
    exists nv, nval nv /\ t -->* nv /\ v = S nv. 
Proof.
  intros t v valv. 
  remember (S t) as t0. 
  intros. 
  generalize dependent t.
  induction H; intros. 
  - rewrite Heqt0 in valv. inv valv. inv H. 
    exists t0. split; auto. split. constructor. auto.
  - rewrite Heqt0 in H.  inv H. 
    destruct (IHstepstar valv t' eq_refl) as [nv [P1 [P2 P3]]].
    exists nv; intuition auto.
    econstructor; eauto.
Qed. 

(* Tolmach *)
Lemma P_v: forall t v
          (valv: val v),                   
    (P t) -->* v ->
    exists nv, nval nv /\ t -->* nv /\ ((nv = O /\ v = O) \/ S v = nv).
Proof.
  intros t v valv. 
  remember (P t) as t0. 
  intros.
  generalize dependent t. 
  induction H; intros. 
  - rewrite Heqt0 in valv.  inv valv. inv H. 
  - rewrite Heqt0 in H. inv H. 
    + exists O. split.  constructor.  split.  constructor. left.  split. auto.
      inv H0. auto. inv H. 
    + exists (S t2). split. constructor; auto. split. constructor. right.
      inv H0. auto. exfalso. eapply val__nf.  apply nvsareval; eauto. eauto.
    + destruct (IHstepstar valv t' eq_refl) as [nv [P1 [P2 P3]]]. 
      exists nv. split.  auto. split. econstructor; eauto.  auto.
Qed.

(* Tolmach *)
Lemma IZ_v: forall t v
            (valv: val v),
    (IZ t) -->* v ->
    exists nv, nval nv /\ t -->* nv /\ ((nv = O /\ v = true) \/ (exists nv', nv = S nv' /\ v = false)). 
Proof.
  intros t v valv. 
  remember (IZ t) as t0.
  intros.
  generalize dependent t. 
  induction H; intros. 
  - rewrite Heqt0 in valv. inv valv. inv H. 
  - rewrite Heqt0 in H. inv H. 
    + exists O.  split.  constructor. split. constructor.  left.  split.  auto.
      inv H0.  auto.  inv H. 
    + exists (S n).  split.  constructor; auto.
      split. constructor.
      right. exists n.  split.  auto.
      inv H0. auto. inv H. 
    + destruct (IHstepstar valv t' eq_refl) as [nv [P1 [P2 P3]]].
      exists nv.  split. auto. split. econstructor; eauto. auto.
Qed.











Lemma nfs_of_all_sizes : forall n, exists t,
  normal_form t /\ size t = Datatypes.S n.
Proof with eauto with bnDB.
  assert (sz1: exists t : tm, normal_form t /\ size t = 2). {
    exists (S O); split...
      do 2 intro. inv H. inv IH.
  }
  assert (sz1more: forall t, normal_form t ->
      exists t', normal_form t' /\ size t' = 1 + (size t)). {
    intros. exists (S t); split...
    do 2 intro. inv H0. eapply H...
  }
  induction n as [|n IH].
  - exists O; split...
    do 2 intro. inv H.
  - destruct IH as (t&NFt&szt), t;
    simpl in *; rewrite <- szt;
    try solve [destruct (sz1more _ NFt) as (?&?&?); exists x; split; auto]...
Qed.

(* 3.5.12 *)
(* Lemma normalizing : forall t, exists t',
  normal_form t' /\ t -->* t'.
Proof.

Qed. *)

Lemma step_shrink : forall t t',
  t --> t' -> size t' < size t.
Proof with try lia.
  induction 1; simpl...
Qed.

Lemma stepstar_shrink : forall t t',
  t -->* t' -> size t' <= size t.
Proof with try lia.
  induction 1 as [|? ? ? ? ? IH]; subst...
  apply step_shrink in H...
Qed.






(* Tolmach *)
Fixpoint size_tol t : nat :=
  match t with
  | true => 1
  | false => 1
  | ITE t1 t2 t3 => 1 + size t1 + size t2 + size t3 
  | O => 1
  | S t => 1 + size t 
  | P t => 1 + size t 
  | IZ t => 1 + size t
  end.

(* Tolmach *)
Lemma step_decreases_size :
  forall t t',
    t --> t' ->
    size t' < size t. 
Proof.
  induction 1; simpl; lia.
Qed.