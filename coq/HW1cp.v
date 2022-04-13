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

Definition normal_form t := forall t', ~ t --> t'.

Definition stuck t := normal_form t /\ ~ val t.