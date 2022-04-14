Require Import Arith.Arith.
Require Import Bool.Bool.
Require Export Coq.Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Require Import Relations String.
Import ListNotations.

Module Maps.
  Definition eqb_string (x y : string) : bool :=
    if string_dec x y then true else false.

  Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
  Proof.
    intros s. unfold eqb_string.
    destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
    - reflexivity.
    - destruct Hs_not_eq. reflexivity.
  Qed.

  Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
  Proof.
    intros x y.
    unfold eqb_string.
    destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
    - rewrite Hs_eq. split. reflexivity. reflexivity.
    - split.
      + intros contra. discriminate contra.
      + intros H. exfalso. apply Hs_not_eq. apply H.
  Qed.

  Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
  Proof.
    intros x y. rewrite <- eqb_string_true_iff.
    rewrite not_true_iff_false. reflexivity. Qed.

  (** This corollary follows just by rewriting: *)

  Theorem false_eqb_string : forall x y : string,
    x <> y -> eqb_string x y = false.
  Proof.
    intros x y. rewrite eqb_string_false_iff.
    intros H. apply H. Qed.
  
  Definition total_map (A : Type) := string -> A.

  Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

  Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

  Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

  Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v at next level, right associativity).

  Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
  Proof ltac:(reflexivity).

  Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
  Proof.
    intros. unfold t_update.
    rewrite <- eqb_string_refl; auto.
  Qed.

  Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
  Proof with auto.
    intros **. unfold t_update.
    rewrite false_eqb_string...
  Qed.

  Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    intros. unfold t_update.
    extensionality y.
    destruct (eqb_string x y); auto.
  Qed.

  Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
  Proof with auto.
    intros. destruct (eqb_string x y) eqn:X;
    constructor;
    [ apply eqb_string_true_iff
    | apply eqb_string_false_iff ]...
  Qed.

  Theorem t_update_same : forall (A : Type)
      (m : total_map A) x,
    (x !-> m x ; m) = m.
  Proof.
    intros. unfold t_update. extensionality y.
    destruct (eqb_stringP x y) as [<- |]; auto.
  Qed.

  Theorem t_update_permute : forall (A : Type)
      (m : total_map A) v1 v2 x1 x2,
      x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
  Proof with auto.
    intros. unfold t_update. extensionality y.
    destruct (eqb_stringP x1 y) as [<-|];
    [rewrite false_eqb_string|]...
  Qed.

  Definition partial_map (A : Type) := total_map (option A).

  Definition empty {A : Type} : partial_map A :=
    t_empty None.

  Definition update {A : Type} (m : partial_map A)
            (x : string) (v : A) :=
    (x !-> Some v ; m).

  (** We introduce a similar notation for partial maps: *)
  Notation "x '|->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity).

  (** We can also hide the last case when it is empty. *)
  Notation "x '|->' v" := (update empty x v)
    (at level 100).

  Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
  Proof.
    intros. unfold empty. rewrite t_apply_empty.
    reflexivity.
  Qed.

  Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
  Proof.
    intros. unfold update. rewrite t_update_eq.
    reflexivity.
  Qed.

  Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
  Proof.
    intros A m x1 x2 v H.
    unfold update. rewrite t_update_neq. reflexivity.
    apply H. Qed.

  Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
  Proof.
    intros A m x v1 v2. unfold update. rewrite t_update_shadow.
    reflexivity.
  Qed.

  Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
  Proof.
    intros A m x v H. unfold update. rewrite <- H.
    apply t_update_same.
  Qed.

  Theorem update_permute : forall (A : Type) (m : partial_map A)
                                  x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
  Proof.
    intros A m x1 x2 v1 v2. unfold update.
    apply t_update_permute.
  Qed.

  Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

  (** We then show that map update preserves map inclusion, that is: *)

  Lemma inclusion_update : forall (A : Type) (m m' : partial_map A)
                                  (x : string) (vx : A),
    inclusion m m' ->
    inclusion (x |-> vx ; m) (x |-> vx ; m').
  Proof.
    unfold inclusion.
    intros A m m' x vx H.
    intros y vy.
    destruct (eqb_stringP x y) as [Hxy | Hxy].
    - rewrite Hxy.
      rewrite update_eq. rewrite update_eq. intro H1. apply H1.
    - rewrite update_neq. rewrite update_neq.
      + apply H.
      + apply Hxy.
      + apply Hxy.
  Qed.

  Corollary inclusion_empty :
      forall (X: Type) (m: partial_map X),
    inclusion empty m.
  Proof ltac:(inversion 1).

  Hint Resolve inclusion_empty : core.

End    Maps.

Import Maps.
Ltac inv H := inversion H; subst; clear H.
Create HintDb stlcabDB.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

(** Now we need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

(* Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core. *)

(** Some examples... *)

(* Notation idB :=
  <{\x:Bool, x}>.

Notation idBB :=
  <{\x:Bool->Bool, x}>.

Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.

Notation k := <{\x:Bool, \y:Bool, x}>.

Notation notB := <{\x:Bool, if x then false else true}>. *)

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


Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if eqb_string x y then s else t
  | <{\y:T, t1}> =>
      if eqb_string x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
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
    T, Gamma)] for "update the partial function [Gamma] so that it
    maps [x] to [T]." *)

Definition context := partial_map ty.

(* ================================================================= *)
(** ** Typing Relation *)


Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall G x T1
      (IH: G x = Some T1),
      G |- x \in T1
  | T_Abs : forall G x T1 T2 t1
      (IH: x |-> T2 ; G |- t1 \in T1),
      G |- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 G t1 t2
      (IH1: G |- t1 \in (T2 -> T1))
      (IH2: G |- t2 \in T2),
      G |- t1 t2 \in T1
  | T_True : forall G,
       G |- true \in Bool
  | T_False : forall G,
       G |- false \in Bool
  | T_If : forall t1 t2 t3 T1 G
       (IH1: G |- t1 \in Bool)
       (IH2: G |- t2 \in T1)
       (IH3: G |- t3 \in T1),
       G |- if t1 then t2 else t3 \in T1

where "G '|-' t '\in' T" := (has_type G t T).

Hint Constructors has_type : core.

Theorem t__unique_typ : forall t G T T'
    (tT: G |- t \in T) (tT': G |- t \in T'),
  T = T'.
Proof with eauto.
  induction t; intros.
  all: inv tT; inv tT'...
  - rewrite IH0 in IH. injection IH...
  - rewrite (IHt2 _ _ _ IH3 IH2) in IH0.
    pose proof (IHt1 _ _ _ IH1 IH0). inv H...
  - rewrite (IHt _ _ _ IH IH0)...
Qed.

Theorem v_val_Bool__tof : forall v G
    (valv: value v)
    (vBool: G |- v \in Bool),
  v = <{true}> \/ v = <{false}>.
Proof with eauto.
  intros. inv valv...
  inv vBool.
Qed.



(* Theorem value__closed : forall v G T
    (valv: value v)
    (vT: G |- v \in T),
  empty |- v \in T.
Proof with eauto.
  induction 2;
  try solve [inv valv]...

  econstructor. clear - vT.
  inv vT...
  + econstructor. erewrite <- update_shadow ...
  update_shadow
  inv vT.
  - inv valv.
  -
Qed. *)

Theorem progress : forall t T
    (twt: empty |- t \in T),
  value t \/ exists t', t --> t'.
Proof with eauto.
  remember empty as G.
  induction 1...
  - rewrite HeqG in IH. inv IH.
  - rename IHtwt1 into IH1, IHtwt2 into IH2.
    specialize (IH1 HeqG). specialize (IH2 HeqG).
    right. destruct IH1; [destruct IH2 |].
    + inv H; [ eexists; econstructor| |]...
      all: inv twt1.
    + destruct H0. eexists; eapply ST_App2...
    + destruct H.  eexists; eapply ST_App1...
  - rename IHtwt1 into IH1, IHtwt2 into IH2,
           IHtwt3 into IH3. specialize (IH1 HeqG).
    specialize (IH2 HeqG). specialize (IH3 HeqG).
    right. destruct IH1;
    [ inv H; [inv twt1| |]
    | destruct H]; eexists; econstructor ...
Qed.

Lemma weakening : forall G G' t T
    (INCL: inclusion G G')
    (H: G |- t \in T),
  G' |- t \in T.
Proof with eauto.
  intros **. generalize dependent G'.
  induction H;
  try solve [econstructor; try apply INCL; auto];
  intros.

  econstructor. eapply IHhas_type. intros ? **.
  destruct (eqb_stringP x x0) as [<-|].
  - now rewrite update_eq in *.
  - rewrite update_neq in *...
Qed.

Lemma weakening_empty : forall G t T,
    empty |- t \in T  ->
  G |- t \in T.
Proof with auto.
  intros. eapply weakening...
Qed.

Lemma substitution_preserves_typing : forall G x U t v T,
    x |-> U ; G |- t \in T ->
    empty |- v \in U ->
  G |- [x:=v]t \in T.
Proof with eauto.
  intros *; revert G x U v T.
  induction t; intros **; simpl; inv H...
  - destruct (eqb_stringP x s) as [<-|].
    + rewrite update_eq in IH.
      injection IH as ->.
      apply weakening_empty...
    + econstructor. rewrite update_neq in IH...
  - destruct (eqb_stringP x s) as [<-|]; econstructor.
    + rewrite update_shadow in IH...
    + eapply IHt... rewrite update_permute...
Qed.


Ltac niceIH :=
  try rename IHhas_type into IH;
  try rename IHhas_type1 into IH1;
  try rename IHhas_type2 into IH2;
  try rename IHhas_type3 into IH3.
(* Goal forall G x U t v T,
    x |-> U ; G |- t \in T ->
    empty |- v \in U ->
  G |- [x:=v]t \in T.
Proof with eauto.
  intros.
  remember (x |-> U; G) as G'.
  revert dependent v. revert dependent G.
  revert x U.
  induction H... all: intros * -> **;
  try rename IHhas_type into IH;
  try rename IHhas_type1 into IH1;
  try rename IHhas_type2 into IH2;
  try rename IHhas_type3 into IH3.
  - destruct (eqb_stringP x x0) as [<-|]; simpl;
    [ rewrite <- eqb_string_refl
    | rewrite false_eqb_string ]...
    + rewrite update_eq in IH.
      injection IH as <-. apply weakening_empty...
    + rewrite update_neq in IH...
  - specialize (IH _ eq_refl).

Qed. *)


Theorem preservation : forall t t' T,
    empty |- t \in T  ->
    t --> t'  ->
  empty |- t' \in T.
Proof with eauto.
  remember empty as G.
  intros * ?; revert t'. induction H; intros;
  try solve [inv H| inv H0|inv H2;eauto]; niceIH.
  inv HeqG. specialize (IH2 eq_refl).
  specialize (IH1 eq_refl).

  inv H1; try solve [econstructor;eauto].
  inv H. eapply substitution_preserves_typing...
Qed.


Theorem preservation_strong : forall t t' T G,
    G |- t \in T  ->
    t --> t'  ->
  G |- t' \in T.
Proof with eauto.
  intros * ?; revert t'. induction H; intros;
  try solve [inv H| inv H0|inv H2;eauto]; niceIH.
  

  inv H1; try solve [econstructor;eauto].
  inv H. eapply substitution_preserves_typing...
Qed.






























Require Import List Nat.
Definition ident := nat.

(* deBruijn index *)
Definition dbi := nat.

Inductive ty : Type :=
  | Bool
  | Arrow : ty -> ty -> ty.

(* Inductive binding : Type := VarBind : ty -> binding. *)
Definition context := list (ident * ty).
Definition add_binding ctx x bind : context := (x,bind)::ctx.

Fixpoint get_binding (ctx:context) i :=
  match ctx with
  | (x,T) :: tl => if Nat.eqb x i
                   then Some T
                   else get_binding tl i
  | _ => None
  end.

Definition getTypeFromContext ctx i :=
  match get_binding ctx i with
  | Some ty => ty
  | _ => Bool
  end.

Notation "x ;; T ∈ G" := (get_binding G x = Some T) (at level 1, T at next level).

Inductive tm : Type :=
  | ttrue
  | tfalse
  | ITE : tm -> tm -> tm -> tm
  | var : nat -> tm
  | abs : ident -> ty -> tm -> tm
  | app : tm -> tm -> tm.

Fixpoint size t :=
  match t with
  | ttrue | tfalse | var _ => 1
  | abs _ _ t => 1 + size t
  | app t1 t2 => 1 + size t1 + size t2
  | ITE t1 t2 t3 => 1 + size t1 + size t2 + size t3
  end.

Fixpoint binders acc t : Prop :=
  match t with
  | var k => if <
  end

Notation "'If' c 'Then' u 'Else' v" :=
  (ITE c u v)
  (at level 200).

Inductive val : tm -> Prop :=
  | vtrue : val ttrue
  | vfalse : val tfalse
  | vabs : forall x T body,
    val (abs x T body).

Inductive type_of : context -> tm -> ty -> Prop :=
  | tttrue : forall G, type_of G ttrue Bool
  | ttfalse : forall G, type_of G tfalse Bool
  | tif : forall G t1 t2 t3 T
      (t1ht: type_of G t1 Bool)
      (t2ht: type_of G t2 T)
      (t3ht: type_of G t3 T),
    type_of G (ITE t1 t2 t3) T
  | tvar : forall G x T,
      (x ;; T ∈ G) ->
    type_of G (var x) T
  | tabs : forall G x body Tx Tb
      (H: type_of (add_binding G x Tx) body Tb),
    type_of G (abs x Tx body) (Arrow Tx Tb)
  | tapp : forall G t1 t2 T2 T
      (t1ht: type_of G t1 (Arrow T2 T))
      (t2ht: type_of G t2 T2),
    type_of G (app t1 t2) T.

Notation "G |- t ;; T" := (type_of G t T) (at level 1, t at next level).

#[export] Hint Resolve vtrue vfalse vabs
tttrue ttfalse tif tvar tabs tapp : stlcabDB.

Fixpoint shift d c t :=
  match t with
  | var k => if k <? c then t else var (k + d)
  | abs x T body => abs x T (shift d (S c) body)
  | app t1 t2 => app (shift d c t1) (shift d c t2)
  | ITE t1 t2 t3 => ITE (shift d c t1) (shift d c t2) (shift d c t3)
  | _ => t
  end.

Definition dshift d t := shift d 0 t.

Fixpoint subst_by_in (j: dbi) (s t: tm) : tm :=
  match t with
  | var k => if k =? j then s else t
  | abs x T body => abs x T (subst_by_in (S j) (dshift 1 s) body)
  | app t1 t2 => app (subst_by_in j s t1) (subst_by_in j s t2)
  | ITE t1 t2 t3 => ITE (subst_by_in j s t1) (subst_by_in j s t2) (subst_by_in j s t3)
  | _ => t
  end.

Inductive step : tm -> tm -> Prop :=
  | eiftrue : forall t2 t3,
      step (If ttrue Then t2 Else t3) t2
  | eiffalse : forall t2 t3,
      step (If tfalse Then t2 Else t3) t3
  | eif : forall t t' t2 t3
        (IH: step t t'),
      step (If t Then t2 Else t3) (If t' Then t2 Else t3)
  | eapp1 : forall t t' targ
        (IH: step t t'),
      step (app t targ) (app t' targ)
  | eapp2 : forall v t t'
        (IHv: val v)
        (IH: step t t'),
      step (app v t) (app v t')
  | eappabs : forall x T body v,
      step (app (abs x T body) v) (subst_by_in 0 v body).

Notation "a --> b" := (step a b) (at level 5).

Inductive stepstar : tm -> tm -> Prop :=
  | zerosteps : forall t, stepstar t t
  | oneormoresteps : forall t1 t2 t3,
      step t1 t2 -> stepstar t2 t3 -> stepstar t1 t3.
Notation "a -->* b" := (stepstar a b) (at level 5).
#[export] Hint Resolve zerosteps
eiftrue eiffalse: stlcabDB.

Theorem t__unique_typ : forall t G T T'
  (tT: G |- t ;; T) (tT': G |- t ;; T'), T = T'.
Proof with eauto.
  induction t; intros.
  all: inv tT; inv tT'...
  - rewrite H1 in H2. injection H2...
  - rewrite (IHt _ _ _ H4 H5)...
  - rewrite (IHt2 _ _ _ t2ht t2ht0) in t1ht.
    pose proof (IHt1 _ _ _ t1ht t1ht0).
    inversion H...
Qed.

Theorem v_val_Bool__tof : forall v G
    (valv: val v)
    (vBool: G |- v ;; Bool),
  v = ttrue \/ v = tfalse.
Proof with eauto.
  intros. inv valv...
  inv vBool.
Qed.

Theorem Progress : forall G t
    (twt: exists T, G |- t ;; T),
  val t \/ exists t', t --> t'.
Proof with eauto with stlcabDB.
  intros * [T tWT].
  induction tWT...
  - admit.
  - 
Qed.

  Theorem Preservation

Definition in_ctx (x:nat) (T:typ) ctx := 
  nth_error ctx x  = Some T.

Inductive has_typ : tcontext -> tm -> typ -> Prop :=
  | 
