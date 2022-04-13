Ltac inv H := inversion H; subst; clear H.
Require Import List.
Definition ident := nat.

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

Inductive tm : Type :=
  | ttrue
  | tfalse
  | ITE : tm -> tm -> tm -> tm
  | var : nat -> tm
  | abs : ident -> ty -> tm -> tm
  | app : tm -> tm -> tm.

Notation "'if' c 'then' u 'else' v" :=
  (ITE c u v)
  (at level 200).

Inductive val : tm -> Prop :=
  | vabs : forall x T body,
    val (abs x T body).

Inductive type_of : context -> tm -> ty -> Prop :=
  | tttrue : forall ctx, type_of ctx ttrue Bool
  | ttfalse : forall ctx, type_of ctx tfalse Bool
  | tif : forall ctx t1 t2 t3 T
      (t1ht: type_of ctx t1 Bool)
      (t2ht: type_of ctx t2 T)
      (t3ht: type_of ctx t3 T),
    type_of ctx (ITE t1 t2 t3) T
  | tvar : forall ctx x,
    type_of ctx (var x) (getTypeFromContext ctx x)
  | tabs : forall ctx x body Tx Tb
      (H: type_of (add_binding ctx x Tx) body Tb),
    type_of ctx (abs x Tx body) (Arrow Tx Tb)
  | tapp : forall ctx t1 t2 T2 T
      (t1ht: type_of ctx t1 (Arrow T2 T))
      (t2ht: type_of ctx t2 T2),
    type_of ctx (app t1 t2) T.


Theorem t__unique_typ : forall t G T T'
  (tT: type_of G t T) (tT': type_of G t T'), T = T'.
Proof with eauto.
  induction t; intros.
  all: inv tT; inv tT'...
  rewrite (IHt _ _ _ H4 H5)...
  rewrite (IHt2 _ _ _ t2ht t2ht0) in t1ht.
  pose proof (IHt1 _ _ _ t1ht t1ht0).
  inversion H...
Qed.

Theorem v_val_Bool__tof : forall v G
    (valv: val v) (vBool: type_of G v Bool),
  v = ttrue \/ v = tfalse.
Proof with eauto.
  intros. inv valv...
  inv H; inv vBool.
Qed.


Definition in_ctx (x:nat) (T:typ) ctx := 
  nth_error ctx x  = Some T.

Inductive has_typ : tcontext -> tm -> typ -> Prop :=
  | 
