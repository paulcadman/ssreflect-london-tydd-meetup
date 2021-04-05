From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A bit of logic to master your SSReflect skills :) *)

Section Logic.

Variables P Q R : Prop.

Lemma or_and_distr :
  (P \/ Q) /\ R -> P /\ R \/ Q /\ R.
Proof.
  by move=> [ [p | q] r ]; [left | right].
Qed.

Lemma contraposition :
  (P -> ~ Q) -> (Q -> ~ P).
Proof.
  move=> p_not_q ? ?.
  by apply: p_not_q.
Qed.

Lemma p_is_not_equal_not_p :
  ~ (P <-> ~ P).
Proof.
  case=> p_imp_not_p not_p_imp_p.
  assert P.
  - apply: not_p_imp_p.
    move=> ?.
    by apply: p_imp_not_p.
  - exact: (p_imp_not_p _).
Qed.

Lemma weak_Peirce :
  ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  move=> h1.
  apply (h1).
  move=> h2.
  apply (h2).
  move=> p.
  apply h1.
  move=> _.
  exact: p.
Qed.

Lemma curry_dep A (S : A -> Prop) :
  ((exists x, S x) -> Q) -> (forall x, S x -> Q).
Proof.
  move=> h1 x ?.
  apply: h1.
  by exists x.
Qed.

Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Lemma lem_implies_Frobenius2 : LEM -> Frobenius2.
Proof.
  compute.
  move=> lem A P0 Q0.
  split; move=> H0; case (lem Q0).
  - move=> q0; by left.
  - move=> not_q0; right; move=> x; specialize (H0 x); by elim: H0.
  - move=> q0; by left.
  - move=> not_q0; move=> x; elim H0.
    + by move=> ?.
    + move=> H1; specialize (H1 x); by right.
Qed.

Lemma Frobenius2_lem : Frobenius2 -> LEM.
Proof.
  compute.
  move=> H P0.
  specialize (H P0 (fun _ => False) P0).
  case: H.
  move=> H0 _.
  apply: H0.
  move=> p0; by left.
Qed.

End Logic.
