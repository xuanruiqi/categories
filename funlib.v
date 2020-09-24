(* A classical library of facts about functions *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section surjective.
  Definition surjective rT aT (f : aT -> rT) :=
    forall y : rT, exists x : aT, f x = y.
  Arguments surjective [rT aT] f.  
End surjective.

Section surjections_theory.
  Variables (A B C : Type) (f g : B -> A) (h : C -> B).

  Lemma sur_id : surjective (@id A).
  Proof.
    move=> y. by exists y.
  Qed.

  Lemma sur_comp : surjective f -> surjective h -> surjective (f \o h).
  Proof.
    move=> sur_f sur_h y.
    move: (@sur_f y) => [z f_z]. move: (@sur_h z) => [x f_x].
    exists x => //=. by rewrite f_x.
  Qed.    

  Lemma sur_compl : surjective (f \o h) -> surjective f.
  Proof.
    move=> sur_comp y.
    move: (@sur_comp y) => [x f_x]. by exists (h x).
  Qed.

  Lemma bij_sur : bijective f -> surjective f.
  Proof.
    move=> [f' cancel_ff' cancel_f'f] y. by exists (f' y).
  Qed.
End surjections_theory.

