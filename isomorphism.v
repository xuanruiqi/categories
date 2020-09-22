From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical category functor natural.

Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Infix "~=" (at level 90, right associativity).

Module Isomorphism.
  Section ClassDef.
    Variables (C : category).
    Definition axiom (X Y : C) (f : X ~> Y) := { g : Y ~> X & g \\o f = id /\ f \\o g = id}.
    Structure type (X Y : C) := Pack { f : X ~> Y; _ : axiom f }.
  End ClassDef.
  Arguments axiom {C X Y} f.

  Module Exports.
    Notation isomorphism f := (axiom f).
    Coercion f : type >-> hom.
    Notation iso := type.
    Notation Iso := Pack.
  End Exports.
End Isomorphism.
Import Isomorphism.Exports.
Notation "X ~= Y" := (iso X Y) : category_scope.

Section iso_lemmas.
  Variable (C : category).

  Lemma iso_id (X : C) : isomorphism (@ident C X).
  Proof.
    rewrite /(isomorphism id). exists id. by rewrite comp_id_left.
  Qed.

  Lemma iso_reflexive (X : C) : X ~= X.
  Proof.
    by apply: (Iso (@iso_id X)).
  Qed.
  
  Lemma iso_symmetric (X Y : C) : X ~= Y -> Y ~= X.
  Proof.
    move=> [f [f_inv [invl invr]]].
    apply: (@Iso _ _ _ f_inv _). by exists f.
  Qed.

  Lemma iso_transitive (X Y Z : C) : X ~= Y -> Y ~= Z -> X ~= Z.
  Proof.
    move=> [f [f_inv [f_inv_l f_inv_r]]] [g [g_inv [g_inv_l g_inv_r]]].
    apply: (@Iso _ _ _ (g \\o f) _). exists (f_inv \\o g_inv); split;
    by rewrite comp_assoc -[X in _ \\o X]comp_assoc ?g_inv_l ?f_inv_r comp_id_right.
  Qed.
End iso_lemmas.
