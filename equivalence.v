From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp.
Require Import classical category functor natural isomorphism.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Reserved Infix "~=~" (at level 90, right associativity).

(* The equivalence of categories *)
Module Equivalence.
  Section ClassDef.
    Variables (C D : category).

    Structure mixin_of (F : C ~~> D) (G : D ~~> C) : Type := Mixin {
      _ : (G \O F) ~= Id ;
      _ : (F \O G) ~= Id
    }.
    Notation class_of := mixin_of.
   
    Structure type := Pack { F : C ~~> D ; G : D ~~> C ; _ : mixin_of F G}.
  End ClassDef.

  Module Exports.
    Notation equiv := type.
    Notation EquivMixin := Mixin.
    Notation Equiv fE := (Pack fE).
  End Exports.
End Equivalence.
Import Equivalence.Exports.
Notation "C ~=~ D" := (equiv C D) : category_scope.

Section equivalence_lemmas.
  Variables (C D : category).

End equivalence_lemmas.
