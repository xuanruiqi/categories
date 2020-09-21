From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp.
Require Import category classical.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Reserved Infix "~~>" (at level 90, right associativity).
Reserved Notation "F @@ f" (at level 11).
Reserved Infix "\O" (at level 40, left associativity).

Module Functor.
  Section ClassDef.    
    Structure mixin_of (C D : category) (F : C -> D) : Type := Mixin {
      fmap : forall (X Y : C) (f : X ~> Y), F X ~> F Y ;
      _ : forall (X : C), @fmap X X id = id ;
      _ : forall (X Y Z : C) (f : X ~> Y) (g : Y ~> Z), fmap (g \\o f) = fmap g \\o fmap f
    }.
    Notation class_of := mixin_of.
    
    Structure type (C D : category) := Pack { F : C -> D ; _ : class_of F }.
    Local Coercion F : type >-> Funclass.

    Variables (C D : category) (F : C -> D) (cF : type C D).

    Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
    Definition clone c of phant_id class c := @Pack C D F c.
  End ClassDef.
  Notation class_of := mixin_of.
  
  Module Exports.
    Notation functor := type.
    Coercion F : type >-> Funclass.

    Section fmap.
      Variables (C D : category) (phCD : phant (C -> D)) (F : C -> D) (cF : type C D).
      Definition FMap (F : type C D) : forall A B : C, A ~> B -> F A ~> F B :=
        let: Pack mp (Mixin f _ _) := F in f.
    End fmap.
    
    Notation FunctorMixin := Mixin.
    Notation Functor fF := (Pack fF).

    Notation "F @@ f" := (FMap F f) : category_scope.
  End Exports.
End Functor.
Import Functor.Exports.

Notation "C ~~> D" := (functor C D) : category_scope.

Section functor_lemmas.
  Variables (C D : category) (F : C ~~> D).

  Lemma fmap_id (X : C) : F @@ (@ident _ X) = id.
  Proof. by case: F => [? []]. Qed.

  Lemma fmap_comp (X Y Z : C) (f : X ~> Y) (g : Y ~> Z) :
    F @@ (g \\o f) = F @@ g \\o F @@ f.
  Proof. by case: F => [? []]. Qed.
End functor_lemmas.

Section identity_functor.
  Variable (C : category).
  
  Definition Id : C ~~> C :=
    Functor (@FunctorMixin C C idfun (fun A B => (@idfun (A ~> B))) (ltac: (by []))
                  (ltac: (by []) )).
End identity_functor.
Arguments Id {C}.

Section composition.
  Variables (C D E : category) (F : C ~~> D) (G : D ~~> E).

  Definition compose_fmap (A B : C) (f : A ~> B) := G @@ (F @@ f).

  Lemma compose_fmap_id (X : C) : G @@ (F @@ (@ident _ X)) = id.
  Proof. by rewrite !fmap_id. Qed.

  Lemma compose_fmap_comp (X Y Z : C) (f : X ~> Y) (g : Y ~> Z) :
    G @@ (F @@ (g \\o f)) = (G @@ (F @@ g)) \\o (G @@ (F @@ f)).
  Proof. by rewrite !fmap_comp. Qed.

  Definition fcomp_FunctorMixin := @FunctorMixin C E (G \o F) (fun X Y f => G @@ (F @@ f)) compose_fmap_id compose_fmap_comp.
  Definition fcomp : @functor C E := Eval hnf in Functor fcomp_FunctorMixin.
  Canonical fcomp.
End composition.

Notation "G \O F" := (fcomp F G) : category_scope.
Notation contravariant C D := (functor (C^op) D).

Section composition_laws.
  Variables (C D E M : category) (F : C ~~> D) (G : D ~~> E) (H : E ~~> M).

  Ltac functor_cstr :=
    congr (Functor.Pack (Functor.Mixin _ _)) => //=; try (apply: Prop_irrelevance).
  
  Lemma fcomp_assoc : H \O G \O F = H \O (G \O F).
  Proof.
    move: F G H => [f [???]] [g [???]] [h [???]] //=.
    functor_cstr.
  Qed.

  Lemma fcomp_id_left : F \O Id = F.
  Proof.
    move: F => [f [???]] //=; functor_cstr.
  Qed.

  Lemma fcomp_id_right : Id \O F = F.
    move: F => [f [???]] //=; functor_cstr.
  Qed.
End composition_laws.

Export Functor.Exports.
