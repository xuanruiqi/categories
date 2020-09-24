From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp.
Require Import classical category functor.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Infix "==>" (at level 55, right associativity).
Reserved Infix "\VO" (at level 40, left associativity).
Reserved Notation "[ C ; D ]" (at level 49).

Module NaturalTransformation.
  Section ClassDef.
    Structure mixin_of (C D : category) (F G : C ~~> D) (eta : forall X, F X ~> G X) : Type :=
      Mixin {
        _ : forall (X Y : C) (f : X ~> Y), (eta Y) \\o (F @@ f) = (G @@ f) \\o (eta X) ; 
      }.
    Notation class_of := mixin_of.

    Structure type (C D : category) (F G : C ~~> D) :=
      Pack { component : (forall (X : C), F X ~> G X) ; _ : mixin_of component }.

    Local Coercion component : type >-> Funclass.
    Arguments type {C D} F G.

    Variables (C D : category) (F G : C ~~> D) (cN : type F G).
    Definition class := let: Pack _ c as cN' := cN return class_of cN' in c.
    Definition clone c of phant_id class c := @Pack C D F G c.
  End ClassDef.
  Notation class_of := mixin_of.

  Module Exports.
    Notation nt := type.
    Coercion component : type >-> Funclass.
    Notation NTMixin := Mixin.
    Notation NT fN := (Pack fN).
  End Exports.
End NaturalTransformation.

Import NaturalTransformation.Exports.
Arguments nt {C D} F G.
Notation "F ==> G" := (nt F G) : category_scope.

Section naturality.
  Variables (C D : category) (F G : C ~~> D) (N : F ==> G).
  
  Lemma naturality (X Y : C) (f : X ~> Y) : (N Y) \\o (F @@ f) = (G @@ f) \\o (N X).
  Proof. by case: N => [? []]. Qed.
End naturality.

Section naturality_lemmas.
  Variables (C D : category) (F G : C ~~> D).

  Lemma natural_extensional (N M : F ==> G) : N = M <-> forall X, (N X = M X :> (_ ~> _)).
  Proof.
    split => [-> //= |].
    move: N M => [cn [nat_n]] [cm [nat_m]] //= nm_eq1. move: nat_m nat_n.
    move: (functional_extensionality_dep cn cm nm_eq1) => -> nat_m nat_n.
    by move: (Prop_irrelevance nat_m nat_n) => ->.
  Qed.
End naturality_lemmas.
  
Section id_nt.
  Variables (C D : category) (F : C ~~> D).

  Definition id_component (X : C) : F X ~> F X := id.

  Definition id_component_natural (X Y : C) (f : X ~> Y) :
    (id_component Y) \\o (F @@ f) = (F @@ f) \\o (id_component X).
  Proof.
    by rewrite /id_component comp_id_left comp_id_right.
  Qed.

  Definition IdNT_NTMixin := @NTMixin C D F F id_component id_component_natural.
  Definition IdNT : F ==> F := Eval hnf in NT IdNT_NTMixin.
  Canonical IdNT.
End id_nt.
Arguments IdNT {C D F}.

Section vertical_composition.
  Variables (C D : category) (F G H : C ~~> D) (N : F ==> G) (M : G ==> H).

  Definition compose_component (X : C) : F X ~> H X :=
    M X \\o N X.

  (* Diagram chasing proof *)
  Definition compose_component_natural (X Y : C) (f : X ~> Y) :
    (compose_component Y) \\o (F @@ f) = (H @@ f) \\o (compose_component X).
  Proof.
    rewrite /compose_component //= -comp_assoc -[in RHS]naturality.
    by rewrite comp_assoc [in LHS]naturality -comp_assoc.
  Qed.

  Definition vcomp_NTMixin := @NTMixin C D F H compose_component compose_component_natural.
  Definition vcomp : F ==> H := Eval hnf in NT vcomp_NTMixin.
  Canonical vcomp.    
End vertical_composition.

Arguments vcomp {C D F G H} N M.
Notation "M \VO N" := (vcomp N M).

Section vcomp_lemmas.
  Variables (C D : category) (F G H K : C ~~> D).

  Lemma vcomp_assoc (N : F ==> G) (M : G ==> H) (Z : H ==> K) : Z \VO M \VO N = Z \VO (M \VO N).
  Proof.
    apply natural_extensional => //= X.
    by rewrite /compose_component /compose_component comp_assoc.
  Qed.

  Lemma vcomp_id_left (N : F ==> G) : N \VO IdNT = N.
  Proof.
    apply natural_extensional => //= X.
    by rewrite /compose_component /id_component comp_id_left.
  Qed.

  Lemma vcomp_id_right (N : F ==> G) : IdNT \VO N = N.
  Proof.
    apply natural_extensional => //= X.
    by rewrite /compose_component /id_component comp_id_right.
  Qed.
End vcomp_lemmas.

Section functor_category.
  Variables (C D : category).

  Definition functor_Category_mixin :=
    @CatMixin (C ~~> D)
              (fun F G => F ==> G)
              (fun F G H N M => M \VO N)
              (@vcomp_assoc C D)
              (fun F => @IdNT _ _ F)
              (@vcomp_id_left C D)
              (@vcomp_id_right C D).
  Definition functor_Category := Eval hnf in Category _ functor_Category_mixin.
  Canonical functor_Category.
End functor_category.
Notation "[ C ; D ]" := (functor_Category C D).

Export NaturalTransformation.Exports.
