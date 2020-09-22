From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical.

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "\\o" (at level 40, left associativity).
Reserved Notation "C '^op'" (at level 20, left associativity).

Module Category.
  Polymorphic Structure mixin_of (obj : Type) := Mixin {
    hom : obj -> obj -> Type ;
    comp : forall X Y Z, hom X Y -> hom Y Z -> hom X Z ;
    _ : forall X Y Z W (f : hom X Y) (g : hom Y Z) (h : hom Z W),
        comp f (comp g h) = comp (comp f g) h ;
    ident : forall X, hom X X ;
    _ : forall X Y (f : hom X Y), comp (ident X) f = f ;
    _ : forall X Y (f : hom X Y), comp f (ident Y) = f ;
  }.
  Notation class_of := mixin_of.

  Section ClassDef.
    Polymorphic Structure type : Type := Pack { obj ; _ : class_of obj }.
    Local Coercion obj : type >-> Sortclass.

    Variables (T : Type) (cT : type).
    Polymorphic Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
    Polymorphic Definition clone c of phant_id class c := @Pack T c.
  End ClassDef.
    
  Module Exports.
    Notation category := type.
    Coercion obj : category >-> Sortclass.
    Bind Scope category_scope with obj.

    Notation CatMixin := Mixin.
    Notation Category T m := (@Pack T m).
  End Exports.
End Category.

Import Category.Exports.
Definition hom C := Category.hom (Category.class C).
Definition comp C := @Category.comp _ (Category.class C).
Definition ident C := Category.ident (Category.class C).

Notation "U ~> V" := (hom U V) : category_scope.
Notation "g \\o f" := (comp f g) : category_scope.
Notation id := (ident _).

Section category_lemmas.
  Variable (C : category).

  Lemma comp_id_left (X Y : C) (f : X ~> Y) :
    f \\o id = f.
  Proof. by case: C X Y f => [? []]. Qed.
  
  Lemma comp_id_right (X Y : C) (f : X ~> Y) :
    id \\o f = f.
  Proof. by case: C X Y f => [? []]. Qed.
  
  Lemma comp_assoc (X Y Z W : C) (f : X ~> Y) (g : Y ~> Z) (h : Z ~> W) :
    h \\o g \\o f = h \\o (g \\o f).
  Proof. by case: C X Y Z W f g h => [? []]. Qed.    
End category_lemmas.

Section opposite.
  Variable (C : category).
  
  Definition opp_CatMixin : Category.mixin_of C.
  Proof.
    refine (@CatMixin C (fun X Y => Y ~> X) (fun _ _ _ f g => f \\o g) _
                      (fun X => id) _ _).
    move=> X Y Z W f g h //=. by rewrite comp_assoc.
    move=> X Y f. by rewrite comp_id_right.
    move=> X Y f. by rewrite comp_id_left.
  Defined.

  Definition opp := Eval hnf in Category C opp_CatMixin.
  Canonical opp.
End opposite.

Notation "C '^op' " := (opp C) : category_scope.

(* A category with products *)
Module ProdCategory.
  Structure mixin_of (CC : category) : Type := Mixin {
    prod : CC -> CC -> CC ;
    proj1 : forall {X1 X2 : CC}, prod X1 X2 ~> X1 ;
    proj2 : forall {X1 X2 : CC}, prod X1 X2 ~> X2 ;
    (* the universal property of products *)
    _ : forall (X1 X2 Y : CC) (f1 : Y ~> X1) (f2 : Y ~> X2),
        exists! (f : Y ~> prod X1 X2), proj1 \\o f = f1 /\ proj2 \\o f = f2
  }.

  Section ClassDef.    
    Record class_of (obj : Type) : Type := Class {
      base : Category.class_of obj ;
      mixin : mixin_of (Category.Pack base)
    }.

    Record type : Type := Pack { obj ; class : class_of obj }.
    Definition category (CC : type) := Category.Pack (base (class CC)).
  End ClassDef.

  Module Exports.    
    (* Definition Prod (CC : type) : CC -> CC -> CC :=
      let: Pack _ (Class _ (Mixin prod _ _ _)) := CC in prod. *)
    Coercion base : class_of >-> Category.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion obj : type >-> Sortclass.    
    Coercion category : type >-> Category.type.
    Canonical category.

    Notation prodCategory := type.
    Notation ProdCatMixin := Mixin.
    Notation ProdCategory T m := (@Pack T (@Class _ _ m)).
    
    Definition Prod (CC : type) : CC -> CC -> CC :=
      let: Pack _ (Class _ (Mixin prod _ _ _)) := CC in prod.

    Notation "A * B" := (Prod A B) : category_scope.
  End Exports.
End ProdCategory.

Export Category.Exports.
Export ProdCategory.Exports.
