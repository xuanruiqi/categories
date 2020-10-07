From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical funlib category functor.

Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* A category with products *)
Module ProdCategory.
  Structure mixin_of (C : category) : Type := Mixin {
    prod : C -> C -> C ;
    proj1 : forall {X1 X2 : C}, prod X1 X2 ~> X1 ;
    proj2 : forall {X1 X2 : C}, prod X1 X2 ~> X2 ;
    (* the universal property of products *)
    _ : forall (X1 X2 Y : C) (f1 : Y ~> X1) (f2 : Y ~> X2),
        exists! (f : Y ~> prod X1 X2), proj1 \\o f = f1 /\ proj2 \\o f = f2
  }.

  Section ClassDef.    
    Record class_of (obj : Type) : Type := Class {
      base : Category.class_of obj ;
      mixin : mixin_of (Category.Pack base)
    }.

    Record type : Type := Pack { obj ; class : class_of obj }.
    Definition category (C : type) := Category.Pack (base (class C)).
  End ClassDef.

  Module Exports.    
    Coercion base : class_of >-> Category.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion obj : type >-> Sortclass.    
    Coercion category : type >-> Category.type.
    Canonical category.

    Notation prodCategory := type.
    Notation ProdCatMixin := Mixin.
    Notation ProdCategory T m := (@Pack T (@Class _ _ m)).
    
    Definition Prod (C : type) : C -> C -> C :=
      let: Pack _ (Class _ (Mixin prod _ _ _)) := C in prod.

    Notation "A * B" := (Prod A B) : category_scope.
  End Exports.
End ProdCategory.
Import ProdCategory.Exports.

(* The category Type has products, which is just the type-theoretic product *)
Section type_prod.
Lemma type_prod_universal (T1 T2 S : Type) (f1 : S -> T1) (f2 : S -> T2) :
  exists! f : S -> (T1 * T2), fst \o f = f1 /\ snd \o f = f2.
Proof.
  exists (fun x => (f1 x, f2 x)). rewrite /unique; split => //=.
  move=> f [<- <-]. apply: functional_extensionality => x //=.
  by move: (f x) => [].
Qed.

Definition type_ProdCatMixin := ProdCatMixin type_prod_universal.
Definition type_ProdCategory := ProdCategory Type type_ProdCatMixin.
Canonical type_ProdCategory.
End type_prod.

Export ProdCategory.Exports.
