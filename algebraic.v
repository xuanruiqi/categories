From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical funlib category functor.

Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section rings.
Open Scope ring_scope.

Fact rmorphism_comp_assoc (R S T U : ringType) (f : {rmorphism R -> S}) (g : {rmorphism S -> T}) (h : {rmorphism T -> U}) : [rmorphism of [rmorphism of h \o g] \o f] = 
  [rmorphism of h \o [rmorphism of g \o f]].
Proof.
  move: f g h => [f ?] [g ?] [h ?] //=.
  congr (GRing.RMorphism.Pack _ (GRing.RMorphism.Class _ _)); apply: Prop_irrelevance.
Qed.

Fact rmorphism_id_left (R S : ringType) (f : {rmorphism R -> S}) :
  [rmorphism of f \o [rmorphism of idfun]] = f.
Proof.
  move: f => [f H] //=. 
  congr (GRing.RMorphism.Pack _ _); apply: Prop_irrelevance.
Qed.

Fact rmorphism_id_right (R S : ringType) (f : {rmorphism R -> S}) :
  [rmorphism of [rmorphism of idfun] \o f] = f.
Proof.
  move: f => [f H] //=. 
  congr (GRing.RMorphism.Pack _ _); apply: Prop_irrelevance.
Qed.

Definition ringType_CatMixin := @CatMixin ringType (fun R S => {rmorphism R -> S})
                                          (fun _ _ _ f g => [rmorphism of g \o f])
                                          rmorphism_comp_assoc
                                          (fun R => [rmorphism of @idfun R])
                                          rmorphism_id_left
                                          rmorphism_id_right.
Definition comRingType_CatMixin := @CatMixin comRingType (fun R S => {rmorphism R -> S})
                                          (fun _ _ _ f g => [rmorphism of g \o f])
                                          rmorphism_comp_assoc
                                          (fun R => [rmorphism of @idfun R])
                                          rmorphism_id_left
                                          rmorphism_id_right.

Definition ringType_Category := Eval hnf in Category ringType ringType_CatMixin.
Definition comRingType_Category := Eval hnf in Category comRingType comRingType_CatMixin.
Canonical ringType_Category.
Canonical comRingType_Category.
End rings.

Notation Ring := ringType_Category.
Notation CRing := comRingType_Category.
