From mathcomp Require Import all_ssreflect.
From mathcomp.analysis Require Import classical_sets boolp.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevanceFacts ProofIrrelevance.

Lemma funext (A B : Type) (f g : A -> B) : f =1 g -> f = g.
Proof.
  move=> H. extensionality x. apply: H.
Qed.
