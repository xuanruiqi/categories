From mathcomp Require Import all_ssreflect all_algebra.
Require Import classical category functor natural.

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section type.
  Definition type_CatMixin := @CatMixin Type (fun S T => S -> T) (fun _ _ _ f g => g \o f)
                                        (ltac: (by []))
                                        (fun T => @idfun T)
                                        (ltac: (by []))
                                        (ltac: (by [])).
  Definition type_Category := Eval hnf in Category Type type_CatMixin.
  Canonical type_Category.
End type.

Section category_category.
  Definition category_Category := Eval hnf in Category category (@CatMixin category (fun C D => C ~~> D) fcomp fcomp_assoc (fun C => @Id C) fcomp_id_left fcomp_id_right).
  Canonical category_Category.
End category_category.

Section functor_category.
  Variables (C D : category).

  Check (@CatMixin (C ~~> D) (fun F G => F ==> G) (fun F G H N M => M \VO N)). 
End functor_category.
