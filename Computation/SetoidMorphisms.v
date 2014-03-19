Require Import Common.
Require Import Computation.Core.

(** General Lemmas about the parametric morphism behavior of
    [computes_to], [refine], and [refineEquiv]. *)

Add Parametric Relation A
: (Comp A) (@refine A)
  reflexivity proved by reflexivity
  transitivity proved by transitivity
    as refine_rel.

Add Parametric Relation A
: (Comp A) (@refineEquiv A)
  reflexivity proved by reflexivity
  symmetry proved by symmetry
  transitivity proved by transitivity
    as refineEquiv_rel.

Local Ltac t := unfold impl; intros; repeat (eapply_hyp || etransitivity).

Add Parametric Morphism A
: (@refine A)
  with signature
  (@refine A) --> (@refine A) ++> impl
    as refine_refine.
Proof. t. Qed.

Add Parametric Morphism A
: (@refine A)
  with signature
  (@refineEquiv A) --> (@refineEquiv A) ++> impl
    as refine_refineEquiv.
Proof. t. Qed.

Hint Constructors computes_to.

Add Parametric Morphism A B
: (@Bind A B)
    with signature
    (@refine A)
      ==> (pointwise_relation _ (@refine B))
      ==> (@refine B)
      as refine_bind.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.

Add Parametric Morphism A B
: (@Bind A B)
    with signature
    (@refineEquiv A)
      ==> (pointwise_relation _ (@refineEquiv B))
      ==> (@refineEquiv B)
      as refineEquiv_bind.
Proof.
  idtac.
  simpl; intros.
  unfold pointwise_relation, refineEquiv, refine in *.
  split_and; simpl in *.
  split; intros;
  inversion_by computes_to_inv;
  eauto.
Qed.

Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ (flip impl))
      ==> (@refine A)
      as refine_flip_impl_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine, impl in *; simpl in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.

Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ impl)
      ==> (flip (@refine A))
      as refine_impl_flip_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine, impl in *; simpl in *.
  intros.
  inversion_by computes_to_inv.
  eauto.
Qed.



Add Parametric Morphism A
: (@Pick A)
    with signature
    (pointwise_relation _ iff)
      ==> (@refineEquiv A)
      as refineEquiv_iff_Pick.
Proof.
  simpl; intros.
  unfold pointwise_relation, refine in *; simpl in *.
  split_iff.
  change (pointwise_relation A impl y x) in H1.
  change (pointwise_relation A impl x y) in H0.
  split;
    intros;
    setoid_rewrite_hyp';
    reflexivity.
Qed.
