/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Characters of a unipotent affine group

Let `H` be the reduced finite-type coordinate Hopf algebra of an affine group over a field `k`,
and let `K` be an algebraically closed extension of `k`. If every `K`-valued point of the group is
unipotent, then every group-like element of `H` is one. In geometric language, every algebraic
character of the group is trivial.

The argument combines two independent inputs. A unipotent point evaluates every group-like
element at one, by the rank-one representation attached to that element. Algebraically closed
points separate elements of a reduced finite-type algebra, so an element evaluated as one by all
points is itself one. The conclusion does not require connectedness: the pointwise unipotence
hypothesis is already strong enough.

## Main results

* `TauCeti.GroupLike.eq_one_of_forall_algHom_apply_eq_one`: a group-like element evaluated as one
  at every algebraically closed point is one.
* `TauCeti.groupLike_eq_one_of_forall_isUnipotentPoint`: every algebraic character is trivial when
  all algebraically closed points are unipotent.
* `TauCeti.subsingleton_groupLike_of_forall_isUnipotentPoint`: the character group is
  subsingleton under the same hypotheses.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This completes the "no nontrivial characters" consequence in Layer 5, "Unipotent groups", of
`TauCetiRoadmap/ReductiveGroups/README.md`.
-/

public section

open WithConv

namespace TauCeti

namespace GroupLike

universe u v w

variable {k : Type u} {H : Type v} {K : Type w}
  [Field k] [CommRing H] [Bialgebra k H] [Algebra.FiniteType k H]
  [IsReduced H] [Field K] [Algebra k K] [IsAlgClosed K]

/-- A group-like element of a reduced finite-type algebra is one if every algebraically closed
point evaluates it as one.

This is the coordinate-algebra form of the fact that an algebraic character is determined by its
values on geometric points. -/
theorem eq_one_of_forall_algHom_apply_eq_one (x : GroupLike k H)
    (h : ∀ f : H →ₐ[k] K, f x = 1) : x = 1 := by
  apply _root_.GroupLike.val_injective
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := K)
  intro f
  simpa using h f

end GroupLike

universe u v w

variable {k : Type u} {H : Type v} {K : Type w}
  [Field k] [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [IsReduced H] [Field K] [Algebra k K] [IsAlgClosed K]

/-- **A reduced finite-type affine group whose algebraically closed points are all unipotent has
no nontrivial algebraic characters.** Every group-like element of its coordinate Hopf algebra is
one. -/
theorem groupLike_eq_one_of_forall_isUnipotentPoint
    (hH : ∀ g : WithConv (H →ₐ[k] K), HopfAlgebra.IsUnipotentPoint g)
    (x : GroupLike k H) : x = 1 := by
  apply GroupLike.eq_one_of_forall_algHom_apply_eq_one (K := K) x
  intro g
  exact (hH (toConv g)).apply_groupLike_eq_one x

/-- The algebraic character group of a reduced finite-type affine group is subsingleton when all
of its algebraically closed points are unipotent. -/
theorem subsingleton_groupLike_of_forall_isUnipotentPoint
    (hH : ∀ g : WithConv (H →ₐ[k] K), HopfAlgebra.IsUnipotentPoint g) :
    Subsingleton (GroupLike k H) :=
  ⟨fun x y ↦
    (groupLike_eq_one_of_forall_isUnipotentPoint hH x).trans
      (groupLike_eq_one_of_forall_isUnipotentPoint hH y).symm⟩

end TauCeti
