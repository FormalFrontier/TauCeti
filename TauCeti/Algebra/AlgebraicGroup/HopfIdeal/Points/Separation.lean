/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Recovering reduced closed subgroups from geometric points

Let `H` be a commutative Hopf algebra over a field and fix an algebraically closed extension. A
Hopf ideal `I` cuts out the subgroup of extension-valued points of `H` that vanish on `I`. If the
quotient `H/I` is reduced and of finite type, its points separate functions, so this subgroup
determines `I`.

The order statement is contravariant: if every point cut out by `J` is also cut out by `I`, then
`I ≤ J`, provided `H/J` is reduced and of finite type. Applying it in both directions shows that
two reduced finite-type closed subgroups with the same points have the same defining Hopf ideal.

## Main declarations

* `TauCeti.HopfIdeal.le_of_quotientPointsSubgroup_le`: recover an inclusion of Hopf ideals from
  the reverse inclusion of their algebraically closed point subgroups.
* `TauCeti.HopfIdeal.eq_of_quotientPointsSubgroup_eq`: reduced finite-type closed subgroups are
  determined by their algebraically closed points.

## References

* J. S. Milne, *Algebraic Groups* (2017), Sections 1.d and 2.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.

This is the point-separation input for the maximal-torus step in Layer 7 of the ReductiveGroups
roadmap. It allows pointwise centralizer calculations to determine reduced closed subgroup
schemes.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace HopfIdeal

variable {k : Type u} [Field k]
variable {K : Type w} [Field K] [Algebra k K] [IsAlgClosed K]
variable {H : _root_.CommHopfAlgCat.{v} k} {I J : HopfIdeal k H}

/-- Recover an inclusion of Hopf ideals from the reverse inclusion of their point subgroups.

Only the quotient by the ideal on the right of the conclusion must be reduced and of finite
type. Those hypotheses make its `K`-valued points separate functions. -/
theorem le_of_quotientPointsSubgroup_le
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H J)]
    [IsReduced (CommHopfAlgCat.quotient H J)]
    (hpoints : CommHopfAlgCat.quotientPointsSubgroup H J (CommAlgCat.of k K) ≤
      CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K)) :
    I ≤ J := by
  intro x hx
  apply HopfIdeal.mem_toIdeal.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply eq_of_forall_algHom_apply_eq (k := k) (K := K)
  intro f
  let g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k K) :=
    CommHopfAlgCat.quotientPointsHom H J (CommAlgCat.of k K) (toConv f)
  have hgJ : g ∈ CommHopfAlgCat.quotientPointsSubgroup H J (CommAlgCat.of k K) :=
    CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H J
      (CommAlgCat.of k K) (toConv f)
  have hgI := hpoints hgJ
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hgI
  have hzero :
      ((CommHopfAlgCat.quotientPointsHom H J (CommAlgCat.of k K) (toConv f)).ofConv) x = 0 :=
    by simpa only [g] using hgI x hx
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply] at hzero
  simpa only [WithConv.ofConv_toConv, map_zero, Ideal.Quotient.mkₐ_eq_mk] using hzero

/-- Two reduced finite-type closed subgroups of an affine group have the same defining Hopf ideal
when they have the same points over an algebraically closed extension. -/
theorem eq_of_quotientPointsSubgroup_eq
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H I)]
    [IsReduced (CommHopfAlgCat.quotient H I)]
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H J)]
    [IsReduced (CommHopfAlgCat.quotient H J)]
    (hpoints : CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k K) =
      CommHopfAlgCat.quotientPointsSubgroup H J (CommAlgCat.of k K)) :
    I = J := by
  apply le_antisymm
  · apply le_of_quotientPointsSubgroup_le (K := K)
    rw [hpoints]
  · apply le_of_quotientPointsSubgroup_le (K := K)
    rw [hpoints]

end HopfIdeal

end TauCeti
