/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange

/-!
# Base change of the derived subgroup

Let `H` be a commutative Hopf algebra over a field `k`, and let `K / k` be a field extension.
This file proves the canonical containment

```text
  baseChangeHopfIdeal (derivedDefiningIdeal H) ≤
    derivedDefiningIdeal (baseChange H).
```

Since closed subgroups and their defining ideals are ordered oppositely, this says that the
derived subgroup formed after extension to `K` is a closed subgroup of the base change of the
derived subgroup formed over `k`.

The proof uses the universal property of the derived subgroup. Restriction of scalars identifies
the points of the base-changed group with the original group's points and carries the base-changed
derived subgroup to the original one. Hence every commutator lies in the base-changed subgroup;
that subgroup is normal and its pointwise quotients are commutative, so it contains the derived
subgroup formed over `K`.

The reverse containment, and therefore equality, requires descent for the largest Hopf ideal in
the commutator kernel; it is not proved here.

## Main result

* `TauCeti.CommHopfAlgCat.baseChangeHopfIdeal_derivedDefiningIdeal_le`: the derived subgroup
  formed after field extension factors through the base change of the original derived subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d, especially Propositions 6.17 and 6.18.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapters 10 and 16.

This advances the base-change compatibility of `G_der` required in Layer 6, "Reductive and
semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open WithConv
open scoped commutatorElement

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

private theorem commutator_mem_baseChangeDerivedPointsSubgroup
    (H : _root_.CommHopfAlgCat.{v} k) (A : CommAlgCat.{v} K)
    (g h : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    ⁅g, h⁆ ∈ quotientPointsSubgroup (baseChange (K := K) H)
      (baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H)) A := by
  rw [mem_quotientPointsSubgroup_baseChangeHopfIdeal_iff]
  simpa using commutator_mem_derivedPointsSubgroup H
    (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)
    (baseChangePointsMulEquiv (K := K) A H g)
    (baseChangePointsMulEquiv (K := K) A H h)

private theorem commutator_le_baseChangeDerivedPointsSubgroup
    (H : _root_.CommHopfAlgCat.{v} k) (A : CommAlgCat.{v} K) :
    _root_.commutator
        (HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) ≤
      quotientPointsSubgroup (baseChange (K := K) H)
        (baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H)) A := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro _ ⟨g, h, rfl⟩
  exact commutator_mem_baseChangeDerivedPointsSubgroup H A g h

private theorem isNormal_baseChangeDerivedDefiningIdeal
    (H : _root_.CommHopfAlgCat.{v} k) :
    (baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H)).IsNormal := by
  rw [isNormal_iff_quotientPointsSubgroup_normal]
  intro A
  exact Subgroup.Normal.of_commutator_le
    (G := HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A)
    (commutator_le_baseChangeDerivedPointsSubgroup (K := K) H A)

/-- The derived subgroup formed after a field extension is contained in the base change of the
original derived subgroup.

In coordinate rings, this is the displayed inclusion of defining Hopf ideals; its direction is
opposite to the corresponding inclusion of closed subgroup schemes. -/
theorem baseChangeHopfIdeal_derivedDefiningIdeal_le
    (H : _root_.CommHopfAlgCat.{v} k) :
    baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H) ≤
      derivedDefiningIdeal (R := K) (baseChange (K := K) H) := by
  rw [le_derivedDefiningIdeal_iff_isNormal_and_isMulCommutative_pointQuotient]
  let I := baseChangeHopfIdeal (K := K) (derivedDefiningIdeal (R := k) H)
  have hnormal : I.IsNormal := isNormal_baseChangeDerivedDefiningIdeal (K := K) H
  refine ⟨hnormal, fun A ↦ ?_⟩
  let _ : (quotientPointsSubgroup (baseChange (K := K) H) I A).Normal :=
    quotientPointsSubgroup_normal (baseChange (K := K) H) I hnormal A
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (commutator_le_baseChangeDerivedPointsSubgroup (K := K) H A)

end TauCeti.CommHopfAlgCat
