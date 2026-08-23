/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Image.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting

/-!
# The degree image and quotient at a weight-one base point

This file gives the weight-one counterparts of the general degree-image and degree-quotient
results of `TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Image.Basic`, using the splitting theory of
`TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting`. These corollaries specialise to a
weight-one base point: the range statement is derived from the general degree-image API, while
the quotient equivalence keeps the explicit inverse supplied by the splitting section.

`DegreeImage` computes the image of the descended weighted degree unconditionally,
`(weightedDegreeClass w h).range = AddSubgroup.closure (Set.range w)`, and identifies the degree
quotient `Cl(X) ⧸ Pic⁰` with that image. Those results are independent of the weight-one
splitting; this file adds the corollaries that *do* use it. `DegreeSplitting` shows that a
weight-one base point makes the descended weighted degree *surjective*, with the degree section
`n ↦ n • [x₀]` as an explicit right inverse. So:

* `weightedDegreeClass_range_eq_top_of_weight_one` restates surjectivity at the `AddSubgroup`
  level as `(weightedDegreeClass w h).range = ⊤`, the weight-one special case of the general
  `weightedDegreeClass_range_eq_top`;
* `classGroupQuotientPicZeroEquivIntOfWeightOne` builds `Cl(X) ⧸ Pic⁰ ≃+ ℤ` from that right
  inverse, giving an explicit inverse and, together with `DegreeSplitting`'s
  `Cl(X) ≃+ picZero × ℤ`, exhibiting the degree as the projection to the `ℤ` factor.

This advances the same `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A targets as
`DegreeImage`; it reuses `DegreeImage`'s image computation, `DegreeSplitting`'s `degreeSection` /
`weightedDegreeClass_surjective`, and Mathlib's
`QuotientAddGroup.quotientKerEquivOfRightInverse`.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*} {G : Type*} [AddCommGroup G] (S : OrderSystem X G)

namespace OrderSystem

/-- With a weight-one base point the descended weighted degree hits all of `ℤ`; this is the
weight-one specialization of `weightedDegreeClass_range_eq_top`. -/
lemma weightedDegreeClass_range_eq_top_of_weight_one (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : (weightedDegreeClass w h).range = ⊤ := by
  exact AddMonoidHom.range_eq_top.mpr (S.weightedDegreeClass_surjective w h hx₀)

/-- **The degree quotient at a weight-one base point.** With a weight-one base point the degree
section `n ↦ n • [x₀]` is a genuine right inverse of the descended weighted degree, so the class
group modulo the abstract `Pic⁰` is `ℤ`, `Cl(X) ⧸ Pic⁰ ≃+ ℤ`, with an explicit inverse. Together
with `DegreeSplitting`'s `Cl(X) ≃+ picZero × ℤ` this exhibits the degree as the projection to the
`ℤ` factor. -/
@[expose] noncomputable def classGroupQuotientPicZeroEquivIntOfWeightOne (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) :
    S.ClassGroup ⧸ picZero w h ≃+ ℤ :=
  QuotientAddGroup.quotientKerEquivOfRightInverse (weightedDegreeClass w h) (S.degreeSection x₀)
    fun n => S.weightedDegreeClass_degreeSection_of_weight_one w h hx₀ n

@[simp]
lemma classGroupQuotientPicZeroEquivIntOfWeightOne_mk (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (c : S.ClassGroup) :
    S.classGroupQuotientPicZeroEquivIntOfWeightOne w h hx₀ (QuotientAddGroup.mk c) =
      weightedDegreeClass w h c :=
  rfl

@[simp]
lemma classGroupQuotientPicZeroEquivIntOfWeightOne_symm_apply (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (n : ℤ) :
    (S.classGroupQuotientPicZeroEquivIntOfWeightOne w h hx₀).symm n =
      QuotientAddGroup.mk (S.degreeSection x₀ n) :=
  rfl

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
