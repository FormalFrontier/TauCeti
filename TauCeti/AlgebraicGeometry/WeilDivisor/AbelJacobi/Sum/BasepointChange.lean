/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.BasepointChange
import Mathlib.Tactic.Abel

/-!
# Changing the base point in Abel-Jacobi divisor sums

This file combines the point-level base-point-change API for the abstract Abel-Jacobi class
with the divisor-level Abel-Jacobi sum.

For an order system whose principal divisors have weighted degree zero, and two weight-one
base points `x₀` and `y₀`, the divisor-level Abel-Jacobi sums satisfy

`AJ_{y₀}(D) = AJ_{x₀}(D) + deg(D) • ([x₀] - [y₀])`.

Here `deg(D)` is the weighted degree for the chosen weight `w`.  The unweighted specialization
is the same formula with the ordinary degree.  This is the formal divisor-class bookkeeping
behind the later Abel maps `D ↦ 𝒪_X(D - d·x₀)` used in the Jacobian roadmap: changing the
normalizing base point translates the degree-`d` Abel map by `d` times the class of
`[x₀] - [y₀]`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "`Pic⁰ X = ker deg` (as
an abstract group)", and supplies a direct prerequisite for the Layer D/F Abel-map lane
`D ↦ 𝒪_X(D - d·x₀)`.  No external mathematics is vendored; the proofs reuse Tau Ceti's
existing `weightedAbelJacobiDivisorClass`, `weightedBasepointChangeClass`, and divisor-class
API.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

/-! ### Weighted base-point change for divisor sums -/

/-- Changing the base point in the weighted Abel-Jacobi sum adds the weighted degree times the
base-point-change class.

Geometrically, for the residue-degree weight and rational base points `x₀`, `y₀`, this is the
formal divisor-class identity
`[D - deg(D)y₀] = [D - deg(D)x₀] + deg(D)[x₀ - y₀]` in `Pic⁰`. -/
lemma weightedAbelJacobiDivisorClass_change_base (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiDivisorClass w h hy₀ D =
      S.weightedAbelJacobiDivisorClass w h hx₀ D +
        weightedDegree w D • S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm) := by
  apply Subtype.ext
  simp only [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedBasepointChangeClass,
    AddMemClass.coe_add, AddSubgroupClass.coe_zsmul]
  rw [← S.degreeCorrection_divisorClass w h y₀ D,
    ← S.degreeCorrection_divisorClass w h x₀ D]
  rw [S.degreeCorrection_change_base w h x₀ y₀, weightedDegreeClass_divisorClass]

/-- In the class group, the difference between weighted Abel-Jacobi divisor sums with two
base points is the weighted degree times the class `[x₀] - [y₀]`. -/
lemma weightedAbelJacobiDivisorClass_sub_change_base_coe (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (D : WeilDivisor X) : (S.weightedAbelJacobiDivisorClass w h hy₀ D : S.ClassGroup) -
        (S.weightedAbelJacobiDivisorClass w h hx₀ D : S.ClassGroup) =
      weightedDegree w D • S.divisorClass (pointDifference x₀ y₀) := by
  have hchange := S.degreeCorrection_change_base w h x₀ y₀ (S.divisorClass D)
  rw [weightedDegreeClass_divisorClass] at hchange
  rw [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiDivisorClass_apply,
    ← S.degreeCorrection_divisorClass w h y₀ D,
    ← S.degreeCorrection_divisorClass w h x₀ D]
  rw [hchange, add_sub_cancel_left]

/-- If a divisor has weighted degree zero, its weighted Abel-Jacobi sum is independent of the
choice of weight-one base point. -/
lemma weightedAbelJacobiDivisorClass_eq_of_weightedDegree_eq_zero (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    {D : WeilDivisor X} (hD : weightedDegree w D = 0) :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
      S.weightedAbelJacobiDivisorClass w h hy₀ D := by
  rw [S.weightedAbelJacobiDivisorClass_change_base w h hx₀ hy₀ D, hD, zero_zsmul,
    add_zero]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
