/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic

/-!
# Changing the base point in the abstract Abel-Jacobi class

This file adds the base-point-change calculus for the formal divisor-class shadow of the
Abel-Jacobi map from `TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic`.

For a weight `w : X → ℤ`, a weight-one base point `x₀`, and another weight-one base point `y₀`,
the degree-corrected point divisors satisfy

`[x] - w(x)[y₀] = ([x] - w(x)[x₀]) + w(x)([x₀] - [y₀])`.

Passing to divisor classes gives the corresponding formula in the abstract `Pic⁰` subgroup:
changing the Abel-Jacobi base point translates the class by the weight `w x` times the
degree-zero class `[x₀] - [y₀]`.  For the geometric weight by residue-field degree, this is
translation by the degree of the point.  In the unweighted/algebraically closed specialization,
this is
the familiar identity

`AJ_{y₀}(x) = AJ_{x₀}(x) + AJ_{y₀}(x₀)`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A (`Pic⁰ X = ker deg`) and is
a direct formal prerequisite for Layer F's normalized Abel-Jacobi morphism `aj : X ⟶ Jac X`,
where choosing a rational base point forces `x₀ ↦ 0` and changing that choice should be a
translation.  No external mathematics is vendored; the proofs use only the existing
`WeilDivisor`, `OrderSystem.divisorClass`, and abstract Abel-Jacobi API.
-/

@[expose] public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

/-! ### Class-level base-point changes -/

namespace OrderSystem

variable (S : OrderSystem X G)

/-- The degree-zero class `[x₀] - [y₀]` measuring the translation between two equal-weight
base points. -/
noncomputable def weightedBasepointChangeClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hxy : w x₀ = w y₀) : picZero w hdeg :=
  ⟨S.divisorClass (pointDifference x₀ y₀), by
    rw [divisorClass_mem_picZero]
    simpa using pointDifference_mem_weightedDegreeZeroSubgroup (w := w) (x := x₀) (y := y₀) hxy⟩

@[simp]
lemma coe_weightedBasepointChangeClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hxy : w x₀ = w y₀) : (S.weightedBasepointChangeClass w hdeg hxy : S.ClassGroup) =
      S.divisorClass (pointDifference x₀ y₀) :=
  rfl

@[simp]
lemma weightedBasepointChangeClass_self (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} :
    S.weightedBasepointChangeClass w hdeg (x₀ := x₀) rfl = 0 := by
  apply Subtype.ext
  simp

/-- Reversing the two base points negates the base-point-change class. -/
lemma weightedBasepointChangeClass_swap (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hxy : w x₀ = w y₀) :
    S.weightedBasepointChangeClass w hdeg hxy.symm =
      -S.weightedBasepointChangeClass w hdeg hxy := by
  apply Subtype.ext
  simp only [coe_weightedBasepointChangeClass, NegMemClass.coe_neg]
  rw [← map_neg, ← pointDifference_swap]

/-- Base-point-change classes compose: the translation from `x₀` to `z₀` is the sum of the
translations from `x₀` to `y₀` and from `y₀` to `z₀`. -/
lemma weightedBasepointChangeClass_add (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ z₀ : X} (hxy : w x₀ = w y₀) (hyz : w y₀ = w z₀) :
    S.weightedBasepointChangeClass w hdeg hxy +
        S.weightedBasepointChangeClass w hdeg hyz =
      S.weightedBasepointChangeClass w hdeg (hxy.trans hyz) := by
  apply Subtype.ext
  simp only [coe_weightedBasepointChangeClass, AddMemClass.coe_add]
  rw [← map_add, pointDifference_add_pointDifference_cancel]

/-- Changing the Abel-Jacobi base point from `x₀` to `y₀` adds `w x` times the class
`[x₀] - [y₀]`. For the geometric specialization, `w x` is the residue-field degree. -/
lemma weightedAbelJacobiClass_change_base (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) (x : X) :
    S.weightedAbelJacobiClass w hdeg hy₀ x =
      S.weightedAbelJacobiClass w hdeg hx₀ x +
      w x • S.weightedBasepointChangeClass w hdeg (hx₀.trans hy₀.symm) := by
  apply Subtype.ext
  simp only [coe_weightedAbelJacobiClass, coe_weightedBasepointChangeClass,
    AddMemClass.coe_add, AddSubgroupClass.coe_zsmul]
  rw [← map_zsmul, ← map_add, ← weightedPointBaseDifference_change_base]

/-- The base-point-change class is the Abel-Jacobi class of the old base point with respect to
the new base point. -/
lemma weightedAbelJacobiClass_oldBase_eq_basepointChangeClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    S.weightedAbelJacobiClass w hdeg hy₀ x₀ =
      S.weightedBasepointChangeClass w hdeg (hx₀.trans hy₀.symm) := by
  apply Subtype.ext
  simp [hx₀]

/-- The base-point-change class equals the Abel-Jacobi class of the old base point with respect
to the new base point. -/
lemma weightedBasepointChangeClass_eq_abelJacobiClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    S.weightedBasepointChangeClass w hdeg (hx₀.trans hy₀.symm) =
      S.weightedAbelJacobiClass w hdeg hy₀ x₀ := by
  rw [S.weightedAbelJacobiClass_oldBase_eq_basepointChangeClass w hdeg hx₀ hy₀]

/-- In the class group, the difference between two weighted Abel-Jacobi classes with different
base points is `w(x)` times the class `[x₀] - [y₀]`. -/
lemma weightedAbelJacobiClass_sub_change_base_coe (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ y₀ : X} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) (x : X) :
    (S.weightedAbelJacobiClass w hdeg hy₀ x : S.ClassGroup) -
        (S.weightedAbelJacobiClass w hdeg hx₀ x : S.ClassGroup) =
      w x • S.divisorClass (pointDifference x₀ y₀) := by
  rw [coe_weightedAbelJacobiClass, coe_weightedAbelJacobiClass, ← map_zsmul, ← map_sub,
    weightedPointBaseDifference_sub_change_base]

/-- The difference between two weighted Abel-Jacobi classes with the same base point is the
class `[x] - [y]` when the two points have equal weight. -/
lemma weightedAbelJacobiClass_sub_coe (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ x y : X} (hx₀ : w x₀ = 1) (hxy : w x = w y) :
    (S.weightedAbelJacobiClass w hdeg hx₀ x : S.ClassGroup) -
        (S.weightedAbelJacobiClass w hdeg hx₀ y : S.ClassGroup) =
      S.divisorClass (pointDifference x y) := by
  rw [coe_weightedAbelJacobiClass, coe_weightedAbelJacobiClass, ← map_sub,
    weightedPointBaseDifference_sub_same_base w hxy]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
