/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting

/-!
# Abel-Jacobi classes and the degree splitting

This file records how the abstract Abel-Jacobi divisor class from
`TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic` interacts with the class-group splitting
from `TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting`.

For an order system whose principal divisors have weighted degree zero, a weight-one base point
`x₀` splits the divisor class group as

`Cl(X) ≃+ Pic⁰(X) × ℤ`.

Under this splitting, the class of a point divisor `[x]` has `Pic⁰` component equal to the
weighted Abel-Jacobi class of `x`, and degree component `w x`. Equivalently, the degree-corrected
class `[x] - w(x)[x₀]` maps to the Abel-Jacobi class together with degree `0`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the "`Pic⁰ X = ker deg`
(as an abstract group)" item and the rational-point degree splitting used by the later
normalized Abel-Jacobi morphism. No external mathematics is vendored; the proofs combine Tau
Ceti's existing `OrderSystem.picZero`, `weightedAbelJacobiClass`, and
`classGroupAddEquivPicZeroProdInt` APIs.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

/-! ### Degree correction of point classes -/

/-- Correcting the degree of the point class `[x]` by the base point `x₀` gives exactly the
class-group representative of the weighted Abel-Jacobi class of `x`. -/
lemma degreeCorrection_divisorClass_ofPoint (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.degreeCorrection w h x₀ (S.divisorClass (ofPoint x)) =
      (S.weightedAbelJacobiClass w h hx₀ x : S.ClassGroup) := by
  rw [degreeCorrection_divisorClass, coe_weightedAbelJacobiClass,
    weightedPointBaseDifference_eq_ofPoint_sub_zsmul, weightedDegree_ofPoint]

/-! ### Weighted splitting formulas -/

/-- Under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`, the class of the point divisor `[x]` has
`Pic⁰` component the weighted Abel-Jacobi class of `x`, and degree component `w x`. -/
lemma classGroupAddEquivPicZeroProdInt_divisorClass_ofPoint (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀ (S.divisorClass (ofPoint x)) =
      (S.weightedAbelJacobiClass w h hx₀ x, w x) := by
  rw [classGroupAddEquivPicZeroProdInt_apply, weightedDegreeClass_divisorClass_ofPoint]
  apply Prod.ext
  · apply Subtype.ext
    exact S.degreeCorrection_divisorClass_ofPoint w h hx₀ x
  · rfl

/-- Under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`, a coerced weighted Abel-Jacobi class has degree
zero and `Pic⁰` component itself. -/
lemma classGroupAddEquivPicZeroProdInt_coe_weightedAbelJacobiClass (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀
        (S.weightedAbelJacobiClass w h hx₀ x : S.ClassGroup) =
      (S.weightedAbelJacobiClass w h hx₀ x, 0) :=
  S.classGroupAddEquivPicZeroProdInt_coe_picZero w h hx₀ (S.weightedAbelJacobiClass w h hx₀ x)

/-- The degree-corrected point divisor `[x] - w(x)[x₀]` maps to the weighted Abel-Jacobi class
and degree `0` under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`. -/
lemma classGroupAddEquivPicZeroProdInt_divisorClass_weightedPointBaseDifference
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀
        (S.divisorClass (weightedPointBaseDifference w x₀ x)) =
      (S.weightedAbelJacobiClass w h hx₀ x, 0) := by
  rw [← S.coe_weightedAbelJacobiClass w h hx₀ x,
    S.classGroupAddEquivPicZeroProdInt_coe_weightedAbelJacobiClass w h hx₀ x]

/-- The inverse splitting reconstructs the point class `[x]` from its weighted Abel-Jacobi
component and its degree `w x`. -/
lemma classGroupAddEquivPicZeroProdInt_symm_weightedAbelJacobiClass (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    (S.classGroupAddEquivPicZeroProdInt w h hx₀).symm (S.weightedAbelJacobiClass w h hx₀ x, w x) =
      S.divisorClass (ofPoint x) := by
  rw [← S.classGroupAddEquivPicZeroProdInt_divisorClass_ofPoint w h hx₀ x]
  simp

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
