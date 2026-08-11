/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Splitting

/-!
# Abel-Jacobi sums of Weil divisors

This file extends the formal Layer A Abel-Jacobi API from points to arbitrary Weil divisors.
Given an order system whose principal divisors have weighted degree zero and a weight-one base
point `x₀`, the degree splitting

`Cl(X) ≃+ Pic⁰(X) × ℤ`

has first component `c ↦ c - (weightedDegreeClass w h c) · [x₀]`. Composing this component
with the divisor-class map gives the additive Abel-Jacobi sum of a formal divisor:

`D ↦ [D - weightedDegree w D · x₀] ∈ Pic⁰`.

For a divisor `D = ∑ nₓ[x]`, this is the finite sum `∑ nₓ AJ(x)`. This is the formal
divisor-class shadow of the Abel maps `D ↦ 𝒪_X(D - d x₀)` used later to construct the
Jacobian from symmetric powers.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the "`Pic⁰ X = ker deg`
(as an abstract group)" item and the Layer D/F Abel-map prerequisite `D ↦ 𝒪_X(D - d·x₀)`.
It reuses Tau Ceti's existing `WeilDivisor`, `OrderSystem.picZero`, `degreeCorrection`, and
`weightedAbelJacobiClass` APIs; no external mathematics is vendored.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

/-! ### Weighted Abel-Jacobi sums -/

/-- The additive Abel-Jacobi sum of a Weil divisor.

For a divisor `D`, this is the class of `D - weightedDegree w D • [x₀]` in the abstract
weighted-degree-zero Picard group. On point divisors it recovers `weightedAbelJacobiClass`,
and on finite sums it is the corresponding sum of point Abel-Jacobi classes. -/
noncomputable def weightedAbelJacobiDivisorClass (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) : WeilDivisor X →+ picZero w h :=
  ((S.degreeCorrection w h x₀).comp S.divisorClass).codRestrict (picZero w h) fun D =>
    S.degreeCorrection_mem_picZero w h hx₀ (S.divisorClass D)

/-- Coercing the weighted Abel-Jacobi sum to the class group gives the divisor class of
`D - weightedDegree w D • [x₀]`. This is the canonical class-group form of the construction. -/
@[simp]
lemma coe_weightedAbelJacobiDivisorClass_apply (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (S.weightedAbelJacobiDivisorClass w h hx₀ D : S.ClassGroup) =
      S.divisorClass (D - weightedDegree w D • ofPoint x₀) := by
  simp [weightedAbelJacobiDivisorClass, S.degreeCorrection_divisorClass w h x₀ D]

/-- The weighted Abel-Jacobi sum is zero on the base-point divisor. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofPoint_base (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (ofPoint x₀) = 0 := by
  rw [← S.weightedAbelJacobiClass_base w h hx₀]
  apply Subtype.ext
  rw [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiClass,
    weightedPointBaseDifference_self hx₀, weightedDegree_ofPoint, hx₀, one_zsmul, sub_self]

/-- On a point divisor, the Abel-Jacobi sum is the point Abel-Jacobi class. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofPoint (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (ofPoint x) =
      S.weightedAbelJacobiClass w h hx₀ x := by
  apply Subtype.ext
  rw [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiClass,
    weightedDegree_ofPoint, weightedPointBaseDifference_eq_ofPoint_sub_zsmul]

/-- The Abel-Jacobi sum of a sum of divisors is the sum of their Abel-Jacobi sums. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_add (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D E : WeilDivisor X) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (D + E) =
      S.weightedAbelJacobiDivisorClass w h hx₀ D +
        S.weightedAbelJacobiDivisorClass w h hx₀ E :=
  map_add (S.weightedAbelJacobiDivisorClass w h hx₀) D E

/-- The Abel-Jacobi sum of an integral multiple of a divisor is the corresponding multiple of
the Abel-Jacobi sum. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_zsmul (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (n : ℤ) (D : WeilDivisor X) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (n • D) =
      n • S.weightedAbelJacobiDivisorClass w h hx₀ D :=
  map_zsmul (S.weightedAbelJacobiDivisorClass w h hx₀) n D

/-- The Abel-Jacobi sum of a finitely supported formal divisor is the finite sum of the
point Abel-Jacobi classes weighted by the divisor coefficients. -/
lemma weightedAbelJacobiDivisorClass_eq_sum (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
      D.sum fun x n => n • S.weightedAbelJacobiClass w h hx₀ x := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
      simp
  | single x n =>
      rw [Finsupp.sum_single_index]
      · rw [single_eq_zsmul_ofPoint x n,
        S.weightedAbelJacobiDivisorClass_zsmul w h hx₀ n (ofPoint x),
        S.weightedAbelJacobiDivisorClass_ofPoint w h hx₀ x]
      · simp
  | add D E hD hE =>
      rw [S.weightedAbelJacobiDivisorClass_add w h hx₀, Finsupp.sum_add_index, hD, hE]
      · intro x
        simp
      · intro x a b
        simp [add_zsmul]

/-- Equality of weighted Abel-Jacobi sums is equality of the corresponding degree-corrected
divisor classes. -/
lemma weightedAbelJacobiDivisorClass_eq_iff_divisorClass
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X} :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
        S.weightedAbelJacobiDivisorClass w h hx₀ E ↔
      S.divisorClass (D - weightedDegree w D • ofPoint x₀) =
        S.divisorClass (E - weightedDegree w E • ofPoint x₀) := by
  constructor
  · intro hDE
    rw [← S.coe_weightedAbelJacobiDivisorClass_apply w h hx₀ D,
      ← S.coe_weightedAbelJacobiDivisorClass_apply w h hx₀ E]
    exact congr_arg Subtype.val hDE
  · intro hDE
    apply Subtype.ext
    rwa [S.coe_weightedAbelJacobiDivisorClass_apply w h hx₀ D,
      S.coe_weightedAbelJacobiDivisorClass_apply w h hx₀ E]

/-- Equality of weighted Abel-Jacobi sums is linear equivalence of the corresponding
degree-corrected divisors. -/
lemma weightedAbelJacobiDivisorClass_eq_iff_linearlyEquivalent
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X} :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
        S.weightedAbelJacobiDivisorClass w h hx₀ E ↔
      S.LinearlyEquivalent (D - weightedDegree w D • ofPoint x₀)
        (E - weightedDegree w E • ofPoint x₀) := by
  rw [S.weightedAbelJacobiDivisorClass_eq_iff_divisorClass w h hx₀, S.divisorClass_eq_iff]

/-- If two divisors have the same weighted degree, equality of their weighted Abel-Jacobi
classes is exactly linear equivalence of the original divisors.

The equal-degree hypothesis is essential: the Abel-Jacobi class only records the `Pic⁰`
component of the divisor class after subtracting the same degree from the chosen base point. -/
lemma weightedAbelJacobiDivisorClass_eq_iff_linearlyEquivalent_of_weightedDegree_eq
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1)
    {D E : WeilDivisor X} (hDE : weightedDegree w D = weightedDegree w E) :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
        S.weightedAbelJacobiDivisorClass w h hx₀ E ↔
      S.LinearlyEquivalent D E := by
  rw [S.weightedAbelJacobiDivisorClass_eq_iff_linearlyEquivalent w h hx₀, hDE]
  constructor
  · intro hlin
    have hlin' :=
      LinearlyEquivalent.add_right (S := S) hlin (weightedDegree w E • ofPoint x₀)
    simpa only [sub_add_cancel] using hlin'
  · intro hlin
    have hlin' :=
      LinearlyEquivalent.add_right (S := S) hlin (-(weightedDegree w E • ofPoint x₀))
    simpa only [sub_eq_add_neg] using hlin'

/-- In the unweighted theory, equal-degree divisors have the same Abel-Jacobi class exactly when
they are linearly equivalent. -/
lemma weightedAbelJacobiDivisorClass_one_eq_iff_linearlyEquivalent_of_degree_eq
    (h : S.IsUnweightedDegreeZero) (x₀ : X) {D E : WeilDivisor X} (hDE : degree D = degree E) :
    S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl D =
        S.weightedAbelJacobiDivisorClass (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl E ↔
      S.LinearlyEquivalent D E := by
  refine S.weightedAbelJacobiDivisorClass_eq_iff_linearlyEquivalent_of_weightedDegree_eq
    (fun _ : X => (1 : ℤ)) h (x₀ := x₀) rfl ?_
  simpa only [weightedDegree_one_eq_degree] using hDE

/-- The Abel-Jacobi sum is invariant under linear equivalence of divisors with the same
weighted degree. -/
lemma weightedAbelJacobiDivisorClass_eq_of_linearlyEquivalent
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1)
    {D E : WeilDivisor X} (hlin : S.LinearlyEquivalent D E) :
    S.weightedAbelJacobiDivisorClass w h hx₀ D =
      S.weightedAbelJacobiDivisorClass w h hx₀ E := by
  have hclass : S.divisorClass D = S.divisorClass E := S.divisorClass_eq_iff.mpr hlin
  have hdeg : weightedDegree w D = weightedDegree w E := by
    rw [← weightedDegreeClass_divisorClass w h D, hclass, weightedDegreeClass_divisorClass]
  apply Subtype.ext
  rw [coe_weightedAbelJacobiDivisorClass_apply, coe_weightedAbelJacobiDivisorClass_apply, hdeg]
  exact S.divisorClass_eq_iff.mpr (by
    rw [linearlyEquivalent_iff, sub_sub_sub_cancel_right]
    exact (S.linearlyEquivalent_iff).mp hlin)

/-- Under the splitting `Cl(X) ≃+ Pic⁰ × ℤ`, the class of a divisor has `Pic⁰` component
its weighted Abel-Jacobi sum and degree component its weighted degree. -/
lemma classGroupAddEquivPicZeroProdInt_divisorClass (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    S.classGroupAddEquivPicZeroProdInt w h hx₀ (S.divisorClass D) =
      (S.weightedAbelJacobiDivisorClass w h hx₀ D, weightedDegree w D) := by
  rw [classGroupAddEquivPicZeroProdInt_apply]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    -- `Prod.ext` and `Subtype.ext` reduce the first projection to its coercion in `ClassGroup`.
    change S.degreeCorrection w h x₀ (S.divisorClass D) =
      (S.weightedAbelJacobiDivisorClass w h hx₀ D : S.ClassGroup)
    rw [S.degreeCorrection_divisorClass, S.coe_weightedAbelJacobiDivisorClass_apply]
  · rw [weightedDegreeClass_divisorClass]

/-- The inverse splitting reconstructs the divisor class from its weighted Abel-Jacobi sum and
weighted degree. -/
lemma classGroupAddEquivPicZeroProdInt_symm_weightedAbelJacobiDivisorClass
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    (S.classGroupAddEquivPicZeroProdInt w h hx₀).symm
        (S.weightedAbelJacobiDivisorClass w h hx₀ D, weightedDegree w D) =
      S.divisorClass D := by
  rw [← S.classGroupAddEquivPicZeroProdInt_divisorClass w h hx₀ D]
  simp

/-- A principal divisor has zero Abel-Jacobi sum. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_principalDivisor (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (g : G) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (S.principalDivisor g) = 0 := by
  apply Subtype.ext
  rw [coe_weightedAbelJacobiDivisorClass_apply, h g, zero_zsmul, sub_zero,
    divisorClass_principalDivisor]
  rfl

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
