/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.PicZeroQuotient

/-!
# Abel-Jacobi sums through the weighted-degree-zero quotient

This file connects two existing Layer A models in the Jacobian roadmap.  The file
`WeilDivisor.AbelJacobiSum` defines the formal Abel-Jacobi sum of a divisor as an element of
the abstract `Pic⁰`, while `WeilDivisor.PicZeroQuotient` identifies `Pic⁰` with
weighted-degree-zero divisors modulo principal divisors of weighted degree zero.  Here we record
the corresponding quotient representative:

`D ↦ [D - weightedDegree w D • x₀]` in
`(weighted-degree-zero divisors) / (principal divisors)`.

Under the quotient equivalence, this representative maps to the existing Abel-Jacobi divisor
class.  For point divisors this recovers the point Abel-Jacobi class.  This is the quotient-level
form of the Abel map `D ↦ 𝒪_X(D - d·x₀)` used later for symmetric powers in the construction of
the Jacobian, with the ordinary degree formula recovered from the constant-weight-one
specialization.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, specifically the "`Pic⁰ X =
ker deg` (as an abstract group)" item and the Layer D/F Abel-map prerequisite
`D ↦ 𝒪_X(D - d·x₀)`.  No external mathematics is vendored; the proofs reuse Tau Ceti's existing
`weightedAbelJacobiDivisorClass` and quotient equivalence
`weightedDegreeZeroQuotientEquivPicZero`.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

/-! ### Weighted quotient representatives -/

/-- The quotient class of the degree-corrected representative
`D - weightedDegree(D) • [x₀]`. -/
def weightedAbelJacobiQuotientClass (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) :
    WeilDivisor X →+
      weightedDegreeZeroSubgroup w ⧸ S.principalSubgroupOfWeightedDegreeZero w where
  toFun D := QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D)
  map_zero' := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [mem_principalSubgroupOfWeightedDegreeZero, coe_weightedAbelJacobiDegreeZeroDivisor]
    simp
  map_add' D E := by
    have hdiv :
        weightedAbelJacobiDegreeZeroDivisor w hx₀ (D + E) =
          weightedAbelJacobiDegreeZeroDivisor w hx₀ D +
            weightedAbelJacobiDegreeZeroDivisor w hx₀ E := by
      ext x
      simp [map_add, add_zsmul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    -- `QuotientAddGroup.mk` is the underlying homomorphism `QuotientAddGroup.mk'`, so its
    -- additivity is `map_add`; rewrite `mk` to `mk'` to apply it explicitly.
    simp only [hdiv, ← QuotientAddGroup.mk'_apply, map_add]

private lemma weightedAbelJacobiQuotientClass_mk_def (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D) :=
  rfl

@[simp]
lemma weightedAbelJacobiQuotientClass_mk (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      QuotientAddGroup.mk (weightedAbelJacobiDegreeZeroDivisor w hx₀ D) :=
  S.weightedAbelJacobiQuotientClass_mk_def w hx₀ D

/-- The quotient Abel-Jacobi representative of a sum is the sum of the quotient
representatives. -/
lemma weightedAbelJacobiQuotientClass_add (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D E : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ (D + E) =
      S.weightedAbelJacobiQuotientClass w hx₀ D +
        S.weightedAbelJacobiQuotientClass w hx₀ E :=
  map_add (S.weightedAbelJacobiQuotientClass w hx₀) D E

/-- The quotient Abel-Jacobi representative of an integral multiple is the corresponding
multiple of the quotient representative. -/
lemma weightedAbelJacobiQuotientClass_zsmul (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (n : ℤ) (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ (n • D) =
      n • S.weightedAbelJacobiQuotientClass w hx₀ D :=
  map_zsmul (S.weightedAbelJacobiQuotientClass w hx₀) n D

/-- The quotient representative maps to the weighted Abel-Jacobi divisor class under the
degree-zero quotient equivalence. -/
lemma weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (D : WeilDivisor X) :
    S.weightedDegreeZeroQuotientEquivPicZero w h
        (S.weightedAbelJacobiQuotientClass w hx₀ D) =
      S.weightedAbelJacobiDivisorClass w h hx₀ D := by
  rw [weightedAbelJacobiQuotientClass_mk, weightedDegreeZeroQuotientEquivPicZero_mk]
  apply Subtype.ext
  rw [coe_weightedDegreeZeroClassHom_apply, coe_weightedAbelJacobiDivisorClass_apply,
    coe_weightedAbelJacobiDegreeZeroDivisor]

/-- For point divisors, the quotient representative maps to the point Abel-Jacobi class. -/
lemma weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass_ofPoint
    (w : X → ℤ) (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (x : X) :
    S.weightedDegreeZeroQuotientEquivPicZero w h
        (S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x)) =
      S.weightedAbelJacobiClass w h hx₀ x := by
  rw [S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedAbelJacobiDivisorClass_ofPoint]

/-- The quotient Abel-Jacobi representative of a finitely supported formal divisor is the
finite sum of the quotient representatives of its point divisors. -/
lemma weightedAbelJacobiQuotientClass_eq_sum (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    (D : WeilDivisor X) :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
      D.sum fun x n => n • S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero =>
      simp
  | single x n =>
      rw [Finsupp.sum_single_index]
      · rw [single_eq_zsmul_ofPoint x n,
          S.weightedAbelJacobiQuotientClass_zsmul w hx₀ n (ofPoint x)]
      · simp
  | add D E hD hE =>
      rw [S.weightedAbelJacobiQuotientClass_add w hx₀, Finsupp.sum_add_index, hD, hE]
      · intro x
        simp
      · intro x a b
        simp [add_zsmul]

/-- The base-point divisor represents zero in the degree-zero quotient. -/
lemma weightedAbelJacobiQuotientClass_ofPoint_base (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiQuotientClass w hx₀ (ofPoint x₀) = 0 := by
  rw [weightedAbelJacobiQuotientClass_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  rw [mem_principalSubgroupOfWeightedDegreeZero, coe_weightedAbelJacobiDegreeZeroDivisor,
    weightedDegree_ofPoint, hx₀, one_zsmul, sub_self]
  exact S.principalSubgroup.zero_mem

/-- A principal divisor has zero weighted quotient Abel-Jacobi representative. -/
lemma weightedAbelJacobiQuotientClass_principalDivisor (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (g : G) :
    S.weightedAbelJacobiQuotientClass w hx₀ (S.principalDivisor g) = 0 := by
  apply (S.weightedDegreeZeroQuotientEquivPicZero w h).injective
  rw [S.weightedDegreeZeroQuotientEquivPicZero_weightedAbelJacobiQuotientClass,
    S.weightedAbelJacobiDivisorClass_principalDivisor]
  simp

/-- Equality of weighted quotient Abel-Jacobi representatives is equality of the corresponding
degree-corrected divisor classes. -/
lemma weightedAbelJacobiQuotientClass_eq_iff_divisorClass (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1)
    {D E : WeilDivisor X} :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
        S.weightedAbelJacobiQuotientClass w hx₀ E ↔
      S.divisorClass (D - weightedDegree w D • ofPoint x₀) =
        S.divisorClass (E - weightedDegree w E • ofPoint x₀) := by
  rw [weightedAbelJacobiQuotientClass_mk, weightedAbelJacobiQuotientClass_mk,
    QuotientAddGroup.eq_iff_sub_mem, mem_principalSubgroupOfWeightedDegreeZero,
    S.divisorClass_eq_iff, linearlyEquivalent_iff]
  simp only [AddSubgroup.coe_sub, coe_weightedAbelJacobiDegreeZeroDivisor]

/-- Equality of weighted quotient Abel-Jacobi representatives is linear equivalence of the
corresponding degree-corrected divisors. -/
lemma weightedAbelJacobiQuotientClass_eq_iff_linearlyEquivalent
    (w : X → ℤ) {x₀ : X} (hx₀ : w x₀ = 1) {D E : WeilDivisor X} :
    S.weightedAbelJacobiQuotientClass w hx₀ D =
        S.weightedAbelJacobiQuotientClass w hx₀ E ↔
      S.LinearlyEquivalent (D - weightedDegree w D • ofPoint x₀)
        (E - weightedDegree w E • ofPoint x₀) := by
  rw [S.weightedAbelJacobiQuotientClass_eq_iff_divisorClass w hx₀, S.divisorClass_eq_iff]

end

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti
