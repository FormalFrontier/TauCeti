/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Normalizing semigroup-group positive-definite functions

This file records the standard normalization step for Berg--Christensen--Ressel
semigroup-group positive-definite functions on `ℝ≥0 × V`: if `F (0, 0) ≠ 0`, then multiplying
`F` by the reciprocal of the nonnegative real number `(F (0, 0)).re` gives a
semigroup-group positive-definite function with value `1` at the origin.

The generic positive-definite-function normalization API applies to the internal involutive
monoid used to define `TauCeti.IsSemigroupGroupPD`, but that wrapper is intentionally private.
This file exposes the corresponding public API directly on functions `ℝ≥0 × V → ℂ`. It is a
small prerequisite for the BCR semigroup--Bochner representation milestone, where one separates
normalization from the independent boundedness and continuity hypotheses.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the positive-definite
function API item "normalization `F(0) = 1`" and Milestone 2 ("BCR semigroup--Bochner").

## Main declarations

* `TauCeti.IsSemigroupGroupPD.normalize`: the normalized function remains
  semigroup-group positive definite.
* `TauCeti.IsSemigroupGroupPD.normalize_apply_zero`: the normalized function has value `1`
  at `(0, 0)`.
* `TauCeti.IsSemigroupGroupPD.normalize_continuous`: normalization preserves continuity.
* `TauCeti.IsSemigroupGroupPD.norm_normalize_apply_le_one_of_norm_le_map_zero_re`: a bounded
  BCR function becomes bounded by `1` after normalization.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

namespace IsSemigroupGroupPD

section PositiveDefinite

variable {V : Type*} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

/-- The normalizing scalar `((F (0, 0)).re)⁻¹`, viewed as a complex number, is nonnegative. -/
private theorem normalizeScalar_nonneg (hF : IsSemigroupGroupPD F) :
    0 ≤ (((F (0, 0)).re)⁻¹ : ℂ) := by
  exact inv_nonneg.mpr ((RCLike.ofReal_nonneg (K := ℂ)).mpr hF.map_zero_re_nonneg)

/-- Multiplying a semigroup-group positive-definite function by the reciprocal of its real value
at the origin preserves semigroup-group positive-definiteness. If `F (0, 0) = 0`, this is the
zero scaling; the separate `normalize_apply_zero` lemma records the useful nonzero case. -/
theorem normalize (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD fun p => (((F (0, 0)).re)⁻¹ : ℂ) * F p :=
  hF.const_mul hF.normalizeScalar_nonneg

/-- The normalized semigroup-group positive-definite function has value `1` at the origin. -/
@[simp]
theorem normalize_apply_zero (hF : IsSemigroupGroupPD F) (h0 : F (0, 0) ≠ 0) :
    (((F (0, 0)).re)⁻¹ : ℂ) * F (0, 0) = 1 := by
  have hpos := hF.map_zero_re_pos_of_ne_zero h0
  rw [hF.map_zero_eq_ofReal_re]
  norm_cast
  exact inv_mul_cancel₀ hpos.ne'

/-- A normalized semigroup-group positive-definite function has origin value `1`, stated as the
map-zero lemma for the normalized function. -/
theorem normalize_map_zero (hF : IsSemigroupGroupPD F) (h0 : F (0, 0) ≠ 0) :
    (fun p => (((F (0, 0)).re)⁻¹ : ℂ) * F p) (0, 0) = 1 :=
  hF.normalize_apply_zero h0

end PositiveDefinite

section Pointwise

variable {V : Type*} [Zero V] {F : ℝ≥0 × V → ℂ}

/-- If a semigroup-group positive-definite function is already normalized at the origin, the
explicit normalization leaves it unchanged pointwise. -/
theorem normalize_apply_of_map_zero_eq_one (hF0 : F (0, 0) = 1) (p : ℝ≥0 × V) :
    (((F (0, 0)).re)⁻¹ : ℂ) * F p = F p := by
  simp [hF0]

/-- Normalization preserves continuity. -/
theorem normalize_continuous [TopologicalSpace V] (hFcont : Continuous F) :
    Continuous fun p : ℝ≥0 × V => (((F (0, 0)).re)⁻¹ : ℂ) * F p :=
  continuous_const.mul hFcont

end Pointwise

section PositiveDefiniteTopology

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] {F : ℝ≥0 × V → ℂ}

/-- Package normalization with continuity preservation. -/
theorem normalize_and_continuous (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) :
    IsSemigroupGroupPD (fun p => (((F (0, 0)).re)⁻¹ : ℂ) * F p) ∧
      Continuous (fun p : ℝ≥0 × V => (((F (0, 0)).re)⁻¹ : ℂ) * F p) :=
  ⟨hFpd.normalize, normalize_continuous hFcont⟩

end PositiveDefiniteTopology

section Pointwise

variable {V : Type*} [Zero V] {F : ℝ≥0 × V → ℂ}

/-- A function bounded by its origin value becomes bounded by `1` after normalization. This keeps
the boundedness hypothesis separate, as in the BCR representation theorem. -/
theorem norm_normalize_apply_le_one_of_norm_le_map_zero_re
    (hbound : ∀ p : ℝ≥0 × V, ‖F p‖ ≤ (F (0, 0)).re) (p : ℝ≥0 × V) :
    ‖(((F (0, 0)).re)⁻¹ : ℂ) * F p‖ ≤ 1 := by
  have hnonneg : 0 ≤ (F (0, 0)).re := le_trans (norm_nonneg (F (0, 0))) (hbound (0, 0))
  rcases hnonneg.lt_or_eq with hpos | hre
  · have hnorm : ‖(((F (0, 0)).re)⁻¹ : ℂ)‖ = ((F (0, 0)).re)⁻¹ := by
      rw [norm_inv, Complex.norm_of_nonneg hpos.le]
    rw [norm_mul, hnorm]
    have hscale := mul_le_mul_of_nonneg_left (hbound p) (inv_nonneg.mpr hpos.le)
    rw [inv_mul_cancel₀ hpos.ne'] at hscale
    simpa [mul_comm] using hscale
  · rw [← hre]
    simp

/-- If a semigroup-group positive-definite function is already bounded by `1` and normalized at
the origin, then applying the explicit normalization preserves the same bound. -/
theorem norm_normalize_apply_le_one_of_norm_le_one_of_map_zero_eq_one
    (hF0 : F (0, 0) = 1) (hbound : ∀ p : ℝ≥0 × V, ‖F p‖ ≤ 1) (p : ℝ≥0 × V) :
    ‖(((F (0, 0)).re)⁻¹ : ℂ) * F p‖ ≤ 1 := by
  simpa [normalize_apply_of_map_zero_eq_one (F := F) hF0 p] using hbound p

end Pointwise

end IsSemigroupGroupPD

end TauCeti
