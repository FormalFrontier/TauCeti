/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The two dilation laws and `Mathlib.Analysis.Calculus.ContDiff.Defs` are imported publicly:
-- between them they supply every notion appearing in the statements below (`eLpNorm`, `fderiv`,
-- the Haar measure and `EuclideanSpace` API, and `ContDiff`).
public import TauCeti.Analysis.Sobolev.Dilation
public import Mathlib.Analysis.Calculus.ContDiff.Defs
-- The remaining three imports are private: the bump function, the compact-support `MemLp`
-- criterion and the open-positivity of Haar measure are used only to build the counterexample,
-- so downstream importers do not pay for them.
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The Poincaré inequality fails on the whole space

A Poincaré inequality bounds the `Lᵖ` seminorm of a function by the `Lᵖ` seminorm of its
derivative, `‖u‖_p ≤ C ‖Du‖_p`. Mathlib proves such an estimate in
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, for `1 ≤ p < n` and functions supported in a *fixed
bounded* set `s`, with the explicit `s`-dependent constant
`MeasureTheory.eLpNormLESNormFDerivOfLeConst ℝ μ s p p`. The PDE roadmap asks for the companion
fact that pins the role of that hypothesis: on the whole of a finite-dimensional space no single
constant works for *all* compactly supported functions, so the boundedness of the support is
load-bearing rather than an artefact of the proof.

The obstruction is scaling. Dilating the variable by `r > 0` multiplies `‖u‖_p` by `r ^ (n / p)`
and `‖Du‖_p` by `r ^ (n / p - 1)` (`TauCeti.eLpNorm_comp_inv_smul` and
`TauCeti.eLpNorm_fderiv_comp_inv_smul`), so applying a putative inequality to the dilates of one
fixed bump function forces `‖u‖_p ≤ C r⁻¹ ‖Du‖_p` for every `r`, and letting `r → ∞` makes the
bump's own seminorm vanish. Note that the two hypotheses `p ≠ 0` and `p ≠ ∞` are the only ones
needed: the failure is not confined to the subcritical range `p < n` in which the positive
result lives.

`TauCeti.Analysis.Sobolev.Poincare.Slab` proves the matching positive statement: bounding the
support in a single direction already suffices, and the constant is then the width of the slab.

## Main declarations

* `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`: no constant `C` satisfies
  `‖u‖_p ≤ C ‖Du‖_p` for all compactly supported `C¹` functions on a finite-dimensional real
  normed space with an additive Haar measure.
* `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv_euclideanSpace`: the roadmap's
  `ℝⁿ` form, for Lebesgue measure on `EuclideanSpace ℝ (Fin n)`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Module Topology
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A bump function has nonzero `p`-seminorm: it is continuous and equal to `1` at the origin. -/
private theorem eLpNorm_contDiffBump_ne_zero {p : ℝ≥0∞} (hp₀ : p ≠ 0)
    (φ : ContDiffBump (0 : E)) : eLpNorm (φ : E → ℝ) p μ ≠ 0 := by
  intro h
  have hcont : Continuous (φ : E → ℝ) := (φ.contDiff (n := 1)).continuous
  have hae := (eLpNorm_eq_zero_iff hcont.aestronglyMeasurable hp₀).1 h
  have hzero : (φ : E → ℝ) = 0 :=
    (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
  have h0 : (φ : E → ℝ) 0 = 1 := φ.one_of_mem_closedBall (by simp [φ.rIn_pos.le])
  rw [hzero] at h0
  norm_num at h0

/-- Testing a putative Poincaré inequality on the dilate of a bump by `r` and cancelling the common
factor `r ^ (n / p)` leaves a bound on the bump's own seminorm that degrades like `r⁻¹`. -/
private theorem eLpNorm_le_ofReal_inv_mul_of_forall {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (φ : ContDiffBump (0 : E)) {C : ℝ≥0}
    (hC : ∀ u : E → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p μ ≤ C * eLpNorm (fderiv ℝ u) p μ)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (φ : E → ℝ) p μ
      ≤ ENNReal.ofReal r⁻¹ * (C * eLpNorm (fderiv ℝ (φ : E → ℝ)) p μ) := by
  have hφ1 : ContDiff ℝ 1 (φ : E → ℝ) := φ.contDiff
  have h1 := hC (fun x => φ (r⁻¹ • x))
    (hφ1.comp (ContDiff.const_smul r⁻¹ (contDiff_id (𝕜 := ℝ) (E := E))))
    (φ.hasCompactSupport.comp_homeomorph (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))))
  rw [eLpNorm_comp_inv_smul μ _ hr hp₀ hp, eLpNorm_fderiv_comp_inv_smul μ _ hr hp₀ hp] at h1
  set s := ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) with hs_def
  have hs0 : s ≠ 0 := by
    rw [hs_def, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hsplit : ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal - 1))
      = s * ENNReal.ofReal r⁻¹ := by
    rw [hs_def, ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub hr, Real.rpow_one,
      div_eq_mul_inv]
  rw [hsplit] at h1
  refine (ENNReal.mul_le_mul_iff_right hs0 ENNReal.ofReal_ne_top).1 (h1.trans (le_of_eq ?_))
  ring

/-- **No Poincaré inequality holds on the whole space.** There is no constant `C` with
`‖u‖_p ≤ C ‖Du‖_p` for every compactly supported `C¹` function `u`, for any `0 < p < ∞`.

Compare `MeasureTheory.eLpNorm_le_eLpNorm_fderiv`, which supplies such a constant once every
`u` is supported in one fixed bounded set; the proof here shows that hypothesis cannot be
dropped. -/
theorem not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    ¬ ∃ C : ℝ≥0, ∀ u : E → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p μ ≤ C * eLpNorm (fderiv ℝ u) p μ := by
  rintro ⟨C, hC⟩
  -- Fix one bump function; every dilate of it is an admissible test function.
  set φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set D := eLpNorm (fderiv ℝ (φ : E → ℝ)) p μ with hD_def
  -- Its derivative is continuous with compact support, hence of finite seminorm.
  have hD : D ≠ ∞ :=
    (((φ.contDiff (n := 2)).continuous_fderiv (by norm_num)).memLp_of_hasCompactSupport
      (μ := μ) (p := p) (φ.hasCompactSupport.fderiv (𝕜 := ℝ))).eLpNorm_lt_top.ne
  -- Letting `r → ∞` forces the bump's own seminorm to vanish, a contradiction.
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal r⁻¹ * (C * D)) atTop (𝓝 (0 * (C * D))) :=
    ENNReal.Tendsto.mul_const
      (by simpa using ENNReal.tendsto_ofReal (tendsto_inv_atTop_zero (𝕜 := ℝ)))
      (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top hD))
  have hle : eLpNorm (φ : E → ℝ) p μ ≤ 0 * (C * D) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr using
      eLpNorm_le_ofReal_inv_mul_of_forall μ hp₀ hp φ hC hr
  rw [zero_mul, le_zero_iff] at hle
  exact eLpNorm_contDiffBump_ne_zero μ hp₀ φ hle

/-- The Poincaré inequality fails on `ℝⁿ` with Lebesgue measure: the roadmap's form of
`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`. -/
theorem not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv_euclideanSpace (n : ℕ) {p : ℝ≥0∞}
    (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    ¬ ∃ C : ℝ≥0, ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p volume ≤ C * eLpNorm (fderiv ℝ u) p volume :=
  not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv volume hp₀ hp

end TauCeti
