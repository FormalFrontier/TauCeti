/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.CuspCircle

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Complex.Periodic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The ceiling contour integral is a `q`-circle integral

The change of variables for the cusp term of the valence contour: along the truncation
ceiling the contour derivative is `1`, the `q`-parameter maps the ceiling onto the
`q`-circle of radius `e^{-2πH}`, and the logarithmic derivative of a width-`1` periodic
function factors through its cusp function — so the ceiling contour integral of the
logarithmic derivative equals the `q`-circle integral of the cusp function's logarithmic
derivative.

The same bridge serves the excised valence contour unchanged, because the excision never
fires on the ceiling: the excision centres of the corner computations lie on the unit circle,
so their heights are at most `1`, while the ceiling runs at height `H`. Once each centre
clears `ε` below the ceiling the excised ceiling integrand *is* the unexcised one, and the
ceiling still reads the cusp order.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_fdBoundarySegment5_eq_circleIntegral_logDeriv_cuspFunction`
  (the ceiling bridge).
* `TauCeti.ModularForm.not_exists_norm_fdBoundary_sub_le_of_mem_Icc_four_five` (the excision
  never fires on the ceiling) and
  `intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp`
  (same namespace; the fully qualified name does not fit the line limit — so the excised
  ceiling integral is still `2πi · ord_∞`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Seg5CuspIntegral.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex Function intervalIntegral MeasureTheory Set

open scoped Real

namespace TauCeti

namespace ModularForm

/-- The pointwise ceiling-integrand identification on the open ceiling: the chain rule
substitutes the cusp function along the `q`-parameter, and the affine angle map matches
the circle parametrization with Jacobian `2π`. -/
private lemma ceiling_integrand_eq {g : UpperHalfPlane → ℂ} {H : ℝ}
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) {t : ℝ} (hgt : 4 < t) :
    deriv (fdBoundary H) t • logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t) =
      (2 * π) • (deriv (circleMap 0 (fdBoundaryQRadius H)) (2 * π * t + -(9 * π)) •
        logDeriv (Function.Periodic.cuspFunction 1 (g ∘ UpperHalfPlane.ofComplex))
          (circleMap 0 (fdBoundaryQRadius H) (2 * π * t + -(9 * π)))) := by
  have hangle : 2 * Real.pi * (t - 9 / 2) = 2 * π * t + -(9 * π) := by ring
  have hqe : Function.Periodic.qParam 1 (fdBoundarySegment5 H t) =
      circleMap 0 (fdBoundaryQRadius H) (2 * π * t + -(9 * π)) := by
    rw [qParam_fdBoundarySegment5 H t, hangle]
  calc deriv (fdBoundary H) t • logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t)
      = logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundarySegment5 H t) := by
        rw [deriv_fdBoundary_of_gt_four hgt, one_smul, fdBoundary_of_gt_four hgt]
    _ = logDeriv (Function.Periodic.cuspFunction 1 (g ∘ UpperHalfPlane.ofComplex))
          (Function.Periodic.qParam 1 (fdBoundarySegment5 H t)) *
          deriv (Function.Periodic.qParam 1) (fdBoundarySegment5 H t) :=
        TauCeti.Periodic.logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam one_ne_zero
          hper (fdBoundarySegment5 H t)
    _ = logDeriv (Function.Periodic.cuspFunction 1 (g ∘ UpperHalfPlane.ofComplex))
          (circleMap 0 (fdBoundaryQRadius H) (2 * π * t + -(9 * π))) *
          (circleMap 0 (fdBoundaryQRadius H) (2 * π * t + -(9 * π)) *
            (2 * ↑π * Complex.I / (1 : ℝ))) := by
        rw [TauCeti.Periodic.deriv_qParam, hqe]
    _ = _ := by
        rw [deriv_circleMap, smul_eq_mul, Complex.real_smul]
        push_cast
        ring

/-- The ceiling contour integral of the logarithmic derivative of a width-`1` periodic
function on the upper half-plane is the `q`-circle integral of its cusp function's
logarithmic derivative: the contour derivative is `1` on the ceiling, the `q`-parameter
carries the ceiling onto the `q`-circle, and the logarithmic derivative factors through
the cusp function. -/
theorem intervalIntegral_fdBoundarySegment5_eq_circleIntegral_logDeriv_cuspFunction
    {g : UpperHalfPlane → ℂ} {H : ℝ}
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) :
    ∫ t in (4 : ℝ)..5,
        deriv (fdBoundary H) t • logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t) =
      circleIntegral (logDeriv (UpperHalfPlane.cuspFunction 1 g)) 0 (fdBoundaryQRadius H) := by
  set R := fdBoundaryQRadius H with hR
  set Lc := logDeriv (UpperHalfPlane.cuspFunction 1 g) with hLc
  have hcusp : UpperHalfPlane.cuspFunction 1 g =
      Function.Periodic.cuspFunction 1 (g ∘ UpperHalfPlane.ofComplex) := by
    simp [UpperHalfPlane.cuspFunction]
  -- the circle integrand is `2π`-periodic
  have hcper : Function.Periodic
      (fun θ ↦ deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ)) (2 * π) := fun θ ↦ by
    simp only []
    rw [TauCeti.Function.Periodic.deriv (periodic_circleMap 0 R) θ,
      periodic_circleMap 0 R θ]
  -- shift the circle integral to `[-π, π]`
  have h2π : -π + 2 * π = π := by ring
  have h0π : (0 : ℝ) + 2 * π = 2 * π := by ring
  have hshift : circleIntegral Lc 0 R = ∫ θ in (-π)..π,
      deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ) := by
    rw [circleIntegral, ← h0π, ← Function.Periodic.intervalIntegral_add_eq hcper (-π) 0,
      h2π]
  -- substitute the affine angle map `θ = 2π·t + -(9π)`
  have h4 : 2 * π * 4 + -(9 * π) = -π := by ring
  have h5 : 2 * π * 5 + -(9 * π) = π := by ring
  have hcov : (∫ θ in (-π)..π, deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ)) =
      (2 * π) • ∫ t in (4 : ℝ)..5,
        deriv (circleMap 0 R) (2 * π * t + -(9 * π)) •
          Lc (circleMap 0 R (2 * π * t + -(9 * π))) := by
    have h := intervalIntegral.smul_integral_comp_mul_add
      (f := fun θ ↦ deriv (circleMap 0 R) θ • Lc (circleMap 0 R θ))
      (2 * π) (-(9 * π)) (a := 4) (b := 5)
    rw [h4, h5] at h
    exact h.symm
  -- identify the substituted integrand with the contour integrand on the open ceiling
  rw [hshift, hcov, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun t ht ↦ ?_
  rw [hLc, hcusp, hR]
  exact ceiling_integrand_eq hper ht.1

/-- **The excision never fires on the ceiling.** The ceiling runs at height `H`, so a centre
whose height clears `ε` below it — `s.im + ε < H` — has no ceiling point within `ε`. This is
the exact condition; callers with centres on the unit circle get it from `ε < H - 1`. -/
theorem not_exists_norm_fdBoundary_sub_le_of_mem_Icc_four_five {H ε : ℝ} {S : Finset ℂ}
    (hlt : ∀ s ∈ S, s.im + ε < H) {t : ℝ} (ht : t ∈ Icc (4 : ℝ) 5) :
    ¬ ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε := by
  rintro ⟨s, hs, hle⟩
  have himle : |(fdBoundary H t - s).im| ≤ ‖fdBoundary H t - s‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, im_fdBoundarySegment5 H ht] at himle
  have : H - s.im ≤ ε := (le_abs_self _).trans (himle.trans hle)
  linarith [hlt s hs]

/-- **The excised ceiling integral is the plain one.** The excision never fires on the
ceiling, so the excised integrand agrees with the unexcised one there and the ceiling still
evaluates through the `q`-circle to `2πi · ord_∞`. -/
theorem intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp
    {g : UpperHalfPlane → ℂ} {H ε : ℝ} {S : Finset ℂ} (hlt : ∀ s ∈ S, s.im + ε < H)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 g) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      UpperHalfPlane.cuspFunction 1 g q ≠ 0) :
    ∫ t in (4 : ℝ)..5, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 g := by
  rw [intervalIntegral.integral_congr (g := fun t ↦ deriv (fdBoundary H) t •
        logDeriv (g ∘ UpperHalfPlane.ofComplex) (fdBoundary H t)) fun t ht ↦ ?_,
    (intervalIntegral_fdBoundarySegment5_eq_circleIntegral_logDeriv_cuspFunction hper).trans
      (circleIntegral_logDeriv_cuspFunction hga hgz)]
  rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)] at ht
  exact ite_eq_right (not_exists_norm_fdBoundary_sub_le_of_mem_Icc_four_five hlt ht)

end ModularForm

end TauCeti

end
