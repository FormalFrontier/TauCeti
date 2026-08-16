/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ArcPairing
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Ceiling.Bridge
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.VerticalCancel

import TauCeti.Analysis.Calculus.PeriodicDeriv


/-!
# The boundary contour integral of a level-one logarithmic derivative

The four boundary pieces assemble: the two verticals cancel by periodicity, the arc
collapses to its weight term, and the ceiling evaluates through the `q`-circle to the
cusp order — so the whole boundary contour integral of the logarithmic derivative is
`2πi · ord_∞ - k·(π/6)·i`. Under the `(2πi)⁻¹` normalization of the valence contour this
is `ord_∞ - k/12`.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_logDeriv_fdBoundary`: the assembled boundary
  integral.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex Function MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- **The boundary contour integral of a level-one logarithmic derivative**: the
verticals cancel by periodicity, the arc collapses to its weight term, and the ceiling
evaluates to the cusp order, so the whole contour integral is
`2πi · ord_∞ - k·(π/6)·i`. -/
theorem intervalIntegral_logDeriv_fdBoundary [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ}
    (hper : Function.Periodic (⇑f ∘ ofComplex) 1)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      UpperHalfPlane.cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 0 1)
    (hint12 : IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 1 2)
    (hint45 : IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 4 5) :
    ∫ t in (0 : ℝ)..5,
        deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        k * ((Real.pi / 6 : ℝ) * Complex.I) := by
  have hint23 := intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
    f hS hd hne hint12
  have hint34 := intervalIntegrable_deriv_smul_fdBoundarySegment4
    (TauCeti.Function.Periodic.logDeriv hper) hint01
  have hint13 := hint12.trans hint23
  have hint35 := hint34.trans hint45
  have hint15 := hint13.trans hint35
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 hint15,
    ← intervalIntegral.integral_add_adjacent_intervals hint13 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hint45,
    intervalIntegral_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc f hS hd hne hint12,
    intervalIntegral_fdBoundarySegment4_eq_neg_segment1 H
      (TauCeti.Function.Periodic.logDeriv hper),
    (intervalIntegral_fdBoundarySegment5_eq_circleIntegral_logDeriv_cuspFunction
      hper).trans (circleIntegral_logDeriv_cuspFunction hga hgz)]
  push_cast
  ring

end ModularForm

end TauCeti

end
