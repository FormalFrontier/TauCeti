/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Assembly

import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# The excised boundary contour integral of a level-one logarithmic derivative

`TauCeti.ModularForm.intervalIntegral_logDeriv_fdBoundary` assembles the boundary integral
for a form with no zeros on the contour. The valence formula needs the version that tolerates
them at the elliptic points `i` and `ρ`, which sit *on* the fundamental-domain boundary, so a
form vanishing there makes `logDeriv f` blow up on the contour itself. (Nonvanishing along the
ceiling is still required, through the `q`-disk hypothesis.) The device is `ε`-excision —
the integrand is replaced by `0` within `ε` of any excision centre — and this file assembles
the excised integral **at a fixed `ε`**, from integrability hypotheses it takes rather than
proves. Taking `ε → 0` and identifying the limit as a principal value is not done here.

The three pieces are already available and each already tolerates the excision: the verticals
cancel by periodicity (`intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1`), the
arc collapses to its weight term
(`two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`), and
the ceiling is untouched by the excision altogether
(`intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp`).

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_excised_logDeriv_fdBoundary`: the assembled excised
  boundary integral, `2πi · ord_∞ - (k/2) · ∫₁³ (excised logDeriv γ)`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Function MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- **The excised boundary contour integral of a level-one logarithmic derivative.** The
four pieces assemble exactly as they do without the excision: the verticals cancel, the arc
collapses to its weight term, and the ceiling reads the cusp order. What the excision buys is
zeros on the arc and at the elliptic boundary points, where the integrand is replaced by `0`
instead. It does not free the ceiling: `hgz` still asks `f` to be nonvanishing at every
nonzero point of the closed `q`-disk, the circle of which is the ceiling.

The statement is at a fixed `ε`, with integrability on `[0, 1]`, `[1, 2]` and `[4, 5]` assumed;
the remaining two pieces are derived by the reflections. Compare
`intervalIntegral_logDeriv_fdBoundary`, the unexcised assembly, whose arc term is the constant
`k·(π/6)·i`: here the arc term is `(k/2)` times the excised arc integral of the contour's own
logarithmic derivative, an `ε`-dependent quantity this theorem says nothing about the limit
of. -/
theorem intervalIntegral_excised_logDeriv_fdBoundary [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hlt : ∀ s ∈ S, s.im + ε < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 0 1)
    (hint12 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2)
    (hint45 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 4 5) :
    ∫ t in (0 : ℝ)..5, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t) := by
  -- On the unit circle inversion is conjugation, so the arc hypothesis already gives the
  -- vertical one: `-1 / s = -s⁻¹ = -conj s`.
  have hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S := fun s hs => by
    have h : -1 / s = -(starRingEnd ℂ) s := by
      rw [neg_div, one_div, Complex.inv_eq_conj (hnorm s hs)]
    exact h ▸ hinv s hs
  have hint23 := intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
    f hS hnorm hinv hd hne hint12
  have hint34 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 3 4 := by
    simpa only [smul_ite, smul_zero] using
      intervalIntegrable_excised_deriv_smul_fdBoundarySegment4
        (TauCeti.Function.Periodic.logDeriv hper) hrefl
        (by simpa only [smul_ite, smul_zero] using hint01)
  have hint13 := hint12.trans hint23
  have hint35 := hint34.trans hint45
  have hvert : (∫ t in (3 : ℝ)..4, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))) =
      -∫ t in (0 : ℝ)..1, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) := by
    simpa only [smul_ite, smul_zero] using
      intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1 H
        (TauCeti.Function.Periodic.logDeriv hper) hrefl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 (hint13.trans hint35),
    ← intervalIntegral.integral_add_adjacent_intervals hint13 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hint45,
    hvert,
    intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp
      hlt hper hga hgz]
  linear_combination
    two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
      f hS hnorm hinv hd hne hint12 / 2

end ModularForm

end TauCeti
