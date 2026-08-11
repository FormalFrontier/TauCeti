/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.ExcisionMeasure
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The excision leaves the arc's full length in the limit

The valence formula integrates over the fundamental-domain boundary with the integrand excised
within `ε` of the elliptic points. On the arc the excised integral turns out to be a constant
multiple of the *length* of the surviving parameter set, so its `ε → 0` limit is governed by
that length alone.

This file supplies both halves. The arc runs once around a `π/3` sector of the unit circle, so it
meets each excision centre at most once (`injOn_fdBoundary_arc`), and
`TauCeti.Contour.tendsto_intervalIntegral_excisionIndicator` applies with the whole length `2`.
The constant is the contour's own logarithmic derivative, which on the arc is `(π/6)·I`
(`logDeriv_fdBoundary_arc`), so the excised integral tends to `(π/3)·I`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development; this file adapts the arc-specific half of
  `ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`
  (`arc_preimage_subsingleton` and the specialisation of `arc_non_excluded_measure_tendsto`)
  onto the current Mathlib pin.

## Main results

* `TauCeti.ModularForm.tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc`: the surviving
  length of `[1, 3]` tends to `2` as `ε → 0⁺`.
* `TauCeti.ModularForm.intervalIntegral_excised_logDeriv_fdBoundary_arc`: at a fixed `ε`, the
  excised arc integral of `logDeriv (fdBoundary H)` is `(π/6)·I` times the surviving length.
* `TauCeti.ModularForm.tendsto_intervalIntegral_excised_logDeriv_fdBoundary_arc`: hence it tends
  to `(π/3)·I`.
-/

public section

open Filter Set Topology

namespace TauCeti

namespace ModularForm

/-- **The excision leaves the arc's full length in the limit.** Deleting from `[1, 3]` the times
at which the boundary comes within `ε` of one of finitely many centres costs no length as
`ε → 0⁺`: the surviving length tends to `2`. -/
theorem tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc (H : ℝ) (S : Finset ℂ) :
    Tendsto (fun ε => ∫ t in (1 : ℝ)..3,
        if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℝ) else 1) (𝓝[>] 0) (𝓝 2) := by
  have h := Contour.tendsto_intervalIntegral_excisionIndicator (continuous_fdBoundary H).measurable
    (by norm_num : (1 : ℝ) ≤ 3) S
    (Contour.measure_setOf_mem_eq_zero_of_injOn (injOn_fdBoundary_arc H) S)
  norm_num at h
  exact h

/-- **The excised arc integral of the contour's own logarithmic derivative.** On the arc
`logDeriv (fdBoundary H)` is the constant `(π/6)·I` (`logDeriv_fdBoundary_arc`), so the excised
integral is that constant times the surviving length. -/
theorem intervalIntegral_excised_logDeriv_fdBoundary_arc (H : ℝ) (S : Finset ℂ) (ε : ℝ) :
    (∫ t in (1 : ℝ)..3, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t) =
      ((Real.pi / 6 : ℝ) * Complex.I) *
        (↑(∫ t in (1 : ℝ)..3, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℝ) else 1) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  rw [uIoo_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
  by_cases hb : ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε
  · simp [hb]
  · simp [hb, logDeriv_fdBoundary_arc ht]

/-- **The arc's excised logarithmic-derivative integral tends to `(π/3)·I`.** Combining the
constant value on the arc with the surviving length's limit `2`. -/
theorem tendsto_intervalIntegral_excised_logDeriv_fdBoundary_arc (H : ℝ) (S : Finset ℂ) :
    Tendsto (fun ε => ∫ t in (1 : ℝ)..3, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t)
      (𝓝[>] 0) (𝓝 ((Real.pi / 3 : ℝ) * Complex.I)) := by
  simp only [intervalIntegral_excised_logDeriv_fdBoundary_arc H S]
  have h := (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_intervalIntegral_excisionIndicator_fdBoundary_arc H S)
  -- `2` surviving units of length at `(π/6)·I` each.
  have hval : ((Real.pi / 6 : ℝ) : ℂ) * Complex.I * ((2 : ℝ) : ℂ)
      = ((Real.pi / 3 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  exact hval ▸ h.const_mul _


end ModularForm

end TauCeti
