/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The vertical integrals of a periodic integrand cancel

The reflection `t ↦ 4 - t` carries the right vertical of the boundary contour onto the
left vertical through the translation `z ↦ z - 1`, reversing the orientation. For any
integrand `φ` of period `1` — the level-one situation, where `φ` is the logarithmic
derivative of the extension of a modular form — the left vertical contour integral of
`γ' • φ ∘ γ` is therefore the negative of the right one: the values are identified by
periodicity and the derivatives by the reflection, up to the orientation sign. The
statement is unconditional: the substitution and the interior congruence need no
integrability.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_fdBoundary_segment4_eq_neg_segment1`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`, the vertical
  cancellation) this file ports onto the current Mathlib pin.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace ModularForm

/-- The left vertical integral of a period-`1` integrand along the boundary contour is
the negative of the right vertical integral: the reflection `t ↦ 4 - t` carries the
right vertical onto the left through the translation `z ↦ z - 1`, which the periodicity
absorbs, and reverses the orientation. -/
theorem intervalIntegral_fdBoundary_segment4_eq_neg_segment1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (H : ℝ) {φ : ℂ → E}
    (hφ : Function.Periodic φ 1) :
    ∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t) =
      -∫ t in (0 : ℝ)..1, deriv (fdBoundary H) t • φ (fdBoundary H t) := by
  have hsub : (∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t)) =
      ∫ u in (0 : ℝ)..1, deriv (fdBoundary H) (4 - u) • φ (fdBoundary H (4 - u)) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
      (fun t ↦ deriv (fdBoundary H) t • φ (fdBoundary H t)) 4
    norm_num at h
    exact h.symm
  rw [hsub, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu ↦ ?_
  rw [fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩,
    deriv_fdBoundary_four_sub_vertical H hu, hφ.sub_eq, neg_smul]

end ModularForm

end TauCeti

end
