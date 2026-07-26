/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Integral lemmas for completely monotone functions

Taylor-remainder sign bounds and finite- and improper-integral facts about completely monotone
functions.

These extend the object API in `CompletelyMonotone/Basic.lean` with the sign of the Taylor
integral remainder, the finite-interval integral-of-`(-f')` identity, and improper-integral facts
for the first derivative within `[0, ∞)`.

## Main declarations

* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_taylor_remainder_nonneg`: the Taylor integral
  remainder has sign `(-1)ⁿ`.
* `TauCeti.IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc`: every iterated derivative
  within `[0, ∞)` is continuous on a compact interval `[x, T] ⊆ [0, ∞)`.
* `TauCeti.IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub`: on a compact
  interval in `[0, ∞)`, the integral of `-f'` is the endpoint drop `f x - f T`.
* `TauCeti.IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one`: integrability and the
  improper integral of `-f'` on `(0, ∞)`, represented as `iteratedDerivWithin 1`.
* `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg`: the same
  improper integral from an arbitrary nonnegative endpoint, `∫ₓ^∞ (-f') = f x - L`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- For a completely monotone function the `n`-th iterated derivative within a compact interval
`[x, T]` agrees with the one taken within the half-line `[0, ∞)` at any strictly positive interior
point. Complete monotonicity supplies the local `ContDiffAt` hypothesis, and both sides reduce to
the unrestricted iterated derivative at `t`. -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_Icc_eq_Ici (hf : IsCompletelyMonotone f)
    {x T t : ℝ} {n : ℕ} (ht_pos : 0 < t) (ht : t ∈ Ioo x T) :
    iteratedDerivWithin n f (Icc x T) t = iteratedDerivWithin n f (Ici 0) t := by
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  have hxT : x < T := lt_trans ht.1 ht.2
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcont
        (Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
        (mem_Ici.mpr ht_pos.le)]

namespace IsCompletelyMonotone

/-- **CM sign of the Taylor remainder.** For a completely monotone function the Taylor
integral remainder `∫ₓᵀ (T-t)ⁿ⁻¹/(n-1)! · f⁽ⁿ⁾(t) dt` has sign `(-1)ⁿ`:
`0 ≤ (-1)ⁿ` times it. -/
lemma neg_one_pow_mul_taylor_remainder_nonneg (hf : IsCompletelyMonotone f) {x T : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hxT : x ≤ T) :
    0 ≤ (-1 : ℝ) ^ n * ∫ t in x..T,
      (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
      iteratedDerivWithin n f (Icc x T) t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_nonneg_of_ae_restrict hxT
  have hIoo : ∀ t ∈ Ioo x T, (0 : ℝ) ≤ ((-1 : ℝ) ^ n *
      ((↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
        iteratedDerivWithin n f (Icc x T) t)) := fun t ht =>
    calc (0 : ℝ) ≤ (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Icc x T) t) :=
          mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr ht.2.le) _))
            (by
              have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
              rw [hf.iteratedDerivWithin_Icc_eq_Ici ht_pos ht]
              exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht_pos.le)
      _ = _ := by ring
  have h_mem : ∀ᵐ t ∂volume.restrict (Icc x T), t ∈ Ioo x T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (Ioo_ae_eq_Icc (a := x) (b := T)).mono (fun t h ht => h.mpr ht)
  exact h_mem.mono fun t ht => by simp only [Pi.zero_apply]; exact hIoo t ht

end IsCompletelyMonotone

/-! ## Smoothness-index helpers -/

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-- Every iterated derivative within `[0, ∞)` of a completely monotone function is continuous on
the interval spanned by any two nonnegative endpoints. The endpoints need no ordering: `uIcc` is
the unordered interval, and `[0, ∞)` is order-connected. -/
lemma IsCompletelyMonotone.continuousOn_iteratedDerivWithin_uIcc (hcm : IsCompletelyMonotone f)
    (m : ℕ) {x T : ℝ} (hx : 0 ≤ x) (hT : 0 ≤ T) :
    ContinuousOn (iteratedDerivWithin m f (Ici 0)) (uIcc x T) :=
  (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top m)
    (uniqueDiffOn_Ici 0)).mono (ordConnected_Ici.uIcc_subset hx hT)

/-- On a compact interval in `[0, ∞)`, the integral of `-f'` for a completely monotone
function is the endpoint drop, with the derivative taken within `[0, ∞)`. -/
lemma IsCompletelyMonotone.integral_neg_iteratedDerivWithin_one_Ici_eq_sub
    (hcm : IsCompletelyMonotone f) {x T : ℝ} (hx : 0 ≤ x) (hxT : x ≤ T) :
    ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t = f x - f T := by
  by_cases h_eq : x = T
  · subst T
    simp
  have htransfer :
      ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t =
      ∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hxT] at ht
    have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
    exact congrArg Neg.neg (hcm.iteratedDerivWithin_Icc_eq_Ici ht_pos ht)
  rw [← htransfer]
  simpa [iteratedDerivWithin_one, intervalIntegral.integral_neg, neg_sub] using
    congrArg Neg.neg (intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
      ((hcm.contDiffOn.mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))).of_le (nat_le_top _)) hxT)

/-- `-f'` is integrable on `(0, ∞)` for a completely monotone function, where the derivative is
taken within the closed half-line `[0, ∞)`. -/
lemma IsCompletelyMonotone.neg_iteratedDerivWithin_one_integrableOn
    (hcm : IsCompletelyMonotone f) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  obtain ⟨L, hL, -⟩ := hcm.exists_nonneg_tendsto_atTop
  have hcont : ContinuousWithinAt f (Ici 0) 0 :=
    hcm.contDiffOn.continuousOn.continuousWithinAt self_mem_Ici
  have hderiv : ∀ t ∈ Ioi 0,
      HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t := by
    intro t ht
    exact hcm.hasDerivAt_iteratedDerivWithin_succ 0 ht
  have hneg : ∀ t ∈ Ioi 0, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos ht.le
  exact (integrableOn_Ioi_deriv_of_nonpos hcont hderiv hneg hL).neg

/-- The improper integral `∫ₓ^∞ (-f') dt = f x - L` from an arbitrary nonnegative endpoint `x`,
for a completely monotone function with limit `L` at infinity. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg
    (hcm : IsCompletelyMonotone f) {x : ℝ} (hx : 0 ≤ x) {L : ℝ}
    (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, -iteratedDerivWithin 1 f (Ici 0) t = f x - L := by
  have hcont : ContinuousWithinAt f (Ici x) x :=
    (hcm.contDiffOn.continuousOn.continuousWithinAt hx).mono (Ici_subset_Ici.mpr hx)
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt f (iteratedDerivWithin 1 f (Ici 0) t) t :=
    fun t ht => hcm.hasDerivAt_iteratedDerivWithin_succ 0 (hx.trans_lt ht)
  have hneg : ∀ t ∈ Ioi x, iteratedDerivWithin 1 f (Ici 0) t ≤ 0 :=
    fun t ht => hcm.iteratedDerivWithin_one_nonpos (hx.trans ht.le)
  have hFTC : ∫ t in Ioi x, iteratedDerivWithin 1 f (Ici 0) t = L - f x :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg hL
  rw [MeasureTheory.integral_neg, hFTC]
  ring

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for completely monotone functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_iteratedDerivWithin_one
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi 0, -iteratedDerivWithin 1 f (Ici 0) t = f 0 - L :=
  hcm.integral_Ioi_neg_iteratedDerivWithin_one_of_nonneg le_rfl hL

end TauCeti
