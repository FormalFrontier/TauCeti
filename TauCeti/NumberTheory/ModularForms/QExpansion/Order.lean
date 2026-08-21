/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Order
public import TauCeti.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.Periodic

/-!
# The order of a `q`-expansion under period rescaling

The order of the `q`-expansion of a periodic, bounded, holomorphic function on the upper
half-plane equals the analytic order of its `cuspFunction` at `0`; consequently, passing
from period `h` to period `m * h` multiplies the order by `m`. This is the vanishing-order
bookkeeping feeding the finite-index Sturm bound.

## Main declarations

* `TauCeti.qExpansion_order_eq_analyticOrderAt_cuspFunction`.
* `TauCeti.qExpansion_nat_mul_order`: `(qExpansion (m * h) g).order = (qExpansion h g).order * m`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic

open scoped ModularForm Topology Filter Manifold

namespace TauCeti

variable {h : ℝ}

/-- The order of the `q`-expansion equals the analytic order of the `cuspFunction` at `0`. -/
lemma qExpansion_order_eq_analyticOrderAt_cuspFunction {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    (qExpansion h f).order = analyticOrderAt (cuspFunction h f) 0 := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  refine ⟨fun H i hi ↦ ?_, fun H ↦ PowerSeries.nat_le_order _ _ fun i hi ↦ ?_⟩
  · have hcoeff : (qExpansion h f).coeff i = 0 :=
      PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (mod_cast hi) H)
    rw [qExpansion_coeff] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_left (inv_ne_zero (mod_cast Nat.factorial_ne_zero i))
  · rw [qExpansion_coeff, H i hi, mul_zero]

/-- The cusp function at period `m * h` agrees near `0` with the cusp function at period `h`
composed with the `m`-th power map. -/
lemma cuspFunction_nat_mul_eventuallyEq {g : ℍ → ℂ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    cuspFunction (m * h : ℝ) g =ᶠ[nhds 0] fun q : ℂ ↦ cuspFunction h g (q ^ m) := by
  have hmh : (0 : ℝ) < m * h := by positivity
  have hg_per_mh : Periodic (g ∘ ofComplex) (m * h : ℝ) := by simpa using hg_per.nat_mul m
  have hpow_cts : ContinuousAt (fun q : ℂ ↦ cuspFunction h g (q ^ m)) 0 :=
    (analyticAt_cuspFunction_zero hh hg_per hg_mdiff hg_bdd).continuousAt.comp_of_eq
      (by fun_prop) (zero_pow hm.ne')
  rw [← (analyticAt_cuspFunction_zero hmh hg_per_mh hg_mdiff
      hg_bdd).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hpow_cts,
    eventuallyEq_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq_lt hq_ne
  rw [mem_ball_zero_iff] at hq_lt
  set τ : ℍ := ⟨Periodic.invQParam ((m : ℝ) * h) q,
    Periodic.im_invQParam_pos_of_norm_lt_one hmh hq_lt hq_ne⟩
  have hτq : Periodic.qParam ((m : ℝ) * h) τ = q := Periodic.qParam_right_inv hmh.ne' hq_ne
  rw [← hτq, TauCeti.Periodic.qParam_nat_mul_pow hm.ne', eq_cuspFunction τ hmh.ne' hg_per_mh,
    eq_cuspFunction τ hh.ne' hg_per]

/-- The order of the `q`-expansion at period `m * h` is `m` times the order at period `h`. -/
lemma qExpansion_nat_mul_order {g : ℍ → ℂ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    (qExpansion (m * h : ℝ) g).order = (qExpansion h g).order * m := by
  have han : AnalyticAt ℂ (cuspFunction h g) 0 :=
    analyticAt_cuspFunction_zero hh hg_per hg_mdiff hg_bdd
  rw [qExpansion_order_eq_analyticOrderAt_cuspFunction han,
    qExpansion_order_eq_analyticOrderAt_cuspFunction (analyticAt_cuspFunction_zero
      (by positivity) (by simpa using hg_per.nat_mul m) hg_mdiff hg_bdd),
    analyticOrderAt_congr (cuspFunction_nat_mul_eventuallyEq hh hm hg_per hg_bdd hg_mdiff),
    TauCeti.analyticOrderAt_comp_pow_zero han hm]

/-- The order of the `q`-expansion at period `h` is at most its order at period `m * h`. -/
lemma qExpansion_order_le_qExpansion_nat_mul_order {g : ℍ → ℂ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hg_per : Periodic (g ∘ ofComplex) h) (hg_bdd : IsBoundedAtImInfty g) (hg_mdiff : MDiff g) :
    (qExpansion h g).order ≤ (qExpansion (m * h : ℝ) g).order :=
  (ENat.self_le_mul_right _ (mod_cast hm.ne')).trans
    (qExpansion_nat_mul_order hh hm hg_per hg_bdd hg_mdiff).ge

end TauCeti

end
