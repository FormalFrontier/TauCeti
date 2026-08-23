/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
-- `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` is imported privately: it supplies
-- `not_integrableOn_Ioi_rpow`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioi`.
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- `Mathlib.Analysis.SpecialFunctions.Integrals.Basic` is imported privately: it supplies the
-- interval integral of `t ^ s`, used only inside the proof of
-- `TauCeti.lintegral_ofReal_rpow_Ioo`.
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lower integrals of a real power, and the layer cake formula in `ℝ≥0∞`

This file collects the two lower integrals of `t ↦ t ^ s` on a half-line that the real
interpolation method needs, and uses them to transport Mathlib's layer cake formula from
real-valued to `ℝ≥0∞`-valued functions.

For `-1 < s` the function `t ↦ t ^ s` is integrable near `0` and not integrable near `∞`, and the
two computations below are the two halves of that dichotomy:
`TauCeti.lintegral_ofReal_rpow_Ioo` evaluates `∫⁻ t in (0, a), t ^ s` to the expected
antiderivative for such an `s`, while `TauCeti.lintegral_ofReal_rpow_Ioi` records that
`∫⁻ t in (0, ∞), t ^ s` diverges — the latter for *every* exponent `s`, since a power that is
integrable at the origin is not integrable at infinity and conversely.

`TauCeti.lintegral_indicator_ofReal_rpow_Ioi` packages the two together as the single formula the
real interpolation method uses: the integral over `(0, ∞)` of `t ^ s` cut off at the height where
`c * t` reaches a threshold `a : ℝ≥0∞`, which is the finite antiderivative when `a` is finite and
`∞` when it is not.

The layer cake formula `∫⁻ u ^ p = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)` is in Mathlib as
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, but only for a nonnegative *real-valued*
`u`. Analysis in `ℝ≥0∞` — where the operators of interpolation theory naturally land, since a
supremum of averages such as the Hardy–Littlewood maximal function is defined without any
finiteness hypothesis — needs the version for `u : β → ℝ≥0∞`, which is
`TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul` below. The superlevel sets there are cut
at the `ℝ≥0∞`-valued threshold `ENNReal.ofReal t`, which is what distinguishes the statement from
Mathlib's.

The passage between the two is by `ENNReal.toReal`, which is faithful exactly where `u` is finite.
Where `u = ∞` on a set of positive measure both sides are `∞`: the left because `u ^ p = ∞`
there, and the right because every superlevel set then has measure at least that of `{u = ∞}`,
and `∫⁻ t in (0, ∞), t ^ (p - 1)` diverges. That is where `TauCeti.lintegral_ofReal_rpow_Ioi` is
used, and it is why the statement needs no finiteness hypothesis on `u`.

## Main declarations

* `TauCeti.lintegral_ofReal_rpow_Ioo`: `∫⁻ t in (0, a), t ^ s = a ^ (s + 1) / (s + 1)` for
  `-1 < s` and `0 ≤ a`.
* `TauCeti.lintegral_ofReal_rpow_Ioi`: `∫⁻ t in (0, ∞), t ^ s = ∞`, for every `s`.
* `TauCeti.lintegral_indicator_ofReal_rpow_Ioi`: the same integral truncated at the height where
  `c * t` reaches `a : ℝ≥0∞`, evaluated to `c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.
* `TauCeti.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul`: the layer cake formula for an
  `ℝ≥0∞`-valued function.

## References

* L. Grafakos, *Classical Fourier Analysis*, Proposition 1.1.4.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {s : ℝ}

/-- The lower integral of `t ^ s` over a bounded interval `(0, a)`, for `-1 < s` and `0 ≤ a`: the
power is integrable at the origin and the value is the expected antiderivative.

Nonnegativity of `a` is needed: for `a < 0` the interval is empty while `a ^ (s + 1)`, a real power
at a negative base, need not vanish. -/
theorem lintegral_ofReal_rpow_Ioo (hs : -1 < s) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (a ^ (s + 1) / (s + 1)) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ s) (Ioo 0 a) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hs
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at h
    exact h.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le s
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ha, integral_rpow (Or.inl hs), Real.zero_rpow hs1.ne',
    sub_zero]

/-- The lower integral of `t ^ s` over `(0, ∞)` diverges, for every exponent `s`: the power fails
to be integrable at the origin or at infinity, according as `s ≤ -1` or `-1 < s`. -/
theorem lintegral_ofReal_rpow_Ioi (s : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ s) = ∞ := by
  by_contra hne
  have hmeas : Measurable fun t : ℝ => t ^ s := measurable_id.pow measurable_const
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => t ^ s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt ht) s
  exact not_integrableOn_Ioi_rpow s
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hne)⟩

/-- **A finite threshold on `c * t` cuts `(0, ∞)` down to a bounded interval.** For `0 < c` and
`a ≠ ∞`, the indicator of `{t | ENNReal.ofReal (c * t) < a}` agrees at every positive `t` with the
indicator of `(0, a.toReal / c)`, whatever the integrand. -/
private theorem indicator_ofReal_mul_lt_eq_indicator_Ioo {a : ℝ≥0∞} (ha : a ≠ ∞) {c : ℝ}
    (hc : 0 < c) (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator f t =
      (Ioo (0 : ℝ) (a.toReal / c)).indicator f t := by
  have ht' : (0 : ℝ) < t := ht
  have hiff : t ∈ {t : ℝ | ENNReal.ofReal (c * t) < a} ↔ t ∈ Ioo (0 : ℝ) (a.toReal / c) := by
    rw [Set.mem_ofPred, Set.mem_Ioo, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ha,
      lt_div_iff₀ hc, mul_comm c t]
    exact ⟨fun h => ⟨ht', h⟩, fun h => h.2⟩
  by_cases hmem : t ∈ Ioo (0 : ℝ) (a.toReal / c)
  · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]

/-- The lower integral of `t ^ s` over `(0, ∞)`, truncated at the height where `c * t` reaches a
threshold `a : ℝ≥0∞`: for `-1 < s` and `0 < c`,

`∫⁻ t in (0, ∞), [c * t < a] * t ^ s = c ^ (-(s + 1)) / (s + 1) * a ^ (s + 1)`.

For a finite `a` the cut-off makes this the integral over `(0, a / c)` evaluated by
`TauCeti.lintegral_ofReal_rpow_Ioo`; for `a = ∞` the cut-off is vacuous and both sides are `∞`, by
`TauCeti.lintegral_ofReal_rpow_Ioi`. This is the inner integral of the real interpolation method,
where `a` is the value of the function being interpolated at a point. -/
theorem lintegral_indicator_ofReal_rpow_Ioi (hs : -1 < s) {c : ℝ} (hc : 0 < c) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ),
        {t : ℝ | ENNReal.ofReal (c * t) < a}.indicator (fun t => ENNReal.ofReal (t ^ s)) t =
      ENNReal.ofReal (c ^ (-(s + 1)) / (s + 1)) * a ^ (s + 1) := by
  have hs1 : (0 : ℝ) < s + 1 := by linarith
  have hconst : (0 : ℝ) < c ^ (-(s + 1)) / (s + 1) := by positivity
  rcases eq_or_ne a ∞ with rfl | ha
  · -- The cut-off is vacuous and the integral diverges.
    have hmem : ∀ t : ℝ, t ∈ {t : ℝ | ENNReal.ofReal (c * t) < ∞} := fun t =>
      Set.mem_ofPred.2 ENNReal.ofReal_lt_top
    rw [setLIntegral_congr_fun measurableSet_Ioi
        (fun t _ => Set.indicator_of_mem (hmem t) _),
      lintegral_ofReal_rpow_Ioi, ENNReal.top_rpow_of_pos hs1,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hconst).ne']
  rcases eq_or_ne a 0 with rfl | ha0
  · -- The cut-off is empty and both sides vanish.
    simp [ENNReal.zero_rpow_of_pos hs1]
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (fun t ht => indicator_ofReal_mul_lt_eq_indicator_Ioo ha hc _ ht)]
  -- abbreviate only now: `set` folds `a.toReal`, which the cut-off lemma above spells out
  set b : ℝ := a.toReal
  have hb0 : 0 < b := ENNReal.toReal_pos ha0 ha
  have hab : a = ENNReal.ofReal b := (ENNReal.ofReal_toReal ha).symm
  -- The elementary real identity behind the constant `c ^ (-(s + 1))`.
  have hreal : (b / c) ^ (s + 1) / (s + 1) = c ^ (-(s + 1)) / (s + 1) * b ^ (s + 1) := by
    have hcp : c ^ (s + 1) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    rw [Real.div_rpow hb0.le hc.le, Real.rpow_neg hc.le]
    field_simp
  rw [lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_self_of_subset_left Ioo_subset_Ioi_self,
    lintegral_ofReal_rpow_Ioo hs (by positivity), hab,
    ENNReal.ofReal_rpow_of_nonneg hb0.le hs1.le, ← ENNReal.ofReal_mul hconst.le, hreal]

variable {β : Type*} [MeasurableSpace β]

/-- **The layer cake formula** for an `ℝ≥0∞`-valued function: for `0 < p`,

`∫⁻ u ^ p ∂ν = p * ∫⁻ t in (0, ∞), ν {u > t} * t ^ (p - 1)`,

where the superlevel set is cut at the threshold `ENNReal.ofReal t`.

This is `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` for a function that is allowed to
take the value `∞`; no finiteness hypothesis is needed, because both sides are `∞` as soon as
`{u = ∞}` has positive measure. -/
theorem lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul (ν : Measure β) {u : β → ℝ≥0∞}
    (hu : AEMeasurable u ν) {p : ℝ} (hp : 0 < p) :
    ∫⁻ y, u y ^ p ∂ν = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} * ENNReal.ofReal (t ^ (p - 1)) := by
  rcases eq_or_ne (ν {y | u y = ∞}) 0 with hnull | hnull
  · -- `u` is finite almost everywhere, so `ENNReal.toReal` transports Mathlib's formula.
    have hfin : ∀ᵐ y ∂ν, u y ≠ ∞ := by rw [ae_iff]; simpa using hnull
    have hg : AEMeasurable (fun y => (u y).toReal) ν := hu.ennreal_toReal
    have hnn : 0 ≤ᵐ[ν] fun y => (u y).toReal := .of_forall fun _ => ENNReal.toReal_nonneg
    have hL : ∫⁻ y, u y ^ p ∂ν = ∫⁻ y, ENNReal.ofReal ((u y).toReal ^ p) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hfin] with y hy
      rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal hy]
    rw [hL, lintegral_rpow_eq_lintegral_meas_lt_mul ν hnn hg hp]
    refine congrArg _ (setLIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg₂ _ ?_ rfl)
    refine measure_congr ?_
    filter_upwards [hfin] with y hy
    exact propext (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hy).symm
  · -- `u = ∞` on a set of positive measure: both sides are `∞`.
    have hL : ∫⁻ y, u y ^ p ∂ν = ∞ := by
      have hlevel : {y | u y ^ p = ∞} = {y | u y = ∞} :=
        Set.ext fun y => ENNReal.rpow_eq_top_iff_of_pos hp
      refine lintegral_eq_top_of_measure_eq_top_ne_zero (hu.pow_const p) ?_
      rwa [hlevel]
    have hR : ∫⁻ t in Ioi (0 : ℝ), ν {y | ENNReal.ofReal t < u y} *
        ENNReal.ofReal (t ^ (p - 1)) = ∞ := by
      have hsub : ∀ {t : ℝ}, {y | u y = ∞} ⊆ {y | ENNReal.ofReal t < u y} := by
        intro t y (hy : u y = ∞)
        rw [Set.mem_ofPred_eq, hy]
        exact ENNReal.ofReal_lt_top
      refine top_le_iff.1 ?_
      calc (∞ : ℝ≥0∞)
          = ν {y | u y = ∞} * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1)) := by
            rw [lintegral_ofReal_rpow_Ioi (p - 1), ENNReal.mul_top hnull]
        _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | u y = ∞} * ENNReal.ofReal (t ^ (p - 1)) :=
            (lintegral_const_mul _ ((measurable_id.pow measurable_const).ennreal_ofReal)).symm
        _ ≤ _ := lintegral_mono fun t => mul_le_mul_left (measure_mono hsub) _
    rw [hL, hR, ENNReal.mul_top (ENNReal.ofReal_pos.2 hp).ne']

end TauCeti
