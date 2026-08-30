/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Characteristic function of the gamma distribution

This file computes the characteristic function of a gamma law with positive shape `a` and
positive rate `r`:

`charFun (gammaMeasure a r) t = (1 - I * t / r) ^ (-a)`.

The power is the principal complex power. Its base stays in the open right half-plane, so there
is no branch-cut ambiguity. The proof analytically continues the moment-generating function from
the real interval `(-∞, r)` to the half-plane `re z < r`, then evaluates the continuation on the
imaginary axis.

## Main result

* `TauCeti.charFun_gammaMeasure` gives the characteristic function of the gamma law.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 1, **Gamma**.
* The identity-theorem and real-to-complex sequence argument adapts
  `ProbabilityTheory.eqOn_complexMGF_of_mgf'` from
  `Mathlib/Probability/Moments/ComplexMGF.lean`.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal Topology

namespace TauCeti

variable {a r : ℝ}

/-- The holomorphic extension of the gamma moment-generating function to `re z < r`. -/
private def gammaComplexMGF (a r : ℝ) (z : ℂ) : ℂ :=
  (1 - z / r) ^ (-(a : ℂ))

/-- The proposed complex moment-generating function is analytic on the half-plane `re z < r`.

On this half-plane the base `1 - z / r` has positive real part, so it lies in the slit plane on
which the principal complex power is holomorphic. -/
private theorem analyticOnNhd_gammaComplexMGF (hr : 0 < r) :
    AnalyticOnNhd ℂ (gammaComplexMGF a r) {z : ℂ | z.re < r} := by
  unfold gammaComplexMGF
  have hdiff : DifferentiableOn ℂ (fun z : ℂ ↦ 1 - z / r) {z : ℂ | z.re < r} := by
    fun_prop
  refine (hdiff.cpow_const ?_).analyticOnNhd (isOpen_lt Complex.continuous_re continuous_const)
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.sub_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  have hzr : z.re / r < 1 := (div_lt_one hr).2 hz
  convert sub_pos.mpr hzr using 1
  field_simp
  ring

/-- On the real part of its domain, `gammaComplexMGF` agrees with the gamma mgf. -/
private theorem gammaComplexMGF_ofReal (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    gammaComplexMGF a r (t : ℂ) = mgf id (gammaMeasure a r) t := by
  rw [mgf_id_gammaMeasure ha hr ht]
  have hbase : 0 ≤ 1 - t / r := (sub_pos.mpr ((div_lt_one hr).2 ht)).le
  rw [gammaComplexMGF, Complex.ofReal_cpow hbase]
  push_cast
  rfl

/-- The characteristic function of a gamma law with positive shape `a` and positive rate `r`.

The right-hand side uses the principal complex power. Since `r > 0`, the real part of
`1 - I * t / r` is `1`, so its value never meets the branch cut. -/
@[simp]
theorem charFun_gammaMeasure (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    charFun (gammaMeasure a r) t =
      (1 - Complex.I * t / r) ^ (-(a : ℂ)) := by
  let U : Set ℂ := {z | z.re < r}
  have hAnalyticMGF : AnalyticOnNhd ℂ (complexMGF id (gammaMeasure a r)) U := by
    simpa only [U, integrableExpSet_id_gammaMeasure ha hr, interior_Iio, Set.mem_ofPred_eq,
      mem_Iio] using
        (analyticOnNhd_complexMGF (X := id) (μ := gammaMeasure a r))
  have hAnalyticFormula : AnalyticOnNhd ℂ (gammaComplexMGF a r) U := by
    simpa only [U] using analyticOnNhd_gammaComplexMGF (a := a) hr
  have hUPreconnected : IsPreconnected U := by
    -- Expose the literal linear preimage; `simp` does not reduce `Complex.reLm z` to `z.re`.
    change IsPreconnected (Complex.reLm ⁻¹' Iio r)
    exact ((convex_Iio r).linear_preimage Complex.reLm).isPreconnected
  have hzeroU : (0 : ℂ) ∈ U := by
    simpa only [U, Set.mem_ofPred_eq, Complex.zero_re] using hr
  have hReal : ∃ᶠ (x : ℝ) in nhdsWithin 0 {0}ᶜ,
      complexMGF id (gammaMeasure a r) x = gammaComplexMGF a r x := by
    have hEventually : ∀ᶠ (x : ℝ) in nhdsWithin 0 {0}ᶜ,
        complexMGF id (gammaMeasure a r) x = gammaComplexMGF a r x := by
      have hxlt : ∀ᶠ x : ℝ in nhdsWithin 0 {0}ᶜ, x < r :=
        nhdsWithin_le_nhds (Iio_mem_nhds hr)
      filter_upwards [hxlt] with x hx
      rw [complexMGF_ofReal, gammaComplexMGF_ofReal ha hr hx]
    exact hEventually.frequently
  have hComplex : ∃ᶠ (z : ℂ) in nhdsWithin 0 {0}ᶜ,
      complexMGF id (gammaMeasure a r) z = gammaComplexMGF a r z := by
    rw [frequently_iff_seq_forall] at hReal ⊢
    obtain ⟨xs, hxs, heq⟩ := hReal
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hxs ⊢
      constructor
      · convert Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1 using 1 <;>
          simp [Function.comp_def]
      · simpa using hxs.2
    · simpa using heq n
  have hEq : Set.EqOn (complexMGF id (gammaMeasure a r)) (gammaComplexMGF a r) U :=
    hAnalyticMGF.eqOn_of_preconnected_of_frequently_eq hAnalyticFormula hUPreconnected hzeroU
      hComplex
  have hit : ((t : ℂ) * Complex.I) ∈ U := by
    simpa only [U, Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero] using hr
  have := hEq hit
  rw [complexMGF_id_mul_I] at this
  simpa only [gammaComplexMGF, mul_comm] using this

end TauCeti
