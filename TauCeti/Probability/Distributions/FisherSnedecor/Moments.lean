/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Moments of Fisher's F distribution

This file establishes the sharp first- and second-moment theory of the Fisher--Snedecor law:
the mean, the second raw moment, the variance, and the exact integrability thresholds `2 < n`
and `4 < n` at which the first two moments diverge.  These all come from a file-internal
computation of the natural moment of order `q`, which exists exactly when `2 * q < n` and is
then a quotient of beta functions.

## Main results

* `integrable_id_fisherSnedecorMeasure_iff` and `integrable_sq_fisherSnedecorMeasure_iff` give
  the two sharp integrability thresholds, hence also the divergence at and below them.
* `integral_id_fisherSnedecorMeasure` computes the mean.
* `integral_sq_fisherSnedecorMeasure` computes the second raw moment.
* `variance_id_fisherSnedecorMeasure` computes the variance.

The proof uses Euler's second beta integral for integrability and the beta pushforward
representation for the exact value.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {m n : ℝ}

private def fisherMomentKernel (m n q x : ℝ) : ℝ :=
  x ^ (m / 2 + q - 1) * (1 + x) ^ (-((m + n) / 2))

private lemma eventually_const_mul_rpow_le_fisherMomentKernel (hm : 0 < m) (hn : 0 < n)
    (q : ℝ) :
    ∀ᶠ x in atTop,
      (2 : ℝ) ^ (-((m + n) / 2)) * x ^ (q - n / 2 - 1) ≤
        fisherMomentKernel m n q x := by
  set s := (m + n) / 2
  set e := q - n / 2 - 1 with he
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hle : 1 + x ≤ 2 * x := by linarith
  have hpos1 : 0 < 1 + x := by linarith
  have hpos2 : 0 < 2 * x := by linarith
  have hs : 0 < s := by
    dsimp only [s]
    linarith
  have hpow : (2 * x) ^ (-s) ≤ (1 + x) ^ (-s) := by
    rw [Real.rpow_neg hpos2.le, Real.rpow_neg hpos1.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos1 s)
      (Real.rpow_le_rpow hpos1.le hle hs.le)
  have hmul : (2 * x) ^ (-s) = (2 : ℝ) ^ (-s) * x ^ (-s) := by
    rw [Real.mul_rpow (by positivity) hx0.le]
  have hexponent : m / 2 + q - 1 + (-s) = e := by
    dsimp only [s, e]
    ring
  have hxpow : x ^ (m / 2 + q - 1) * x ^ (-s) = x ^ e := by
    rw [← Real.rpow_add hx0, hexponent]
  calc
    (2 : ℝ) ^ (-((m + n) / 2)) * x ^ (q - n / 2 - 1) =
        x ^ (m / 2 + q - 1) * ((2 : ℝ) ^ (-s) * x ^ (-s)) := by
          rw [← hxpow]
          dsimp only [s, e]
          ring
    _ = x ^ (m / 2 + q - 1) * (2 * x) ^ (-s) := by rw [hmul]
    _ ≤ x ^ (m / 2 + q - 1) * (1 + x) ^ (-s) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
    _ = fisherMomentKernel m n q x := by simp [fisherMomentKernel, s]

private lemma not_integrableOn_fisherMomentKernel_of_le (hm : 0 < m) (hn : 0 < n)
    {q : ℝ} (hnq : n / 2 ≤ q) :
    ¬ IntegrableOn (fisherMomentKernel m n q) (Ioi (0 : ℝ)) := by
  intro h
  set s := (m + n) / 2
  set e := q - n / 2 - 1 with he
  have he1 : -1 ≤ e := by linarith
  have hbound := eventually_const_mul_rpow_le_fisherMomentKernel hm hn q
  have hIoi1 : IntegrableOn (fisherMomentKernel m n q) (Ioi (1 : ℝ)) :=
    h.mono_set fun x hx ↦ by simpa only [mem_Ioi] using lt_trans zero_lt_one hx
  obtain ⟨a0, ha0⟩ := eventually_atTop.mp hbound
  set a := max a0 1 with ha_def
  let f : ℝ → ℝ := fun x ↦ (2 : ℝ) ^ (-s) * x ^ e
  have ha : ∀ x : ℝ, a ≤ x → f x ≤ fisherMomentKernel m n q x := by
    intro x hx
    exact ha0 x (le_trans (le_max_left a0 1) hx)
  have hbounded : IntegrableOn f (Ioc (1 : ℝ) a) := by
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_compact isCompact_Icc |>.mono_set
      Ioc_subset_Icc_self
    intro x hx
    exact (Real.continuousAt_rpow_const x e
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1)))).continuousWithinAt
  have htail : IntegrableOn f (Ioi a) := by
    refine (hIoi1.mono_set fun x hx ↦ by
      have ha1 : 1 ≤ a := le_max_right _ _
      exact by simpa only [mem_Ioi] using lt_of_le_of_lt ha1 hx).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right a0 1) hx.le)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ha x hx.le
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hx0.le _)
  have hpow : IntegrableOn (fun x : ℝ ↦ x ^ e) (Ioi (1 : ℝ)) := by
    have hf : IntegrableOn f (Ioi (1 : ℝ)) := by
      rw [← Ioc_union_Ioi_eq_Ioi (le_max_right a0 1)]
      exact hbounded.union htail
    have hc : IsUnit ((2 : ℝ) ^ (-s)) :=
      isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
    simpa [f, IntegrableOn, integrable_const_mul_iff hc] using hf
  rw [integrableOn_Ioi_rpow_iff one_pos] at hpow
  linarith

private lemma integrableOn_fisherMomentKernel_iff (hm : 0 < m) (hn : 0 < n) (q : ℝ)
    (hq : 0 ≤ q) :
    IntegrableOn (fisherMomentKernel m n q) (Ioi (0 : ℝ)) ↔ q < n / 2 := by
  constructor
  · intro h
    exact lt_of_not_ge fun hnq ↦ not_integrableOn_fisherMomentKernel_of_le hm hn hnq h
  · intro hqn
    have ha : 0 < m / 2 + q := by linarith
    have hb : 0 < n / 2 - q := by linarith
    unfold fisherMomentKernel
    convert integrableOn_rpow_mul_one_add_rpow ha hb using 1
    ring_nf

private lemma integrable_fisherSnedecorMeasure_iff (f : ℝ → ℝ) :
    Integrable f (fisherSnedecorMeasure m n) ↔
      IntegrableOn (fun x ↦ f x * fisherSnedecorPDFReal m n x) (Ioi (0 : ℝ)) := by
  rw [fisherSnedecorMeasure_eq_withDensity, integrable_withDensity_iff
    (measurable_fisherSnedecorPDF m n) (ae_of_all _ fun x ↦ by
      rw [fisherSnedecorPDF_eq_ofReal]
      exact ENNReal.ofReal_lt_top)]
  simp_rw [toReal_fisherSnedecorPDF]
  have hzero : ∀ x ∉ Ioi (0 : ℝ), f x * fisherSnedecorPDFReal m n x = 0 := by
    intro x hx
    rw [fisherSnedecorPDFReal_of_nonpos (not_lt.mp hx), mul_zero]
  rw [← integrable_indicator_iff measurableSet_Ioi]
  apply integrable_congr
  filter_upwards with x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hzero x hx]

private lemma fisherMomentDensity_eq (hm : 0 < m) (hn : 0 < n) (q : ℕ) {x : ℝ}
    (hx : x ∈ Ioi (0 : ℝ)) :
    x ^ q * fisherSnedecorPDFReal m n x =
      (Real.Gamma ((m + n) / 2) /
          (Real.Gamma (m / 2) * Real.Gamma (n / 2)) * (m / n) ^ (m / 2)) *
        (x ^ (m / 2 + q - 1) * (1 + m * x / n) ^ (-((m + n) / 2))) := by
  rw [fisherSnedecorPDFReal_of_pos hm hn hx]
  have hx0 : 0 < x := hx
  have hpow : x ^ q * x ^ (m / 2 - 1) = x ^ (m / 2 + q - 1) := by
    rw [← Real.rpow_natCast x q, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [← hpow]
  ring

private lemma integrableOn_scaled_fisherMomentKernel_iff (hm : 0 < m) (hn : 0 < n)
    (q : ℕ) :
    IntegrableOn
        (fun x : ℝ ↦ x ^ (m / 2 + q - 1) *
          (1 + m * x / n) ^ (-((m + n) / 2))) (Ioi (0 : ℝ)) ↔
      (q : ℝ) < n / 2 := by
  let c : ℝ := m / n
  have hc : 0 < c := div_pos hm hn
  let C : ℝ := c ^ (m / 2 + q - 1)
  have hC : IsUnit C := isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos hc _).ne'
  have hcomp := integrableOn_Ioi_comp_mul_left_iff
    (fisherMomentKernel m n q) 0 hc
  have heq : EqOn (fun x : ℝ ↦ fisherMomentKernel m n q (c * x))
      (fun x ↦ C * (x ^ (m / 2 + q - 1) *
        (1 + m * x / n) ^ (-((m + n) / 2)))) (Ioi (0 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hscale : m * x / n = m / n * x := by ring
    dsimp only [fisherMomentKernel, c, C]
    calc
      (m / n * x) ^ (m / 2 + (q : ℝ) - 1) *
          (1 + m / n * x) ^ (-((m + n) / 2)) =
          ((m / n) ^ (m / 2 + (q : ℝ) - 1) *
            x ^ (m / 2 + (q : ℝ) - 1)) *
              (1 + m / n * x) ^ (-((m + n) / 2)) := by
            rw [Real.mul_rpow hc.le hx0.le]
      _ = (m / n) ^ (m / 2 + (q : ℝ) - 1) *
          (x ^ (m / 2 + (q : ℝ) - 1) *
            (1 + m * x / n) ^ (-((m + n) / 2))) := by
            rw [hscale]
            ring
  rw [mul_zero] at hcomp
  rw [← integrableOn_fisherMomentKernel_iff hm hn q (Nat.cast_nonneg q), ← hcomp]
  constructor
  · intro h
    have h' : IntegrableOn (fun x : ℝ ↦ C *
        (x ^ (m / 2 + q - 1) * (1 + m * x / n) ^ (-((m + n) / 2))))
        (Ioi (0 : ℝ)) := by
      simpa [IntegrableOn, integrable_const_mul_iff hC] using h
    exact h'.congr_fun heq.symm measurableSet_Ioi
  · intro h
    have h' : IntegrableOn (fun x : ℝ ↦ C *
        (x ^ (m / 2 + q - 1) * (1 + m * x / n) ^ (-((m + n) / 2))))
        (Ioi (0 : ℝ)) := h.congr_fun heq measurableSet_Ioi
    simpa [IntegrableOn, integrable_const_mul_iff hC] using h'

/-- A natural power is integrable under a valid Fisher--Snedecor law exactly when twice its
order is below the denominator degrees of freedom. -/
private theorem integrable_pow_fisherSnedecorMeasure_iff (hm : 0 < m) (hn : 0 < n) (q : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ q) (fisherSnedecorMeasure m n) ↔ 2 * q < n := by
  rw [integrable_fisherSnedecorMeasure_iff]
  have hC : IsUnit (Real.Gamma ((m + n) / 2) /
      (Real.Gamma (m / 2) * Real.Gamma (n / 2)) * (m / n) ^ (m / 2)) := by
    rw [isUnit_iff_ne_zero]
    positivity
  have heq : EqOn (fun x : ℝ ↦ x ^ q * fisherSnedecorPDFReal m n x)
      (fun x ↦ (Real.Gamma ((m + n) / 2) /
          (Real.Gamma (m / 2) * Real.Gamma (n / 2)) * (m / n) ^ (m / 2)) *
        (x ^ (m / 2 + q - 1) * (1 + m * x / n) ^ (-((m + n) / 2))))
      (Ioi (0 : ℝ)) := fun _ hx ↦ fisherMomentDensity_eq hm hn q hx
  constructor
  · intro h
    have h' := h.congr_fun heq measurableSet_Ioi
    have hk : IntegrableOn
        (fun x : ℝ ↦ x ^ (m / 2 + q - 1) *
          (1 + m * x / n) ^ (-((m + n) / 2))) (Ioi (0 : ℝ)) := by
      simpa [IntegrableOn, integrable_const_mul_iff hC] using h'
    rw [integrableOn_scaled_fisherMomentKernel_iff hm hn q] at hk
    exact by linarith
  · intro h
    have hq : (q : ℝ) < n / 2 := by linarith
    have hk := (integrableOn_scaled_fisherMomentKernel_iff hm hn q).2 hq
    have h' : IntegrableOn (fun x ↦
        (Real.Gamma ((m + n) / 2) /
          (Real.Gamma (m / 2) * Real.Gamma (n / 2)) * (m / n) ^ (m / 2)) *
        (x ^ (m / 2 + q - 1) * (1 + m * x / n) ^ (-((m + n) / 2))))
        (Ioi (0 : ℝ)) := by
      simpa [IntegrableOn, integrable_const_mul_iff hC] using hk
    exact h'.congr_fun heq.symm measurableSet_Ioi

/-- The identity is integrable under a valid Fisher--Snedecor law exactly above two denominator
degrees of freedom. -/
@[simp]
theorem integrable_id_fisherSnedecorMeasure_iff (hm : 0 < m) (hn : 0 < n) :
    Integrable id (fisherSnedecorMeasure m n) ↔ 2 < n := by
  have h := integrable_pow_fisherSnedecorMeasure_iff hm hn 1
  norm_num at h
  have hid : id = fun x : ℝ ↦ x := rfl
  rw [hid]
  exact h

/-- Squaring is integrable under a valid Fisher--Snedecor law exactly above four denominator
degrees of freedom. -/
theorem integrable_sq_fisherSnedecorMeasure_iff (hm : 0 < m) (hn : 0 < n) :
    Integrable (fun x : ℝ ↦ x ^ 2) (fisherSnedecorMeasure m n) ↔ 4 < n := by
  have h := integrable_pow_fisherSnedecorMeasure_iff hm hn 2
  norm_num at h
  exact h

private lemma betaMomentIntegrand_eq (q : ℕ) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal (m / 2) (n / 2) u * fisherSnedecorMap m n u ^ q =
      (n / m) ^ q / beta (m / 2) (n / 2) *
        (u ^ (m / 2 + q - 1) * (1 - u) ^ (n / 2 - q - 1)) := by
  rw [betaPDFReal, ite_eq_left ⟨hu.1, hu.2⟩, fisherSnedecorMap_def]
  have hu0 : 0 < u := hu.1
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hratio : ((n / m) * u / (1 - u)) ^ q =
      (n / m) ^ q * u ^ q * ((1 - u) ^ q)⁻¹ := by
    rw [div_pow, mul_pow, div_eq_mul_inv]
  have hpowu : u ^ (m / 2 - 1) * u ^ (q : ℝ) = u ^ (m / 2 + q - 1) := by
    rw [← Real.rpow_add hu0]
    congr 1
    ring
  have hpowv : (1 - u) ^ (n / 2 - 1) * (1 - u) ^ (-(q : ℝ)) =
      (1 - u) ^ (n / 2 - q - 1) := by
    rw [← Real.rpow_add h1u]
    congr 1
    ring
  rw [hratio, ← Real.rpow_natCast u q, ← Real.rpow_natCast (1 - u) q,
    ← Real.rpow_neg h1u.le]
  calc
    1 / beta (m / 2) (n / 2) * u ^ (m / 2 - 1) * (1 - u) ^ (n / 2 - 1) *
          ((n / m) ^ q * u ^ (q : ℝ) * (1 - u) ^ (-(q : ℝ))) =
        (n / m) ^ q / beta (m / 2) (n / 2) *
          ((u ^ (m / 2 - 1) * u ^ (q : ℝ)) *
            ((1 - u) ^ (n / 2 - 1) * (1 - u) ^ (-(q : ℝ)))) := by ring
    _ = (n / m) ^ q / beta (m / 2) (n / 2) *
        (u ^ (m / 2 + q - 1) * (1 - u) ^ (n / 2 - q - 1)) := by
      rw [hpowu, hpowv]

/-- The `q`th natural moment of a valid Fisher--Snedecor law, in beta-function form. -/
private theorem integral_pow_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) (q : ℕ)
    (hq : 2 * q < n) :
    ∫ x, x ^ q ∂fisherSnedecorMeasure m n =
      (n / m) ^ q * beta (m / 2 + q) (n / 2 - q) / beta (m / 2) (n / 2) := by
  rw [fisherSnedecorMeasure_eq_map hm hn,
    integral_map (measurable_fisherSnedecorMap m n).aemeasurable (by fun_prop), betaMeasure]
  -- `integral_withDensity_eq_integral_toReal_smul` expects the defining `ofReal` form of the
  -- beta density, while `betaPDF` is kept opaque by the public distribution API.
  change (∫ x, fisherSnedecorMap m n x ^ q ∂volume.withDensity
    (fun x ↦ ENNReal.ofReal (betaPDFReal (m / 2) (n / 2) x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have htoReal : ∀ x : ℝ,
      (ENNReal.ofReal (betaPDFReal (m / 2) (n / 2) x)).toReal =
        betaPDFReal (m / 2) (n / 2) x := fun x ↦
    ENNReal.toReal_ofReal (TauCeti.betaPDFReal_nonneg (by linarith) (by linarith) x)
  simp_rw [htoReal, smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (0 : ℝ) 1)]
  · rw [setIntegral_congr_fun measurableSet_Ioo
      (fun u hu ↦ betaMomentIntegrand_eq q hu), integral_const_mul,
      ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      integral_rpow_mul_one_sub_rpow (by positivity) (by norm_num at hq ⊢; linarith)]
    ring_nf
  · intro u hu
    rw [betaPDFReal, ite_eq_right (by simpa only [mem_Ioo] using hu), zero_mul]

/-- The mean of a Fisher--Snedecor law is `n / (n - 2)` when `2 < n`. -/
@[simp]
theorem integral_id_fisherSnedecorMeasure (hm : 0 < m) (hn : 2 < n) :
    ∫ x, x ∂fisherSnedecorMeasure m n = n / (n - 2) := by
  have h := integral_pow_fisherSnedecorMeasure hm (lt_trans zero_lt_two hn) 1 (by simpa)
  simp only [pow_one, Nat.cast_one] at h
  rw [h, ProbabilityTheory.beta, ProbabilityTheory.beta]
  have hm2 : 0 < m / 2 := by linarith
  have hn2 : 0 < n / 2 - 1 := by linarith
  have hsum1 : m / 2 + 1 + (n / 2 - 1) = (m + n) / 2 := by ring
  have hsum0 : m / 2 + n / 2 = (m + n) / 2 := by ring
  rw [hsum1, hsum0, Real.Gamma_add_one (ne_of_gt hm2)]
  have hgamma : Real.Gamma (n / 2) = (n / 2 - 1) * Real.Gamma (n / 2 - 1) := by
    simpa using Real.Gamma_add_one (ne_of_gt hn2)
  rw [hgamma]
  have hG : Real.Gamma (n / 2 - 1) ≠ 0 := (Real.Gamma_pos_of_pos hn2).ne'
  have hfactor : n * Real.Gamma (n / 2 - 1) - Real.Gamma (n / 2 - 1) * 2 =
      (n - 2) * Real.Gamma (n / 2 - 1) := by ring
  have hden : n * Real.Gamma (n / 2 - 1) - Real.Gamma (n / 2 - 1) * 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (by linarith) hG
  have harg : (n - 2) / 2 = n / 2 - 1 := by ring
  have hG' : Real.Gamma ((n - 2) / 2) ≠ 0 := by
    rw [harg]
    exact hG
  field_simp [(Real.Gamma_pos_of_pos hm2).ne', (Real.Gamma_pos_of_pos hn2).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < (m + n) / 2)).ne', hm.ne',
    (by linarith : n - 2 ≠ 0), hden, hG']

/-- The second raw moment of a Fisher--Snedecor law when `4 < n`. -/
@[simp]
theorem integral_sq_fisherSnedecorMeasure (hm : 0 < m) (hn : 4 < n) :
    ∫ x, x ^ 2 ∂fisherSnedecorMeasure m n =
      n ^ 2 * (m + 2) / (m * (n - 2) * (n - 4)) := by
  have h := integral_pow_fisherSnedecorMeasure hm (by linarith) 2 (by norm_num; linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [h, ProbabilityTheory.beta, ProbabilityTheory.beta]
  have hm2 : 0 < m / 2 := by linarith
  have hn2 : 0 < n / 2 - 2 := by linarith
  have hsum1 : m / 2 + 2 + (n / 2 - 2) = (m + n) / 2 := by ring
  have hsum0 : m / 2 + n / 2 = (m + n) / 2 := by ring
  rw [hsum1, hsum0]
  have hmarg : m / 2 + 2 = m / 2 + 1 + 1 := by ring
  have hgm : Real.Gamma (m / 2 + 2) =
      (m / 2 + 1) * (m / 2) * Real.Gamma (m / 2) := by
    rw [hmarg,
      Real.Gamma_add_one (by linarith : m / 2 + 1 ≠ 0),
      Real.Gamma_add_one hm2.ne']
    ring_nf
  have hnarg : n / 2 = (n / 2 - 2) + 1 + 1 := by ring
  have hgn : Real.Gamma (n / 2) =
      (n / 2 - 1) * (n / 2 - 2) * Real.Gamma (n / 2 - 2) := by
    rw [hnarg,
      Real.Gamma_add_one (by linarith : n / 2 - 2 + 1 ≠ 0),
      Real.Gamma_add_one hn2.ne']
    ring_nf
  rw [hgm, hgn]
  have hG : Real.Gamma (n / 2 - 2) ≠ 0 := (Real.Gamma_pos_of_pos hn2).ne'
  have hfactor : n * Real.Gamma (n / 2 - 2) - Real.Gamma (n / 2 - 2) * 4 =
      (n - 4) * Real.Gamma (n / 2 - 2) := by ring
  have hden : n * Real.Gamma (n / 2 - 2) - Real.Gamma (n / 2 - 2) * 4 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (by linarith) hG
  have harg : -2 + n * (1 / 2) = n / 2 - 2 := by ring
  have hden' : n * Real.Gamma (-2 + n * (1 / 2)) -
      Real.Gamma (-2 + n * (1 / 2)) * 4 ≠ 0 := by
    rw [harg]
    exact hden
  field_simp [(Real.Gamma_pos_of_pos hm2).ne', (Real.Gamma_pos_of_pos hn2).ne',
    (Real.Gamma_pos_of_pos (by linarith : 0 < (m + n) / 2)).ne', hm.ne',
    (by linarith : n - 2 ≠ 0), (by linarith : n - 4 ≠ 0), hden, hden']
  field_simp [(by norm_num; linarith : n - 2 ^ 2 ≠ 0),
    (Real.Gamma_pos_of_pos (by norm_num; linarith : 0 < (n - 2 ^ 2) / 2)).ne']
  norm_num

/-- The variance of a Fisher--Snedecor law when `4 < n`. -/
@[simp]
theorem variance_id_fisherSnedecorMeasure (hm : 0 < m) (hn : 4 < n) :
    variance id (fisherSnedecorMeasure m n) =
      2 * n ^ 2 * (m + n - 2) / (m * (n - 2) ^ 2 * (n - 4)) := by
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure m n) :=
    isProbabilityMeasure_fisherSnedecorMeasure hm (by linarith)
  have hmem : MemLp id 2 (fisherSnedecorMeasure m n) :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2
      ((integrable_pow_fisherSnedecorMeasure_iff hm (by linarith) 2).2 (by norm_num; linarith))
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_fisherSnedecorMeasure hm hn,
    integral_id_fisherSnedecorMeasure hm (by linarith)]
  field_simp [hm.ne', (by linarith : n - 2 ≠ 0), (by linarith : n - 4 ≠ 0)]
  ring

end Probability

end TauCeti
