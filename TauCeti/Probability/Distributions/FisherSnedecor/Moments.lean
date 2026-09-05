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

This file establishes the natural moments of the Fisher--Snedecor law.  The moment of order `q`
exists exactly when `2 * q < n` and is then a quotient of beta functions.  The first two cases
give the mean, second raw moment, and variance, together with the exact thresholds `2 < n` and
`4 < n` at which those moments diverge.

## Main results

* `integrable_id_fisherSnedecorMeasure_iff` and `integrable_sq_fisherSnedecorMeasure_iff` give
  the two sharp integrability thresholds, hence also the divergence at and below them.
* `integrable_pow_fisherSnedecorMeasure_iff` and `integral_pow_fisherSnedecorMeasure` give the
  integrability criterion and beta-function formula for every natural moment.
* `integral_id_fisherSnedecorMeasure` computes the mean.
* `integral_sq_fisherSnedecorMeasure` computes the second raw moment.
* `variance_id_fisherSnedecorMeasure` computes the variance.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
* The formal beta-kernel argument follows
  `TauCeti.Probability.Distributions.StudentT.Moments`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Topology

namespace TauCeti

namespace Probability

variable {m n : ℝ}

private def fisherMomentKernel (m n q x : ℝ) : ℝ :=
  x ^ (m / 2 + q - 1) * (1 + x) ^ (-((m + n) / 2))

private lemma integrableOn_fisherMomentKernel_iff (hm : 0 < m) (q : ℝ)
    (hq : 0 ≤ q) :
    IntegrableOn (fisherMomentKernel m n q) (Ioi (0 : ℝ)) ↔ q < n / 2 := by
  have h := integrableOn_rpow_mul_one_add_rpow_iff
    (a := m / 2 + q) (b := n / 2 - q) (by linarith)
  have hsum : m / 2 + q + (n / 2 - q) = (m + n) / 2 := by ring
  have htail : 0 < n / 2 - q ↔ q < n / 2 := by
    constructor <;> intro hh <;> linarith
  -- Expose the reducible kernel so the parameter-sum rewrite can reach its exponent.
  change IntegrableOn (fun x : ℝ ↦ x ^ (m / 2 + q - 1) *
    (1 + x) ^ (-((m + n) / 2))) (Ioi 0) ↔ q < n / 2
  simpa only [hsum, htail] using h

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
  rw [← integrableOn_fisherMomentKernel_iff hm q (Nat.cast_nonneg q), ← hcomp]
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
theorem integrable_pow_fisherSnedecorMeasure_iff (hm : 0 < m) (hn : 0 < n) (q : ℕ) :
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
@[simp]
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

/-- The `q`th natural moment of a Fisher--Snedecor law, in beta-function form. -/
theorem integral_pow_fisherSnedecorMeasure (hm : 0 < m) (q : ℕ)
    (hq : 2 * q < n) :
    ∫ x, x ^ q ∂fisherSnedecorMeasure m n =
      (n / m) ^ q * beta (m / 2 + q) (n / 2 - q) / beta (m / 2) (n / 2) := by
  have hn : 0 < n := lt_of_le_of_lt (mul_nonneg (by norm_num) (Nat.cast_nonneg q)) hq
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

private lemma beta_add_one_sub_one_div {a b : ℝ} (ha : 0 < a) (hb : 1 < b) :
    beta (a + 1) (b - 1) / beta a b = a / (b - 1) := by
  have hab : a + (b - 1) ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  have hbase : beta a (b - 1) ≠ 0 := (beta_pos ha (by linarith)).ne'
  have hleft : beta (a + 1) (b - 1) =
      a / (a + (b - 1)) * beta a (b - 1) :=
    beta_add_one_left ha.ne' hab
  have hright : beta a b =
      (b - 1) / (a + (b - 1)) * beta a (b - 1) := by
    calc
      beta a b = beta b a := beta_comm a b
      _ = beta ((b - 1) + 1) a := by ring_nf
      _ = (b - 1) / ((b - 1) + a) * beta (b - 1) a :=
        beta_add_one_left hb1 (by linarith)
      _ = (b - 1) / (a + (b - 1)) * beta a (b - 1) := by
        rw [beta_comm (b - 1) a, add_comm (b - 1) a]
  rw [hleft, hright]
  field_simp

private lemma beta_add_two_sub_two_div {a b : ℝ} (ha : 0 < a) (hb : 2 < b) :
    beta (a + 2) (b - 2) / beta a b =
      a * (a + 1) / ((b - 1) * (b - 2)) := by
  have hstep1 := beta_add_one_sub_one_div ha (by linarith : 1 < b)
  have hstep2 := beta_add_one_sub_one_div (a := a + 1) (b := b - 1)
    (by linarith) (by linarith)
  have hsub : (b - 1) - 1 = b - 2 := by ring
  rw [hsub] at hstep2
  have hbeta : beta (a + 1) (b - 1) ≠ 0 :=
    (beta_pos (by linarith) (by linarith)).ne'
  have hb1 : b - 1 ≠ 0 := by linarith
  have hb2 : b - 2 ≠ 0 := by linarith
  have ha2 : a + 2 = (a + 1) + 1 := by ring
  rw [ha2]
  calc
    beta ((a + 1) + 1) (b - 2) / beta a b =
        (beta ((a + 1) + 1) (b - 2) / beta (a + 1) (b - 1)) *
          (beta (a + 1) (b - 1) / beta a b) := by field_simp
    _ = ((a + 1) / (b - 2)) * (a / (b - 1)) := by rw [hstep1, hstep2]
    _ = a * (a + 1) / ((b - 1) * (b - 2)) := by
      field_simp [hb1, hb2]

/-- The mean of a Fisher--Snedecor law is `n / (n - 2)` when `2 < n`. -/
@[simp]
theorem integral_id_fisherSnedecorMeasure (hm : 0 < m) (hn : 2 < n) :
    ∫ x, x ∂fisherSnedecorMeasure m n = n / (n - 2) := by
  have h := integral_pow_fisherSnedecorMeasure hm 1 (by simpa)
  simp only [pow_one, Nat.cast_one] at h
  rw [h]
  calc
    n / m * beta (m / 2 + 1) (n / 2 - 1) / beta (m / 2) (n / 2) =
        n / m * (beta (m / 2 + 1) (n / 2 - 1) / beta (m / 2) (n / 2)) := by ring
    _ = n / m * ((m / 2) / (n / 2 - 1)) := by
      rw [beta_add_one_sub_one_div (by linarith) (by linarith)]
    _ = n / (n - 2) := by
      field_simp [hm.ne', (by linarith : n - 2 ≠ 0)]

/-- The second raw moment of a Fisher--Snedecor law is
`n ^ 2 * (m + 2) / (m * (n - 2) * (n - 4))` when `4 < n`. -/
@[simp]
theorem integral_sq_fisherSnedecorMeasure (hm : 0 < m) (hn : 4 < n) :
    ∫ x, x ^ 2 ∂fisherSnedecorMeasure m n =
      n ^ 2 * (m + 2) / (m * (n - 2) * (n - 4)) := by
  have h := integral_pow_fisherSnedecorMeasure hm 2 (by norm_num; linarith)
  norm_num only [Nat.cast_ofNat] at h
  rw [h]
  calc
    (n / m) ^ 2 * beta (m / 2 + 2) (n / 2 - 2) / beta (m / 2) (n / 2) =
        (n / m) ^ 2 *
          (beta (m / 2 + 2) (n / 2 - 2) / beta (m / 2) (n / 2)) := by ring
    _ = (n / m) ^ 2 *
        ((m / 2) * (m / 2 + 1) / ((n / 2 - 1) * (n / 2 - 2))) := by
      rw [beta_add_two_sub_two_div (by linarith) (by linarith)]
    _ = n ^ 2 * (m + 2) / (m * (n - 2) * (n - 4)) := by
      have hm2 : m / 2 + 1 = (m + 2) / 2 := by ring
      have hn2 : n / 2 - 1 = (n - 2) / 2 := by ring
      have hn4 : n / 2 - 2 = (n - 4) / 2 := by ring
      rw [hm2, hn2, hn4]
      field_simp [hm.ne', (by linarith : n - 2 ≠ 0), (by linarith : n - 4 ≠ 0)]

/-- The variance of a Fisher--Snedecor law is
`2 * n ^ 2 * (m + n - 2) / (m * (n - 2) ^ 2 * (n - 4))` when `4 < n`. -/
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
