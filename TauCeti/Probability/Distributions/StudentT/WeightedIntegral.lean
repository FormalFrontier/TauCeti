/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.Basic

/-!
# The square-root chart for weighted half-line integrals of Student's t law

The substitution `w = z ^ 2 / ν` reduces weighted integrals of the even Student t density over the
positive half-line to Euler integrals on `(0, ∞)`. This file collects the chart, its
injectivity and derivative, the beta-kernel normal form of the transformed density, and the kernel
itself; the polynomial moment evaluations live in `Basic.lean`, the exponential-moment results in
`Moments.lean`, and the tail/cdf evaluation in `Cdf.lean`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν q x t : ℝ}

/-! ### Weighted half-line integrals -/


/-- The kernel on the positive half-line after the substitution `w = x ^ 2 / ν`:
`w ^ ((q - 1) / 2) * (1 + w) ^ (-((ν + 1) / 2))`. -/
abbrev studentTBetaKernel (ν q w : ℝ) : ℝ :=
  w ^ ((q - 1) / 2) * (1 + w) ^ (-((ν + 1) / 2))

/-- The square-root chart `z ↦ z ^ 2 / ν` carries `(y, ∞)` onto `(y ^ 2 / ν, ∞)` for `0 ≤ y`. -/
lemma image_sq_div_const_Ioi (hν : 0 < ν) {y : ℝ} (hy : 0 ≤ y) :
    (fun z : ℝ => z ^ 2 / ν) '' Ioi y = Ioi (y ^ 2 / ν) := by
  ext w
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 : 0 < z := hy.trans_lt hz
    have hsq : y ^ 2 < z ^ 2 := by gcongr
    exact div_lt_div_of_pos_right hsq hν
  · intro hw
    have h0 : 0 ≤ y ^ 2 / ν := by positivity
    have hw0 : 0 < w := h0.trans_lt hw
    have hνw : 0 < ν * w := mul_pos hν hw0
    have hsqrt_y : y < Real.sqrt (ν * w) := by
      have h : y ^ 2 < ν * w := by
        have h' : y ^ 2 / ν < w := hw
        calc y ^ 2 = ν * (y ^ 2 / ν) := by field_simp [hν.ne']
             _ < ν * w := mul_lt_mul_of_pos_left h' hν
      have h2 : y ^ 2 < (Real.sqrt (ν * w)) ^ 2 := by
        rw [Real.sq_sqrt (by linarith)]; exact h
      nlinarith [Real.sqrt_nonneg (ν * w)]
    refine ⟨Real.sqrt (ν * w), hsqrt_y, ?_⟩
    rw [Real.sq_sqrt (by linarith)]; field_simp [hν.ne']

/-- The chart `z ↦ z ^ 2 / ν` is injective on the positive half-line for nonzero `ν`. -/
lemma sq_div_const_injOn_Ioi (hν : ν ≠ 0) :
    InjOn (fun z : ℝ => z ^ 2 / ν) (Ioi (0 : ℝ)) := by
  intro z hz w hw h
  have hz0 : 0 < z := hz
  have hw0 : 0 < w := hw
  have : z ^ 2 = w ^ 2 := by
    field_simp [hν] at h
    linarith
  nlinarith

/-- The derivative of the chart `z ↦ z ^ 2 / ν`. -/
lemma hasDerivAt_sq_div_const (ν z : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 2 / ν) (2 * z / ν) z := by
  simpa using ((hasDerivAt_id z).pow 2).div_const ν

/-- The square chart rewrites the beta-kernel power as the sample power times the compensating
degree-of-freedom power. -/
private lemma sq_div_const_rpow_studentTBetaExponent (hν : 0 < ν) (q : ℝ) {z : ℝ}
    (hz : 0 < z) :
    (z ^ 2 / ν) ^ ((q - 1) / 2) = z ^ (q - 1) * ν ^ (-((q - 1) / 2)) := by
  set e := (q - 1) / 2 with he
  have hz0 : 0 ≤ z := hz.le
  have hdiv : (z ^ 2 / ν) ^ e = (z ^ 2) ^ e / ν ^ e := by
    rw [Real.div_rpow (by positivity) hν.le]
  have hz2 : (z ^ 2) ^ e = z ^ (q - 1) := by
    have hzpow : z ^ (2 * e) = (z ^ (2 : ℝ)) ^ e := Real.rpow_mul hz0 2 e
    have hz2' : (z ^ (2 : ℕ)) = z ^ (2 : ℝ) := by
      simp
    have hzpow2 : (z ^ (2 : ℕ)) ^ e = z ^ (2 * e) := by
      rw [hz2']
      exact hzpow.symm
    rw [hzpow2]
    have heq : 2 * e = q - 1 := by simp [he]; ring
    rw [heq]
  have hνinv : (ν ^ e)⁻¹ = ν ^ (-e) := by
    have h : ν ^ (-e) = (ν ^ e)⁻¹ := Real.rpow_neg hν.le e
    exact h.symm
  rw [hdiv, hz2, div_eq_mul_inv, hνinv, he]

/-- The sample powers left by the Jacobian combine to `z ^ q`. -/
private lemma rpow_sub_one_mul_self (q : ℝ) {z : ℝ} (hz : 0 < z) :
    z ^ (q - 1) * z = z ^ q := by
  have h : z ^ (q - 1) * z = z ^ (q - 1) * z ^ (1 : ℝ) := by
    rw [Real.rpow_one]
  rw [h, ← Real.rpow_add hz]
  congr 1
  ring

/-- The powers of `ν` introduced by the square chart and the Jacobian cancel. -/
private lemma studentT_chart_nu_powers_cancel (hν : 0 < ν) (q : ℝ) :
    ν ^ ((q + 1) / 2) * ν ^ (-((q - 1) / 2)) * ν ^ (-1 : ℝ) = 1 := by
  have hνexp : (q + 1) / 2 + (-((q - 1) / 2)) + (-1 : ℝ) = 0 := by ring
  have h31 : ν ^ ((q + 1) / 2 + (-((q - 1) / 2)) + (-1 : ℝ)) =
      ν ^ ((q + 1) / 2) * ν ^ (-((q - 1) / 2)) * ν ^ (-1 : ℝ) := by
    rw [Real.rpow_add hν, Real.rpow_add hν]
  rw [← h31, hνexp, Real.rpow_zero]

/-- The non-kernel scalar part of the transformed weighted density reduces to the expected
normalizing constant times `z ^ q`. -/
private lemma studentT_chart_scalar_part (hν : 0 < ν) (q : ℝ) {z : ℝ} (hz : 0 < z)
    (C : ℝ) :
    C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
        (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) = C * z ^ q := by
  have h51 : ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) =
      z * (ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ)) := by
    have hdiv : 2 * z / ν = (2 * z) * ν ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      ring
    rw [hdiv]
    ring
  have h5 : C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
      (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) =
      C * (z ^ (q - 1) * z) *
        (ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ) * ν ^ (-((q - 1) / 2))) := by
    calc
      C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
          (z ^ (q - 1) * ν ^ (-((q - 1) / 2)))
        = C * (ν ^ ((q + 1) / 2) / 2 * (2 * z / ν)) *
            (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) := by ring
      _ = C * (z * (ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ))) *
            (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) := by rw [h51]
      _ = C * (z ^ (q - 1) * z) *
            (ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ) * ν ^ (-((q - 1) / 2))) := by ring
  have hνpow : ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ) * ν ^ (-((q - 1) / 2)) = 1 := by
    have hcomm : ν ^ ((q + 1) / 2) * ν ^ (-1 : ℝ) * ν ^ (-((q - 1) / 2)) =
        ν ^ ((q + 1) / 2) * ν ^ (-((q - 1) / 2)) * ν ^ (-1 : ℝ) := by ring
    rw [hcomm]
    exact studentT_chart_nu_powers_cancel hν q
  rw [h5, hνpow, mul_one, rpow_sub_one_mul_self q hz]

/-- Under the chart `z ↦ z ^ 2 / ν`, the weighted Student t density becomes the normalized
beta kernel on the positive half-line. -/
lemma abs_deriv_smul_studentTPDFReal (hν : 0 < ν) (q : ℝ) {z : ℝ} (hz : 0 < z) :
    |2 * z / ν| •
        (Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) *
          ν ^ ((q + 1) / 2) / 2 * studentTBetaKernel ν q (z ^ 2 / ν)) =
      studentTPDFReal ν z * z ^ q := by
  set C := Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  rw [studentTPDFReal_of_pos hν, studentTBetaKernel, abs_of_pos (by positivity), smul_eq_mul,
    sq_div_const_rpow_studentTBetaExponent hν q hz]
  have h7 : C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
        (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) * (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      C * (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)) * z ^ q := by
    have h71 : C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
          (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) = C * z ^ q :=
      studentT_chart_scalar_part hν q hz C
    rw [h71]; ring
  have hgoal : (2 * z / ν) * (C * ν ^ ((q + 1) / 2) / 2 *
        (z ^ (q - 1) * ν ^ (-((q - 1) / 2)) *
          (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)))) =
      C * (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)) * z ^ q := by
    have hreorder : (2 * z / ν) * (C * ν ^ ((q + 1) / 2) / 2 *
          (z ^ (q - 1) * ν ^ (-((q - 1) / 2)) *
            (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)))) =
        C * ν ^ ((q + 1) / 2) / 2 * (2 * z / ν) *
          (z ^ (q - 1) * ν ^ (-((q - 1) / 2))) *
            (1 + z ^ 2 / ν) ^ (-((ν + 1) / 2)) := by ring
    rw [hreorder, h7]
  exact hgoal

end Probability

end TauCeti
