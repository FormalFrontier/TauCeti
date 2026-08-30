/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Power
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Stieltjes functions are completely monotone

A Stieltjes representation is a nonnegative combination of a reciprocal, a constant, and an
integral of shifted reciprocals.  This file proves that every such representation is completely
monotone on `(0, ∞)`.  The open half-line is essential: the singular coefficient `a / t`, and
more generally an infinite representing measure, need not admit a finite value or derivatives at
the origin.

The proof differentiates the integral under the integral sign.  Its `n`-th derivative has kernel
`(-1)ⁿ n! (t + x)⁻ⁿ⁻¹`.  On a neighborhood of a positive parameter, every such kernel is
dominated by a constant multiple of the defining Stieltjes weight `(1 + x)⁻¹`; thus the sharp
integrability hypothesis in `RepresentsStieltjes` suffices at every derivative order.

## Main declarations

* `TauCeti.integrable_zpow_neg_one_sub_add`: all derivative-order Stieltjes kernels are
  integrable at positive parameters.
* `TauCeti.iteratedDeriv_integral_inv_add`: the derivative formula for the integral term.
* `TauCeti.isCompletelyMonotoneOnIoi_integral_inv_add`: a Stieltjes integral is completely
  monotone on `(0, ∞)`.
* `TauCeti.IsStieltjesFunction.isCompletelyMonotoneOnIoi`: every Stieltjes function is completely
  monotone on `(0, ∞)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Theorem 2.2.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B, the
  Stieltjes/Bernstein-function relationships target.
-/

public section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff ENNReal NNReal Topology

namespace TauCeti

variable {μ : Measure ℝ≥0}

/-- The kernel obtained after differentiating a shifted reciprocal `n` times. -/
private def stieltjesDerivKernel (n : ℕ) (t : ℝ) (x : ℝ≥0) : ℝ :=
  (-1 : ℝ) ^ n * n.factorial * (t + (x : ℝ)) ^ (-1 - (n : ℤ))

private lemma stieltjesDerivKernel_zero (t : ℝ) (x : ℝ≥0) :
    stieltjesDerivKernel 0 t x = (t + (x : ℝ))⁻¹ := by
  simp [stieltjesDerivKernel]

private lemma zpow_neg_le_zpow_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    b ^ (-(k : ℤ)) ≤ a ^ (-(k : ℤ)) := by
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (ha.trans_le hab) k) (pow_pos ha k)).2
    (pow_le_pow_left₀ ha.le hab k)

private lemma hasDerivAt_stieltjesDerivKernel (n : ℕ) {t : ℝ} (x : ℝ≥0)
    (ht : 0 < t) :
    HasDerivAt (fun u => stieltjesDerivKernel n u x) (stieltjesDerivKernel (n + 1) t x) t := by
  have hne : t + (x : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
  have hbase : HasDerivAt (fun u : ℝ => u + (x : ℝ)) 1 t := by
    simpa using (hasDerivAt_id t).add_const (x : ℝ)
  have hpow :=
    (hasDerivAt_zpow (-1 - (n : ℤ)) (t + (x : ℝ)) (Or.inl hne)).comp t hbase
  have h := hpow.const_mul ((-1 : ℝ) ^ n * n.factorial)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [] with u
    simp only [stieltjesDerivKernel, Function.comp_def]
  · unfold stieltjesDerivKernel
    have hexp : -1 - ((n + 1 : ℕ) : ℤ) = -1 - (n : ℤ) - 1 := by omega
    rw [hexp]
    push_cast [Nat.factorial_succ]
    ring

/-! ### Integrability and domination of the derivative kernels -/

/-- Every integer-power kernel occurring in a derivative of a Stieltjes integral is integrable
at a positive parameter. -/
theorem integrable_zpow_neg_one_sub_add (hμ : Integrable stieltjesWeight μ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => (t + (x : ℝ)) ^ (-1 - (n : ℤ))) μ := by
  refine ((integrable_inv_add hμ ht).const_mul (t ^ (-(n : ℤ)))).mono' ?_ ?_
  · exact (((continuous_const.add continuous_subtype_val).zpow₀ _ fun (x : ℝ≥0) =>
      Or.inl (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne')).aestronglyMeasurable
  filter_upwards [] with x
  have hpos : 0 < t + (x : ℝ) := add_pos_of_pos_of_nonneg ht x.coe_nonneg
  have hfactor : (t + (x : ℝ)) ^ (-1 - (n : ℤ)) =
      (t + (x : ℝ))⁻¹ * (t + (x : ℝ)) ^ (-(n : ℤ)) := by
    rw [sub_eq_add_neg, zpow_add₀ hpos.ne', zpow_neg_one]
  have htx : t ≤ t + (x : ℝ) := by linarith [x.coe_nonneg]
  have hpow : (t + (x : ℝ)) ^ (-(n : ℤ)) ≤ t ^ (-(n : ℤ)) :=
    zpow_neg_le_zpow_neg ht htx n
  have hval : (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ≤
      t ^ (-(n : ℤ)) * (t + (x : ℝ))⁻¹ := by
    rw [hfactor]
    calc
      (t + (x : ℝ))⁻¹ * (t + (x : ℝ)) ^ (-(n : ℤ))
          ≤ (t + (x : ℝ))⁻¹ * t ^ (-(n : ℤ)) :=
        mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hpos.le)
      _ = t ^ (-(n : ℤ)) * (t + (x : ℝ))⁻¹ := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (zpow_pos hpos _),
    abs_of_pos (mul_pos (zpow_pos ht _) (inv_pos.mpr hpos))] using hval

private lemma integrable_stieltjesDerivKernel (hμ : Integrable stieltjesWeight μ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) : Integrable (stieltjesDerivKernel n t) μ := by
  have hkernel : stieltjesDerivKernel n t = fun x : ℝ≥0 =>
      ((-1 : ℝ) ^ n * n.factorial) * (t + (x : ℝ)) ^ (-1 - (n : ℤ)) := by
    funext x
    simp only [stieltjesDerivKernel]
  rw [hkernel]
  exact (integrable_zpow_neg_one_sub_add hμ n ht).const_mul
    ((-1 : ℝ) ^ n * n.factorial)

private lemma norm_stieltjesDerivKernel_le (n : ℕ) (x : ℝ≥0) {r t : ℝ}
    (hr : 0 < r) (hrt : r ≤ t) :
    ‖stieltjesDerivKernel n t x‖ ≤ ‖stieltjesDerivKernel n r x‖ := by
  have hrx : 0 < r + (x : ℝ) := add_pos_of_pos_of_nonneg hr x.coe_nonneg
  have hrtx : r + (x : ℝ) ≤ t + (x : ℝ) := by linarith
  have htx : 0 < t + (x : ℝ) := lt_of_lt_of_le hrx hrtx
  have hbase : (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ≤
      (r + (x : ℝ)) ^ (-1 - (n : ℤ)) := by
    have hexp : -1 - (n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hexp]
    exact zpow_neg_le_zpow_neg hrx hrtx (n + 1)
  simp only [stieltjesDerivKernel, Real.norm_eq_abs, abs_mul,
    abs_of_pos (zpow_pos htx _), abs_of_pos (zpow_pos hrx _)]
  exact mul_le_mul_of_nonneg_left hbase (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The integral of the kernel obtained after `n` differentiations. -/
private def stieltjesDerivIntegral (μ : Measure ℝ≥0) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x, stieltjesDerivKernel n t x ∂μ

private lemma stieltjesDerivIntegral_zero (μ : Measure ℝ≥0) :
    stieltjesDerivIntegral μ 0 = fun t : ℝ => ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ := by
  funext t
  simp only [stieltjesDerivIntegral, stieltjesDerivKernel_zero]

private lemma hasDerivAt_stieltjesDerivIntegral (hμ : Integrable stieltjesWeight μ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (stieltjesDerivIntegral μ n) (stieltjesDerivIntegral μ (n + 1) t) t := by
  let r := t / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hts : t ∈ Ioi r := by
    have hrt : r < t := by dsimp [r]; linarith
    exact hrt
  have hs : Ioi r ∈ 𝓝 t := isOpen_Ioi.mem_nhds hts
  have hmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable (stieltjesDerivKernel n u) μ := by
    filter_upwards [hs] with u hu
    exact (integrable_stieltjesDerivKernel hμ n (hr.trans hu)).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable (stieltjesDerivKernel (n + 1) t) μ :=
    (integrable_stieltjesDerivKernel hμ (n + 1) ht).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ u ∈ Ioi r,
      ‖stieltjesDerivKernel (n + 1) u x‖ ≤ ‖stieltjesDerivKernel (n + 1) r x‖ :=
    Filter.Eventually.of_forall fun x u hu => norm_stieltjesDerivKernel_le (n + 1) x hr hu.le
  have hdiff : ∀ᵐ x ∂μ, ∀ u ∈ Ioi r,
      HasDerivAt (fun v => stieltjesDerivKernel n v x) (stieltjesDerivKernel (n + 1) u x) u :=
    Filter.Eventually.of_forall fun x u hu =>
      hasDerivAt_stieltjesDerivKernel n x (hr.trans hu)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    (integrable_stieltjesDerivKernel hμ n ht) hderivMeas hbound
    (integrable_stieltjesDerivKernel hμ (n + 1) hr).norm hdiff).2

private lemma differentiableOn_stieltjesDerivIntegral
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) :
    DifferentiableOn ℝ (stieltjesDerivIntegral μ n) (Ioi 0) := fun _t ht =>
  (hasDerivAt_stieltjesDerivIntegral hμ n ht).differentiableAt.differentiableWithinAt

private lemma deriv_stieltjesDerivIntegral (hμ : Integrable stieltjesWeight μ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    deriv (stieltjesDerivIntegral μ n) t = stieltjesDerivIntegral μ (n + 1) t :=
  (hasDerivAt_stieltjesDerivIntegral hμ n ht).deriv

private lemma contDiffOn_stieltjesDerivIntegral
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) :
    ContDiffOn ℝ ∞ (stieltjesDerivIntegral μ n) (Ioi 0) := by
  rw [contDiffOn_infty]
  intro k
  induction k generalizing n with
  | zero =>
      exact contDiffOn_zero.mpr (differentiableOn_stieltjesDerivIntegral hμ n).continuousOn
  | succ k ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨differentiableOn_stieltjesDerivIntegral hμ n, by simp, ?_⟩
      exact (ih (n + 1)).congr fun t ht => deriv_stieltjesDerivIntegral hμ n ht

private lemma iteratedDeriv_stieltjesDerivIntegral_zero
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (stieltjesDerivIntegral μ 0) t = stieltjesDerivIntegral μ n t := by
  induction n generalizing t with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have heq : iteratedDeriv n (stieltjesDerivIntegral μ 0) =ᶠ[𝓝 t]
          stieltjesDerivIntegral μ n := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu using ih hu
      rw [iteratedDeriv_succ, heq.deriv_eq,
        deriv_stieltjesDerivIntegral hμ n ht, Nat.add_comm n 1]

/-- The `n`-th derivative of a Stieltjes integral is the integral of
`(-1)ⁿ n! (t + x)⁻ⁿ⁻¹` at every positive parameter. -/
theorem iteratedDeriv_integral_inv_add (hμ : Integrable stieltjesWeight μ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (fun u : ℝ => ∫ x : ℝ≥0, (u + (x : ℝ))⁻¹ ∂μ) t =
      (-1 : ℝ) ^ n * n.factorial *
        ∫ x : ℝ≥0, (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ := by
  rw [← stieltjesDerivIntegral_zero, iteratedDeriv_stieltjesDerivIntegral_zero hμ n ht,
    stieltjesDerivIntegral]
  simpa only [stieltjesDerivKernel] using
    integral_const_mul ((-1 : ℝ) ^ n * n.factorial)
      (fun x : ℝ≥0 => (t + (x : ℝ)) ^ (-1 - (n : ℤ)))

/-- Integrating the shifted reciprocal kernels against a measure satisfying the Stieltjes
weight condition gives a function completely monotone on `(0, ∞)`. -/
theorem isCompletelyMonotoneOnIoi_integral_inv_add
    (hμ : Integrable stieltjesWeight μ) :
    IsCompletelyMonotoneOnIoi fun t : ℝ => ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ := by
  refine ⟨stieltjesDerivIntegral_zero μ ▸ contDiffOn_stieltjesDerivIntegral hμ 0,
    fun n t ht => ?_⟩
  rw [iteratedDeriv_integral_inv_add hμ n ht]
  have hint : 0 ≤ ∫ x : ℝ≥0, (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ :=
    integral_nonneg fun x => (zpow_pos (add_pos_of_pos_of_nonneg ht x.coe_nonneg) _).le
  have heq : (-1 : ℝ) ^ n *
      ((-1 : ℝ) ^ n * n.factorial *
        ∫ x : ℝ≥0, (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ) =
      ((-1 : ℝ) ^ n) ^ 2 * n.factorial *
        ∫ x : ℝ≥0, (t + (x : ℝ)) ^ (-1 - (n : ℤ)) ∂μ := by ring
  rw [heq]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hint

namespace RepresentsStieltjes

variable {a b : ℝ≥0} {f : ℝ → ℝ}

/-- A function with a Stieltjes representation is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (h : RepresentsStieltjes μ a b f) :
    IsCompletelyMonotoneOnIoi f := by
  have ha : IsCompletelyMonotoneOnIoi fun t : ℝ => (a : ℝ) / t := by
    have hs := (isCompletelyMonotoneOnIoi_rpow_neg (s := 1) zero_le_one).smul a.coe_nonneg
    exact hs.congr fun t _ => by
      simp [Pi.smul_apply, smul_eq_mul, Real.rpow_neg_one, div_eq_mul_inv]
  have hb : IsCompletelyMonotoneOnIoi fun _ : ℝ => (b : ℝ) :=
    (isCompletelyMonotone_const b.coe_nonneg).isCompletelyMonotoneOnIoi
  have hi : IsCompletelyMonotoneOnIoi fun t : ℝ =>
      ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ :=
    isCompletelyMonotoneOnIoi_integral_inv_add h.integrable_weight
  exact ((ha.add hb).add hi).congr fun t ht => h.eq_div_add_add_integral_inv_add ht

end RepresentsStieltjes

namespace IsStieltjesFunction

variable {f : ℝ → ℝ}

/-- Every Stieltjes function is completely monotone on `(0, ∞)`. -/
@[grind =>]
lemma isCompletelyMonotoneOnIoi (hf : IsStieltjesFunction f) :
    IsCompletelyMonotoneOnIoi f := by
  rw [isStieltjesFunction_iff] at hf
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact hμ.isCompletelyMonotoneOnIoi

end IsStieltjesFunction

end TauCeti

end

end
