/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompletelyMonotone
public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic

/-!
# From Stieltjes functions to Bernstein functions

If

`f t = a / t + b + ∫ x, (t + x)⁻¹ ∂μ`,

then its continuously extended product with the parameter is a Bernstein function:

`g t = a + b * t + ∫ x, t / (t + x) ∂μ`.

On the open half-line this is exactly `t * f(t)`, while `g(0) = a`.  The value at zero is
essential: the literal product `0 * f(0)` would lose the coefficient of the possible `a / t`
singularity.  This is the first standard Stieltjes--Bernstein correspondence.

The proof differentiates the integral on the open half-line.  Its derivative is

`∫ x, x / (t + x) ^ 2 ∂μ`,

whose derivatives have alternating signs.  Continuity at zero follows by dominated convergence;
the normalization `μ {0} = 0` removes the only point where `t / (t + x)` does not tend to zero.

## Main declarations

* `TauCeti.stieltjesBernsteinTransform` and `TauCeti.stieltjesBernsteinTransform_apply`: the
  continuous extension of `t * f(t)` written directly from Stieltjes representing data and its
  defining equation.
* `TauCeti.stieltjesBernsteinTransform_zero`: the transform takes the value `a` at zero.
* `TauCeti.integrable_mul_zpow_neg_two_sub_add`: the derivative kernels of the integral term are
  integrable at positive parameters.
* `TauCeti.iteratedDeriv_integral_div_add`: the iterated derivatives of the integral
  term at positive parameters.
* `TauCeti.hasDerivAt_stieltjesBernsteinTransform` and
  `TauCeti.deriv_stieltjesBernsteinTransform`: the transform has derivative
  `b + ∫ x, x / (t + x) ^ 2 ∂μ` at positive parameters.
* `TauCeti.isBernsteinFunction_integral_div_add`: the integral term is Bernstein.
* `TauCeti.isBernsteinFunction_stieltjesBernsteinTransform`: the transform is Bernstein.
* `TauCeti.RepresentsStieltjes.stieltjesBernsteinTransform_eq_mul`: on `(0, ∞)` the
  transform of a Stieltjes representation of `f` is `t * f(t)`.
* `TauCeti.RepresentsStieltjes.isBernsteinFunction_stieltjesBernsteinTransform`: the transform of
  a Stieltjes representation is Bernstein.
* `TauCeti.IsStieltjesFunction.exists_isBernsteinFunction_eqOn_mul`: every Stieltjes function has
  a Bernstein extension of its product with the parameter on `(0, ∞)`.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff NNReal Topology

namespace TauCeti

/-- The candidate Bernstein transform associated to Stieltjes representing data. Under the
normalization and integrability hypotheses of `isBernsteinFunction_stieltjesBernsteinTransform`,
it is a Bernstein function and is continuous on `[0, ∞)`. For representing data, the later theorem
`RepresentsStieltjes.stieltjesBernsteinTransform_eq_mul` identifies it with `t * f t` for
positive `t`. Its defining equation is `stieltjesBernsteinTransform_apply`. -/
def stieltjesBernsteinTransform (μ : Measure ℝ≥0) (a b : ℝ≥0) (t : ℝ) : ℝ :=
  a + b * t + ∫ x : ℝ≥0, t / (t + x) ∂μ

/-- The defining equation for the Stieltjes--Bernstein transform. -/
lemma stieltjesBernsteinTransform_apply (μ : Measure ℝ≥0) (a b : ℝ≥0) (t : ℝ) :
    stieltjesBernsteinTransform μ a b t = a + b * t + ∫ x : ℝ≥0, t / (t + x) ∂μ :=
  (rfl)

/-- The Stieltjes--Bernstein transform takes the value `a` at zero. -/
@[simp]
theorem stieltjesBernsteinTransform_zero (μ : Measure ℝ≥0) (a b : ℝ≥0) :
    stieltjesBernsteinTransform μ a b 0 = a := by
  simp [stieltjesBernsteinTransform_apply]

private lemma stieltjesBernsteinIntegral_eq_mul_integral_inv_add (μ : Measure ℝ≥0)
    (t : ℝ) :
    (∫ x : ℝ≥0, t / (t + x) ∂μ) =
      t * ∫ x : ℝ≥0, (t + x)⁻¹ ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv])

/-- The kernels in the iterated derivative formula for the integral term of the
Stieltjes--Bernstein transform are integrable at positive parameters. -/
theorem integrable_mul_zpow_neg_two_sub_add {μ : Measure ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) * (t + x) ^ (-2 - (n : ℤ))) μ := by
  have hexpSucc : -1 - ((n + 1 : ℕ) : ℤ) = -2 - (n : ℤ) := by omega
  have hpowInt : Integrable (fun x : ℝ≥0 => (t + (x : ℝ)) ^ (-2 - (n : ℤ))) μ := by
    simpa only [hexpSucc] using integrable_zpow_neg_one_sub_add hμ (n + 1) ht
  refine ((integrable_zpow_neg_one_sub_add hμ n ht).sub (hpowInt.const_mul t)).congr ?_
  filter_upwards with x
  have htx : t + (x : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
  have hexp : -1 - (n : ℤ) = 1 + (-2 - (n : ℤ)) := by omega
  simp only [Pi.sub_apply]
  rw [hexp, zpow_add₀ htx, zpow_one]
  ring

private lemma integral_mul_zpow_eq_sub {μ : Measure ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ≥0, (x : ℝ) * (t + x) ^ (-2 - (n : ℤ)) ∂μ) =
      (∫ x : ℝ≥0, (t + x) ^ (-1 - (n : ℤ)) ∂μ) -
        t * ∫ x : ℝ≥0, (t + x) ^ (-2 - (n : ℤ)) ∂μ := by
  have hexpSucc : -1 - ((n + 1 : ℕ) : ℤ) = -2 - (n : ℤ) := by omega
  have hpowInt : Integrable (fun x : ℝ≥0 => (t + (x : ℝ)) ^ (-2 - (n : ℤ))) μ := by
    simpa only [hexpSucc] using integrable_zpow_neg_one_sub_add hμ (n + 1) ht
  rw [← integral_const_mul,
    ← integral_sub (integrable_zpow_neg_one_sub_add hμ n ht) (hpowInt.const_mul t)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    have htx : t + (x : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
    have hexp : -1 - (n : ℤ) = 1 + (-2 - (n : ℤ)) := by omega
    simp only
    rw [hexp, zpow_add₀ htx, zpow_one]
    ring)

private lemma contDiffOn_stieltjesBernsteinIntegral {μ : Measure ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => ∫ x : ℝ≥0, t / (t + x) ∂μ) (Ioi 0) := by
  refine (contDiffOn_id.mul
    (isCompletelyMonotoneOnIoi_integral_inv_add hμ).contDiffOn).congr fun t _ => ?_
  simpa only [id_eq] using stieltjesBernsteinIntegral_eq_mul_integral_inv_add μ t

/-- The Leibniz expansion of `t * F t` collapses to two terms, because every derivative of the
identity beyond the first vanishes. -/
private lemma iteratedDeriv_succ_id_mul {F : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (hF : ContDiffAt ℝ (n + 1 : ℕ) F t) :
    iteratedDeriv (n + 1) (fun u : ℝ => u * F u) t =
      t * iteratedDeriv (n + 1) F t + ((n : ℝ) + 1) * iteratedDeriv n F t := by
  have hmul := iteratedDeriv_fun_mul (n := n + 1) (x := t) contDiffAt_id hF
  simp only [id_eq] at hmul
  rw [hmul,
    ← Finset.add_sum_erase _ _ (by simp : 0 ∈ Finset.range (n + 1 + 1)),
    ← Finset.add_sum_erase _ _ (by simp : 1 ∈ (Finset.range (n + 1 + 1)).erase 0)]
  have hrest :
      (∑ x ∈ ((Finset.range (n + 1 + 1)).erase 0).erase 1,
        ((n + 1).choose x : ℝ) * iteratedDeriv x id t *
          iteratedDeriv (n + 1 - x) F t) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp [iteratedDeriv_id, hx0, hx1]
  have hid0 : iteratedDeriv 0 id t = t := by simp
  have hid1 : iteratedDeriv 1 id t = 1 := by simp [iteratedDeriv_one]
  rw [hrest, hid0, hid1]
  simp [Nat.choose_one_right]

/-- The iterated derivatives of the integral term in the Stieltjes--Bernstein transform at a
positive parameter. -/
theorem iteratedDeriv_integral_div_add {μ : Measure ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv (n + 1) (fun u : ℝ => ∫ x : ℝ≥0, u / (u + x) ∂μ) t =
      (-1 : ℝ) ^ n * (n + 1).factorial *
        ∫ x : ℝ≥0, (x : ℝ) * (t + x) ^ (-2 - (n : ℤ)) ∂μ := by
  let F := fun u : ℝ => ∫ x : ℝ≥0, (u + (x : ℝ))⁻¹ ∂μ
  have hFdiff : ContDiffAt ℝ (n + 1 : ℕ) F t :=
    ((isCompletelyMonotoneOnIoi_integral_inv_add hμ).contDiffOn.contDiffAt
      (isOpen_Ioi.mem_nhds ht)).of_le (by simp)
  have hjumpEq : (fun u : ℝ => ∫ x : ℝ≥0, u / (u + x) ∂μ) =
      fun u => u * F u := by
    funext u
    exact stieltjesBernsteinIntegral_eq_mul_integral_inv_add μ u
  rw [hjumpEq, iteratedDeriv_succ_id_mul hFdiff]
  have hn := iteratedDeriv_integral_inv_add hμ n ht
  have hn1 := iteratedDeriv_integral_inv_add hμ (n + 1) ht
  have hexpSucc : -1 - ((n + 1 : ℕ) : ℤ) = -2 - (n : ℤ) := by omega
  rw [hexpSucc] at hn1
  rw [hn, hn1, integral_mul_zpow_eq_sub hμ n ht]
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The derivative of the Stieltjes--Bernstein transform at a positive parameter. -/
theorem hasDerivAt_stieltjesBernsteinTransform {μ : Measure ℝ≥0} {a b : ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (stieltjesBernsteinTransform μ a b)
      ((b : ℝ) + ∫ x : ℝ≥0, (x : ℝ) / (t + x) ^ 2 ∂μ) t := by
  have hdiff : DifferentiableAt ℝ (fun u : ℝ => ∫ x : ℝ≥0, u / (u + x) ∂μ) t :=
    ((contDiffOn_stieltjesBernsteinIntegral hμ).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds ht)
  have hderiv : deriv (fun u : ℝ => ∫ x : ℝ≥0, u / (u + x) ∂μ) t =
      ∫ x : ℝ≥0, (x : ℝ) / (t + x) ^ 2 ∂μ := by
    simpa [iteratedDeriv_one, div_eq_mul_inv, zpow_neg, zpow_ofNat] using
      iteratedDeriv_integral_div_add hμ 0 ht
  have hlinear : HasDerivAt (fun u : ℝ => (a : ℝ) + (b : ℝ) * u) b t := by
    simpa using ((hasDerivAt_id t).const_mul (b : ℝ)).const_add (a : ℝ)
  refine (hlinear.add (hdiff.hasDerivAt.congr_deriv hderiv)).congr_of_eventuallyEq ?_
  filter_upwards with u
  rw [stieltjesBernsteinTransform_apply]
  simp only [Pi.add_apply]

/-- The derivative formula for the Stieltjes--Bernstein transform at a positive parameter. -/
theorem deriv_stieltjesBernsteinTransform {μ : Measure ℝ≥0} {a b : ℝ≥0}
    (hμ : Integrable stieltjesWeight μ) {t : ℝ} (ht : 0 < t) :
    deriv (stieltjesBernsteinTransform μ a b) t =
      (b : ℝ) + ∫ x : ℝ≥0, (x : ℝ) / (t + x) ^ 2 ∂μ :=
  (hasDerivAt_stieltjesBernsteinTransform hμ ht).deriv

private lemma isCompletelyMonotoneOnIoi_deriv_stieltjesBernsteinIntegral
    {μ : Measure ℝ≥0} (hμ : Integrable stieltjesWeight μ) :
    IsCompletelyMonotoneOnIoi
      (deriv fun t : ℝ => ∫ x : ℝ≥0, t / (t + x) ∂μ) := by
  refine ⟨?_, ?_⟩
  · exact ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp
      (contDiffOn_stieltjesBernsteinIntegral hμ)).2
  · intro n t ht
    rw [← iteratedDeriv_succ', iteratedDeriv_integral_div_add hμ n ht]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add]
      norm_num [two_mul n]
    calc
      0 ≤ ((n + 1).factorial : ℝ) *
          ∫ x : ℝ≥0, (x : ℝ) * (t + x) ^ (-2 - (n : ℤ)) ∂μ :=
        mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun x : ℝ≥0 =>
          mul_nonneg x.coe_nonneg (zpow_nonneg (add_nonneg ht.le x.coe_nonneg) _))
      _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * (n + 1).factorial *
          ∫ x : ℝ≥0, (x : ℝ) * (t + x) ^ (-2 - (n : ℤ)) ∂μ := by rw [hsign, one_mul]
      _ = _ := by ring

private lemma continuousWithinAt_stieltjesBernsteinIntegral_zero
    {μ : Measure ℝ≥0} (hzero : μ {0} = 0) (hμ : Integrable stieltjesWeight μ) :
    ContinuousWithinAt (fun t : ℝ => ∫ x : ℝ≥0, t / (t + x) ∂μ)
      (Ici 0) 0 := by
  refine continuousWithinAt_of_dominated (μ := μ) (bound := stieltjesWeight) ?_ ?_ hμ ?_
  · exact Filter.Eventually.of_forall fun _ =>
      (measurable_const.div
        (measurable_const.add NNReal.continuous_coe.measurable)).aestronglyMeasurable
  · have hlt : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ici 0), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [eventually_mem_nhdsWithin, hlt] with t ht ht_one
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht (add_nonneg ht x.coe_nonneg))]
    rw [stieltjesWeight_apply]
    by_cases ht0 : t = 0
    · subst t
      rw [zero_div]
      exact inv_nonneg.mpr (by positivity)
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hden : 0 < t + (x : ℝ) := add_pos_of_pos_of_nonneg htpos x.coe_nonneg
      have h1x : 0 < 1 + (x : ℝ) := by positivity
      rw [inv_eq_one_div, div_le_div_iff₀ hden h1x]
      nlinarith [mul_nonneg ht x.coe_nonneg]
  · have hne : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]
      simp [hzero]
    filter_upwards [hne] with x hx
    have hx0 : (x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hx
    exact (continuousAt_id.div (continuousAt_id.add continuousAt_const)
      (by simpa using hx0)).continuousWithinAt

/-- The integral term in the Stieltjes--Bernstein transform is a Bernstein function under the
normalization and integrability hypotheses on the representing measure. -/
theorem isBernsteinFunction_integral_div_add {μ : Measure ℝ≥0}
    (hzero : μ {0} = 0) (hμ : Integrable stieltjesWeight μ) :
    IsBernsteinFunction (fun t : ℝ => ∫ x : ℝ≥0, t / (t + x) ∂μ) := by
  have hjumpCont : ContinuousOn
      (fun t : ℝ => ∫ x : ℝ≥0, t / (t + x) ∂μ) (Ici 0) := by
    intro t ht
    have ht' : 0 ≤ t := ht
    rcases ht'.eq_or_lt with rfl | ht
    · exact continuousWithinAt_stieltjesBernsteinIntegral_zero hzero hμ
    · exact ((contDiffOn_stieltjesBernsteinIntegral hμ).contDiffAt
        (isOpen_Ioi.mem_nhds ht)).continuousAt.continuousWithinAt
  rw [isBernsteinFunction_iff]
  exact ⟨hjumpCont, contDiffOn_stieltjesBernsteinIntegral hμ,
    fun t ht => integral_nonneg fun x => div_nonneg ht (add_nonneg ht x.coe_nonneg),
    isCompletelyMonotoneOnIoi_deriv_stieltjesBernsteinIntegral hμ⟩

/-- The transform built from normalized Stieltjes representing data is a Bernstein function. -/
theorem isBernsteinFunction_stieltjesBernsteinTransform {μ : Measure ℝ≥0} {a b : ℝ≥0}
    (hzero : μ {0} = 0) (hμ : Integrable stieltjesWeight μ) :
    IsBernsteinFunction (stieltjesBernsteinTransform μ a b) := by
  apply ((isBernsteinFunction_affine a.coe_nonneg b.coe_nonneg).add
    (isBernsteinFunction_integral_div_add hzero hμ)).congr
  intro t _
  rw [stieltjesBernsteinTransform_apply]
  simp only [Pi.add_apply]

namespace RepresentsStieltjes

variable {μ : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ}

/-- Multiplying a represented Stieltjes function by its parameter gives the associated Bernstein
transform on the open half-line. -/
theorem stieltjesBernsteinTransform_eq_mul (h : RepresentsStieltjes μ a b f) {t : ℝ}
    (ht : 0 < t) : stieltjesBernsteinTransform μ a b t = t * f t := by
  rw [h.eq_div_add_add_integral_inv_add ht, stieltjesBernsteinTransform_apply]
  rw [stieltjesBernsteinIntegral_eq_mul_integral_inv_add]
  field_simp [ht.ne']

/-- The transform attached to a Stieltjes representation is a Bernstein function.  Its agreement
with `t * f(t)` on `(0, ∞)` is `RepresentsStieltjes.stieltjesBernsteinTransform_eq_mul`, and its
boundary value at zero is `stieltjesBernsteinTransform_zero`. -/
theorem isBernsteinFunction_stieltjesBernsteinTransform (h : RepresentsStieltjes μ a b f) :
    IsBernsteinFunction (stieltjesBernsteinTransform μ a b) :=
  TauCeti.isBernsteinFunction_stieltjesBernsteinTransform
    h.measure_singleton_zero h.integrable_weight

end RepresentsStieltjes

namespace IsStieltjesFunction

variable {f : ℝ → ℝ}

/-- Every Stieltjes function has a Bernstein extension of its product with the parameter on the
open positive half-line. -/
theorem exists_isBernsteinFunction_eqOn_mul (h : IsStieltjesFunction f) :
    ∃ g : ℝ → ℝ, IsBernsteinFunction g ∧ EqOn g (fun t => t * f t) (Ioi 0) := by
  rw [isStieltjesFunction_iff] at h
  obtain ⟨a, b, μ, hrep⟩ := h
  exact ⟨stieltjesBernsteinTransform μ a b,
    hrep.isBernsteinFunction_stieltjesBernsteinTransform,
    fun _ ht => hrep.stieltjesBernsteinTransform_eq_mul ht⟩

end IsStieltjesFunction

end TauCeti

end

end
