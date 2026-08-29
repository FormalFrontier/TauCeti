/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompletelyMonotone
public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# From Stieltjes functions to Bernstein functions

If

`f(t) = a / t + b + integral x, (t + x)^(-1) partial mu`,

then its continuously extended product with the parameter is a Bernstein function:

`g(t) = a + b * t + integral x, t / (t + x) partial mu`.

On the open half-line this is exactly `t * f(t)`, while `g(0) = a`.  The value at zero is
essential: the literal product `0 * f(0)` would lose the coefficient of the possible `a / t`
singularity.  This is the first standard Stieltjes--Bernstein correspondence.

The proof differentiates the integral on the open half-line.  Its derivative is

`integral x, x / (t + x)^2 partial mu`,

whose derivatives have alternating signs.  Continuity at zero follows by dominated convergence;
the normalization `mu {0} = 0` removes the only point where `t / (t + x)` does not tend to zero.

## Main declarations

* `TauCeti.stieltjesBernsteinTransform`: the continuous extension of `t * f(t)` written directly
  from Stieltjes representing data.
* `TauCeti.isBernsteinFunction_stieltjesBernsteinTransform`: the transform is Bernstein.
* `TauCeti.RepresentsStieltjes.isBernsteinFunction_transform`: a Stieltjes representation produces
  a Bernstein extension agreeing with `t * f(t)` on `(0, infinity)`.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- The Bernstein function associated to Stieltjes representing data.  For positive `t`, this is
`t` times the represented Stieltjes function; the formula also supplies its continuous value `a`
at zero. -/
def stieltjesBernsteinTransform (mu : Measure NNReal) (a b : NNReal) (t : Real) : Real :=
  a + b * t + ∫ x : NNReal, t / (t + x) ∂mu

/-- Evaluation of the Stieltjes--Bernstein transform. -/
@[simp]
theorem stieltjesBernsteinTransform_apply (mu : Measure NNReal) (a b : NNReal) (t : Real) :
    stieltjesBernsteinTransform mu a b t =
      a + b * t + ∫ x : NNReal, t / (t + x) ∂mu := by
  rw [stieltjesBernsteinTransform]

/-- The Stieltjes--Bernstein transform takes the value `a` at zero. -/
@[simp]
theorem stieltjesBernsteinTransform_zero (mu : Measure NNReal) (a b : NNReal) :
    stieltjesBernsteinTransform mu a b 0 = a := by
  simp

private def stieltjesBernsteinDerivKernel (n : Nat) (t : Real) (x : NNReal) : Real :=
  (-1 : Real) ^ n * (n + 1).factorial * x *
    (t + (x : Real)) ^ (-2 - (n : Int))

private def stieltjesBernsteinDerivIntegral (mu : Measure NNReal) (n : Nat) (t : Real) : Real :=
  ∫ x, stieltjesBernsteinDerivKernel n t x ∂mu

private lemma stieltjesBernsteinDerivKernel_zero (t : Real) (x : NNReal) :
    stieltjesBernsteinDerivKernel 0 t x = (x : Real) / (t + x) ^ 2 := by
  simp [stieltjesBernsteinDerivKernel, zpow_neg, div_eq_mul_inv]

private lemma hasDerivAt_stieltjesBernsteinDerivKernel (n : Nat) (x : NNReal) {t : Real}
    (ht : 0 < t) :
    HasDerivAt (fun u => stieltjesBernsteinDerivKernel n u x)
      (stieltjesBernsteinDerivKernel (n + 1) t x) t := by
  have hne : t + (x : Real) ≠ 0 := (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
  have hbase : HasDerivAt (fun u : Real => u + (x : Real)) 1 t := by
    simpa using (hasDerivAt_id t).add_const (x : Real)
  have hpow := (hasDerivAt_zpow (-2 - (n : Int)) (t + (x : Real)) (Or.inl hne)).comp t hbase
  have h := hpow.const_mul ((-1 : Real) ^ n * (n + 1).factorial * (x : Real))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [] with u
    simp only [stieltjesBernsteinDerivKernel, Function.comp_def]
  · unfold stieltjesBernsteinDerivKernel
    have hexp : -2 - ((n + 1 : Nat) : Int) = -2 - (n : Int) - 1 := by omega
    rw [hexp]
    push_cast [Nat.factorial_succ]
    ring

private lemma integrable_stieltjesBernsteinDerivKernel
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) (n : Nat) {t : Real}
    (ht : 0 < t) : Integrable (stieltjesBernsteinDerivKernel n t) mu := by
  have hbase := integrable_zpow_neg_one_sub_add hmu n ht
  refine (hbase.const_mul ((n + 1).factorial : Real)).mono' ?_ ?_
  · have hpowCont : Continuous (fun x : NNReal =>
        (t + (x : Real)) ^ (-2 - (n : Int))) :=
      (by fun_prop : Continuous fun x : NNReal => t + (x : Real)).zpow₀ _ fun x =>
        Or.inl (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
    exact (((continuous_const.mul continuous_const).mul NNReal.continuous_coe).mul
      hpowCont).aestronglyMeasurable
  filter_upwards with x
  have htx : 0 < t + (x : Real) := add_pos_of_pos_of_nonneg ht x.coe_nonneg
  have hpow : (x : Real) * (t + (x : Real)) ^ (-2 - (n : Int)) ≤
      (t + (x : Real)) ^ (-1 - (n : Int)) := by
    rw [show -1 - (n : Int) = 1 + (-2 - (n : Int)) by omega,
      zpow_add₀ htx.ne', zpow_one]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht.le)
      (zpow_nonneg htx.le _)
  simpa only [stieltjesBernsteinDerivKernel, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, Nat.abs_cast, abs_of_nonneg x.coe_nonneg,
    abs_of_pos (zpow_pos htx _), mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (n + 1).factorial)

private lemma zpow_neg_le_zpow_neg {a b : Real} (ha : 0 < a) (hab : a ≤ b) (k : Nat) :
    b ^ (-(k : Int)) ≤ a ^ (-(k : Int)) := by
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (ha.trans_le hab) k) (pow_pos ha k)).2
    (pow_le_pow_left₀ ha.le hab k)

private lemma norm_stieltjesBernsteinDerivKernel_le (n : Nat) (x : NNReal) {r t : Real}
    (hr : 0 < r) (hrt : r <= t) :
    norm (stieltjesBernsteinDerivKernel n t x) <=
      norm (stieltjesBernsteinDerivKernel n r x) := by
  have hrx : 0 < r + (x : Real) := add_pos_of_pos_of_nonneg hr x.coe_nonneg
  have htx : 0 < t + (x : Real) := by linarith
  have hexp : -2 - (n : Int) = -((n + 2 : Nat) : Int) := by omega
  have hpow := zpow_neg_le_zpow_neg hrx (by linarith : r + (x : Real) ≤ t + x) (n + 2)
  simp only [stieltjesBernsteinDerivKernel, hexp, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, Nat.abs_cast, abs_of_nonneg x.coe_nonneg,
    abs_of_pos (zpow_pos htx _), abs_of_pos (zpow_pos hrx _)]
  have hcoeff : 0 ≤ (1 : Real) * ((n + 1).factorial : Real) * (x : Real) := by positivity
  exact mul_le_mul_of_nonneg_left hpow hcoeff

private lemma hasDerivAt_stieltjesBernsteinDerivIntegral
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) (n : Nat) {t : Real}
    (ht : 0 < t) :
    HasDerivAt (stieltjesBernsteinDerivIntegral mu n)
      (stieltjesBernsteinDerivIntegral mu (n + 1) t) t := by
  let r := t / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have htr : t ∈ Ioi r := by change r < t; dsimp [r]; linarith
  have hs : Ioi r ∈ nhds t := isOpen_Ioi.mem_nhds htr
  have hmeas : ∀ᶠ u in nhds t,
      AEStronglyMeasurable (stieltjesBernsteinDerivKernel n u) mu := by
    filter_upwards [hs] with u hu
    exact (integrable_stieltjesBernsteinDerivKernel hmu n (hr.trans hu)).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable (stieltjesBernsteinDerivKernel (n + 1) t) mu :=
    (integrable_stieltjesBernsteinDerivKernel hmu (n + 1) ht).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂mu, ∀ u ∈ Ioi r,
      ‖stieltjesBernsteinDerivKernel (n + 1) u x‖ ≤
        ‖stieltjesBernsteinDerivKernel (n + 1) r x‖ := by
    filter_upwards with x
    intro u hu
    exact norm_stieltjesBernsteinDerivKernel_le (n + 1) x hr hu.le
  have hdiff : ∀ᵐ x ∂mu, ∀ u ∈ Ioi r,
      HasDerivAt (fun v => stieltjesBernsteinDerivKernel n v x)
        (stieltjesBernsteinDerivKernel (n + 1) u x) u := by
    filter_upwards with x
    intro u hu
    exact hasDerivAt_stieltjesBernsteinDerivKernel n x (hr.trans hu)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    (integrable_stieltjesBernsteinDerivKernel hmu n ht) hderivMeas hbound
    (integrable_stieltjesBernsteinDerivKernel hmu (n + 1) hr).norm hdiff).2

private lemma contDiffOn_stieltjesBernsteinDerivIntegral
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) (n : Nat) :
    ContDiffOn Real ∞ (stieltjesBernsteinDerivIntegral mu n) (Ioi 0) := by
  rw [contDiffOn_infty]
  intro k
  induction k generalizing n with
  | zero =>
      exact contDiffOn_zero.mpr fun t ht =>
        (hasDerivAt_stieltjesBernsteinDerivIntegral hmu n ht).continuousAt.continuousWithinAt
  | succ k ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht =>
          DifferentiableAt.differentiableWithinAt
            (hasDerivAt_stieltjesBernsteinDerivIntegral hmu n ht).differentiableAt
        , by simp, ?_⟩
      exact (ih (n + 1)).congr fun t ht =>
        (hasDerivAt_stieltjesBernsteinDerivIntegral hmu n ht).deriv

private lemma iteratedDeriv_stieltjesBernsteinDerivIntegral_zero
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) (n : Nat) {t : Real}
    (ht : 0 < t) :
    iteratedDeriv n (stieltjesBernsteinDerivIntegral mu 0) t =
      stieltjesBernsteinDerivIntegral mu n t := by
  induction n generalizing t with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      have heq : iteratedDeriv n (stieltjesBernsteinDerivIntegral mu 0) =ᶠ[nhds t]
          stieltjesBernsteinDerivIntegral mu n := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu using ih hu
      rw [iteratedDeriv_succ, heq.deriv_eq,
        (hasDerivAt_stieltjesBernsteinDerivIntegral hmu n ht).deriv, Nat.add_comm n 1]

private lemma isCompletelyMonotoneOnIoi_stieltjesBernsteinDerivIntegral
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) :
    IsCompletelyMonotoneOnIoi (stieltjesBernsteinDerivIntegral mu 0) := by
  refine ⟨contDiffOn_stieltjesBernsteinDerivIntegral hmu 0, ?_⟩
  intro n t ht
  rw [iteratedDeriv_stieltjesBernsteinDerivIntegral_zero hmu n ht,
    stieltjesBernsteinDerivIntegral]
  have hint : 0 ≤ ∫ x : NNReal,
      (x : Real) * (t + (x : Real)) ^ (-2 - (n : Int)) ∂mu :=
    integral_nonneg fun x => mul_nonneg x.coe_nonneg
      (zpow_pos (add_pos_of_pos_of_nonneg ht x.coe_nonneg) _).le
  have hconst : 0 ≤ ((-1 : Real) ^ n) ^ 2 * (n + 1).factorial :=
    mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  rw [show (fun x => stieltjesBernsteinDerivKernel n t x) =
      fun x : NNReal => ((-1 : Real) ^ n * (n + 1).factorial) *
        ((x : Real) * (t + (x : Real)) ^ (-2 - (n : Int))) by
    funext x
    simp only [stieltjesBernsteinDerivKernel]
    ring]
  rw [integral_const_mul]
  nlinarith

private lemma hasDerivAt_stieltjesBernsteinIntegral
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) {t : Real} (ht : 0 < t) :
    HasDerivAt (fun u : Real => ∫ x : NNReal, u / (u + x) ∂mu)
      (stieltjesBernsteinDerivIntegral mu 0 t) t := by
  let r := t / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have htr : t ∈ Ioi r := by change r < t; dsimp [r]; linarith
  have hs : Ioi r ∈ nhds t := isOpen_Ioi.mem_nhds htr
  have hmeas : ∀ᶠ u : Real in nhds t,
      AEStronglyMeasurable (fun x : NNReal => u / (u + (x : Real))) mu := by
    filter_upwards [hs] with u hu
    exact ((integrable_inv_add hmu (hr.trans hu)).const_mul u).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable (stieltjesBernsteinDerivKernel 0 t) mu :=
    (integrable_stieltjesBernsteinDerivKernel hmu 0 ht).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂mu, ∀ u ∈ Ioi r,
      ‖stieltjesBernsteinDerivKernel 0 u x‖ ≤
        ‖stieltjesBernsteinDerivKernel 0 r x‖ := by
    filter_upwards with x
    intro u hu
    exact norm_stieltjesBernsteinDerivKernel_le 0 x hr hu.le
  have hdiff : ∀ᵐ x : NNReal ∂mu, ∀ u ∈ Ioi r,
      HasDerivAt (fun v : Real => v / (v + (x : Real)))
        (stieltjesBernsteinDerivKernel 0 u x) u := by
    filter_upwards with x
    intro u hu
    have hne : u + (x : Real) ≠ 0 :=
      (add_pos_of_pos_of_nonneg (hr.trans hu) x.coe_nonneg).ne'
    have hden : HasDerivAt (fun v : Real => v + x) 1 u := by
      simpa using (hasDerivAt_id u).add_const (x : Real)
    have hform := (hasDerivAt_const u (1 : Real)).sub ((hden.inv hne).const_mul (x : Real))
    refine (hform.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hden.continuousAt.eventually_ne hne] with v hv
      change v / (v + (x : Real)) = (1 : Real) - (x : Real) * (v + x)⁻¹
      field_simp
      ring
    · change 0 - (x : Real) * (-1 / (u + x) ^ 2) =
        stieltjesBernsteinDerivKernel 0 u x
      rw [stieltjesBernsteinDerivKernel_zero]
      field_simp
      ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas
    ((integrable_inv_add hmu ht).const_mul t) hderivMeas hbound
    (integrable_stieltjesBernsteinDerivKernel hmu 0 hr).norm hdiff).2

private lemma continuousWithinAt_stieltjesBernsteinIntegral_zero
    {mu : Measure NNReal} (hzero : mu {0} = 0) (hmu : Integrable stieltjesWeight mu) :
    ContinuousWithinAt (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (Ici 0) 0 := by
  change Tendsto (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (nhdsWithin 0 (Ici 0))
    (nhds (∫ x : NNReal, (0 : Real) / (0 + x) ∂mu))
  have hDCT : Tendsto (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (nhdsWithin 0 (Ici 0)) (nhds (∫ _x : NNReal, (0 : Real) ∂mu)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := mu) (l := nhdsWithin (0 : Real) (Ici 0))
      (F := fun (t : Real) (x : NNReal) => t / (t + (x : Real)))
      (f := fun _ : NNReal => (0 : Real))
      (bound := stieltjesWeight) ?_ ?_ hmu ?_
    · filter_upwards [eventually_mem_nhdsWithin] with t ht
      by_cases ht0 : t = 0
      · subst t
        simpa using
          (continuous_const : Continuous fun _ : NNReal => (0 : Real)).aestronglyMeasurable
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        exact (continuous_const.div (continuous_const.add NNReal.continuous_coe)
          fun x => (add_pos_of_pos_of_nonneg htpos x.coe_nonneg).ne').aestronglyMeasurable
    · have hlt : ∀ᶠ t in nhdsWithin (0 : Real) (Ici 0), t < 1 :=
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
        have hden : 0 < t + (x : Real) := add_pos_of_pos_of_nonneg htpos x.coe_nonneg
        have h1x : 0 < 1 + (x : Real) := by positivity
        rw [inv_eq_one_div, div_le_div_iff₀ hden h1x]
        nlinarith [mul_nonneg ht x.coe_nonneg]
    · have hne : ∀ᵐ x ∂mu, x ≠ 0 := by
        rw [ae_iff]
        simp [hzero]
      filter_upwards [hne] with x hx
      have hx0 : (x : Real) ≠ 0 := NNReal.coe_ne_zero.mpr hx
      have hid : Tendsto id (nhdsWithin (0 : Real) (Ici 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hquot := hid.div (hid.add_const (x : Real)) (by simpa using hx0)
      have hquot' : Tendsto (id / fun y : Real => y + (x : Real))
          (nhdsWithin 0 (Ici 0)) (nhds 0) := by simpa using hquot
      refine hquot'.congr' ?_
      filter_upwards with y
      rfl
  simpa using hDCT

/-- The transform built from normalized Stieltjes representing data is a Bernstein function. -/
theorem isBernsteinFunction_stieltjesBernsteinTransform {mu : Measure NNReal} {a b : NNReal}
    (hzero : mu {0} = 0) (hmu : Integrable stieltjesWeight mu) :
    IsBernsteinFunction (stieltjesBernsteinTransform mu a b) := by
  have hjump_cont : ContinuousOn
      (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (Ici 0) := by
    intro t ht
    have ht' : 0 ≤ t := ht
    rcases ht'.eq_or_lt with rfl | ht
    · exact continuousWithinAt_stieltjesBernsteinIntegral_zero hzero hmu
    · exact (hasDerivAt_stieltjesBernsteinIntegral hmu ht).continuousAt.continuousWithinAt
  have hderiv : EqOn (deriv (stieltjesBernsteinTransform mu a b))
      (fun t => (b : Real) + stieltjesBernsteinDerivIntegral mu 0 t) (Ioi 0) := by
    intro t ht
    have hlin : HasDerivAt (fun u : Real => (a : Real) + (b : Real) * u) b t := by
      simpa using ((hasDerivAt_id t).const_mul (b : Real)).const_add (a : Real)
    unfold stieltjesBernsteinTransform
    exact (hlin.add (hasDerivAt_stieltjesBernsteinIntegral hmu ht)).deriv
  rw [isBernsteinFunction_iff]
  have hjump_diff : DifferentiableOn Real
      (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (Ioi 0) := fun t ht =>
    (hasDerivAt_stieltjesBernsteinIntegral hmu ht).differentiableAt.differentiableWithinAt
  have hjump_deriv : EqOn (deriv fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (stieltjesBernsteinDerivIntegral mu 0) (Ioi 0) := fun t ht =>
    (hasDerivAt_stieltjesBernsteinIntegral hmu ht).deriv
  have hjump_contDiff : ContDiffOn Real ∞
      (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨hjump_diff,
      (contDiffOn_stieltjesBernsteinDerivIntegral hmu 0).congr hjump_deriv⟩
  refine ⟨(continuousOn_const.add (continuousOn_const.mul continuousOn_id)).add hjump_cont,
    ?_, ?_, ?_⟩
  · exact ((contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id)).add
      hjump_contDiff).congr fun _ _ => (stieltjesBernsteinTransform_apply mu a b _).symm
  · intro t ht
    exact add_nonneg (add_nonneg a.coe_nonneg (mul_nonneg b.coe_nonneg ht))
      (integral_nonneg fun x => div_nonneg ht (add_nonneg ht x.coe_nonneg))
  · exact ((isCompletelyMonotone_const b.coe_nonneg).isCompletelyMonotoneOnIoi.add
      (isCompletelyMonotoneOnIoi_stieltjesBernsteinDerivIntegral hmu)).congr hderiv

namespace RepresentsStieltjes

variable {mu : Measure NNReal} {a b : NNReal} {f : Real → Real}

/-- Multiplying a represented Stieltjes function by its parameter gives the associated Bernstein
transform on the open half-line. -/
theorem stieltjesBernsteinTransform_eq_mul (h : RepresentsStieltjes mu a b f) {t : Real}
    (ht : 0 < t) : stieltjesBernsteinTransform mu a b t = t * f t := by
  rw [h.eq_div_add_add_integral_inv_add ht, stieltjesBernsteinTransform_apply]
  have hint : (∫ x : NNReal, t / (t + x) ∂mu) =
      t * ∫ x : NNReal, (t + x)⁻¹ ∂mu := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp [div_eq_mul_inv]
  rw [hint]
  field_simp [ht.ne']

/-- A Stieltjes representation produces a Bernstein function that agrees with `t * f(t)` for
every positive `t` and has the canonical boundary value `a` at zero. -/
theorem isBernsteinFunction_transform (h : RepresentsStieltjes mu a b f) :
    IsBernsteinFunction (stieltjesBernsteinTransform mu a b) :=
  isBernsteinFunction_stieltjesBernsteinTransform h.measure_singleton_zero h.integrable_weight

end RepresentsStieltjes

end TauCeti

end

end
