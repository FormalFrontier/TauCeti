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
* `TauCeti.RepresentsStieltjes.isBernsteinFunction_stieltjesBernsteinTransform`: a Stieltjes
  representation produces a Bernstein extension agreeing with `t * f(t)` on `(0, infinity)`.
* `TauCeti.IsStieltjesFunction.exists_isBernsteinFunction_eq_mul`: every Stieltjes function has
  a Bernstein extension of its product with the parameter on `(0, infinity)`.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- The candidate Bernstein transform associated to Stieltjes representing data. Under the
normalization and integrability hypotheses of `isBernsteinFunction_stieltjesBernsteinTransform`,
it is a Bernstein function and is continuous at zero. For representing data, the later theorem
`RepresentsStieltjes.stieltjesBernsteinTransform_eq_mul` identifies it with `t * f t` for
positive `t`. -/
def stieltjesBernsteinTransform (mu : Measure NNReal) (a b : NNReal) (t : Real) : Real :=
  a + b * t + ∫ x : NNReal, t / (t + x) ∂mu

/-- Evaluation of the Stieltjes--Bernstein transform. -/
@[simp]
theorem stieltjesBernsteinTransform_apply (mu : Measure NNReal) (a b : NNReal) (t : Real) :
    stieltjesBernsteinTransform mu a b t =
      a + b * t + ∫ x : NNReal, t / (t + x) ∂mu := by
  rw [stieltjesBernsteinTransform]

/-- The Stieltjes--Bernstein transform takes the value `a` at zero. -/
theorem stieltjesBernsteinTransform_zero (mu : Measure NNReal) (a b : NNReal) :
    stieltjesBernsteinTransform mu a b 0 = a := by
  simp

private lemma stieltjesBernsteinIntegral_eq_mul_integral_inv_add (mu : Measure NNReal)
    (t : Real) :
    (∫ x : NNReal, t / (t + x) ∂mu) =
      t * ∫ x : NNReal, (t + x)⁻¹ ∂mu := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv])

private lemma integral_stieltjesBernsteinDerivKernel_eq_sub {mu : Measure NNReal}
    (hmu : Integrable stieltjesWeight mu) {t : Real} (ht : 0 < t) :
    (∫ x : NNReal, (x : Real) / (t + x) ^ 2 ∂mu) =
      (∫ x : NNReal, (t + x)⁻¹ ∂mu) -
        t * ∫ x : NNReal, (t + x) ^ (-2 : Int) ∂mu := by
  have hpowInt : Integrable (fun x : NNReal => (t + (x : Real)) ^ (-2 : Int)) mu := by
    simpa using integrable_zpow_neg_one_sub_add hmu 1 ht
  rw [← integral_const_mul,
    ← integral_sub (integrable_inv_add hmu ht) (hpowInt.const_mul t)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    have htx : t + (x : Real) ≠ 0 :=
      (add_pos_of_pos_of_nonneg ht x.coe_nonneg).ne'
    have hzpow : (t + (x : Real)) ^ (-2 : Int) = ((t + (x : Real)) ^ 2)⁻¹ := by
      rw [zpow_neg, zpow_ofNat]
    dsimp only
    rw [hzpow, inv_eq_one_div]
    field_simp
    ring)

private lemma contDiffOn_stieltjesBernsteinIntegral {mu : Measure NNReal}
    (hmu : Integrable stieltjesWeight mu) :
    ContDiffOn Real ∞ (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (Ioi 0) := by
  refine (contDiffOn_id.mul
    (isCompletelyMonotoneOnIoi_integral_inv_add hmu).contDiffOn).congr fun t _ => ?_
  simpa only [id_eq] using stieltjesBernsteinIntegral_eq_mul_integral_inv_add mu t

/-- The derivative of the Stieltjes--Bernstein transform at a positive parameter. -/
theorem hasDerivAt_stieltjesBernsteinTransform {mu : Measure NNReal} {a b : NNReal}
    (hmu : Integrable stieltjesWeight mu) {t : Real} (ht : 0 < t) :
    HasDerivAt (stieltjesBernsteinTransform mu a b)
      ((b : Real) + ∫ x : NNReal, (x : Real) / (t + x) ^ 2 ∂mu) t := by
  let F := fun u : Real => ∫ x : NNReal, (u + (x : Real))⁻¹ ∂mu
  have hFdiff : DifferentiableAt Real F t :=
    ((isCompletelyMonotoneOnIoi_integral_inv_add hmu).contDiffOn.differentiableOn
      (by simp)).differentiableAt (isOpen_Ioi.mem_nhds ht)
  have hFderiv : deriv F t = -∫ x : NNReal, (t + (x : Real)) ^ (-2 : Int) ∂mu := by
    simpa [F, iteratedDeriv_one] using
      iteratedDeriv_integral_inv_add hmu 1 ht
  have hjump : HasDerivAt (fun u => u * F u)
      (∫ x : NNReal, (x : Real) / (t + x) ^ 2 ∂mu) t := by
    refine ((hasDerivAt_id t).mul hFdiff.hasDerivAt).congr_deriv ?_
    rw [hFderiv]
    rw [integral_stieltjesBernsteinDerivKernel_eq_sub hmu ht]
    simp only [F, id_eq]
    ring
  have hlinear : HasDerivAt (fun u : Real => (a : Real) + (b : Real) * u) b t := by
    simpa using ((hasDerivAt_id t).const_mul (b : Real)).const_add (a : Real)
  refine ((hlinear.add hjump).congr_of_eventuallyEq ?_).congr_deriv rfl
  filter_upwards [] with u
  rw [stieltjesBernsteinTransform_apply,
    stieltjesBernsteinIntegral_eq_mul_integral_inv_add]
  rfl

/-- The derivative formula for the Stieltjes--Bernstein transform at a positive parameter. -/
theorem deriv_stieltjesBernsteinTransform {mu : Measure NNReal} {a b : NNReal}
    (hmu : Integrable stieltjesWeight mu) {t : Real} (ht : 0 < t) :
    deriv (stieltjesBernsteinTransform mu a b) t =
      (b : Real) + ∫ x : NNReal, (x : Real) / (t + x) ^ 2 ∂mu :=
  (hasDerivAt_stieltjesBernsteinTransform hmu ht).deriv

private lemma isCompletelyMonotoneOnIoi_deriv_stieltjesBernsteinIntegral
    {mu : Measure NNReal} (hmu : Integrable stieltjesWeight mu) :
    IsCompletelyMonotoneOnIoi
      (deriv fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) := by
  let F := fun u : Real => ∫ x : NNReal, (u + (x : Real))⁻¹ ∂mu
  have hFcm : IsCompletelyMonotoneOnIoi F :=
    isCompletelyMonotoneOnIoi_integral_inv_add hmu
  have hjumpContDiff : ContDiffOn Real ∞ (fun t => t * F t) (Ioi 0) :=
    contDiffOn_id.mul hFcm.contDiffOn
  have hjumpEq : EqOn (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (fun t => t * F t) (Ioi 0) := fun t _ =>
    stieltjesBernsteinIntegral_eq_mul_integral_inv_add mu t
  have hderivEq : EqOn
      (deriv fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (deriv fun t => t * F t) (Ioi 0) := fun t ht =>
    (hjumpEq.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht)).deriv_eq
  refine ⟨?_, ?_⟩
  · rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi] at hjumpContDiff
    exact hjumpContDiff.2.congr hderivEq
  · intro n t ht
    rw [(hderivEq.eventuallyEq_of_mem
      (isOpen_Ioi.mem_nhds ht)).iteratedDeriv_eq n, ← iteratedDeriv_succ']
    have hFdiff : ContDiffAt Real (n + 1 : Nat) F t :=
      (hFcm.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by simp)
    have hmulFun : (fun u => u * F u) = id * F := rfl
    rw [hmulFun, iteratedDeriv_mul contDiffAt_id hFdiff]
    rw [← Finset.add_sum_erase _ _
      (by simp : 0 ∈ Finset.range (n + 1 + 1))]
    rw [← Finset.add_sum_erase _ _
      (by simp : 1 ∈ (Finset.range (n + 1 + 1)).erase 0)]
    have hrest :
        (∑ x ∈ ((Finset.range (n + 1 + 1)).erase 0).erase 1,
          ((n + 1).choose x : Real) * iteratedDeriv x id t *
            iteratedDeriv (n + 1 - x) F t) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [iteratedDeriv_id, hx0, hx1]
    rw [hrest]
    have hid0 : iteratedDeriv 0 id t = t := by simp
    have hid1 : iteratedDeriv 1 id t = 1 := by simp [iteratedDeriv_one]
    rw [hid0, hid1]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul,
      Nat.sub_zero, add_zero]
    rw [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one]
    have hn := iteratedDeriv_integral_inv_add hmu n ht
    have hn1 := iteratedDeriv_integral_inv_add hmu (n + 1) ht
    have hexpSucc : -1 - ((n + 1 : Nat) : Int) = -2 - (n : Int) := by omega
    rw [hexpSucc] at hn1
    rw [hn, hn1]
    have hle : t * ∫ x : NNReal,
          (t + (x : Real)) ^ (-2 - (n : Int)) ∂mu ≤
        ∫ x : NNReal, (t + (x : Real)) ^ (-1 - (n : Int)) ∂mu := by
      have hIntSucc : Integrable
          (fun x : NNReal => (t + (x : Real)) ^ (-2 - (n : Int))) mu := by
        simpa only [hexpSucc] using integrable_zpow_neg_one_sub_add hmu (n + 1) ht
      rw [← integral_const_mul]
      exact integral_mono
        (hIntSucc.const_mul t)
        (integrable_zpow_neg_one_sub_add hmu n ht) fun x => by
          have htx : 0 < t + (x : Real) :=
            add_pos_of_pos_of_nonneg ht x.coe_nonneg
          have hexp : -1 - (n : Int) = 1 + (-2 - (n : Int)) := by omega
          rw [hexp, zpow_add₀ htx.ne', zpow_one]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right x.coe_nonneg)
            (zpow_nonneg htx.le _)
    have hsign : (-1 : Real) ^ n * (-1 : Real) ^ n = 1 := by
      rw [← pow_add]
      norm_num [two_mul n]
    have heq :
        (-1 : Real) ^ n *
          (t * ((-1 : Real) ^ (n + 1) * (n + 1).factorial *
              ∫ x : NNReal, (t + (x : Real)) ^ (-2 - (n : Int)) ∂mu) +
            ((n : Real) + 1) * ((-1 : Real) ^ n * n.factorial *
              ∫ x : NNReal, (t + (x : Real)) ^ (-1 - (n : Int)) ∂mu)) =
          ((n + 1).factorial : Real) *
            ((∫ x : NNReal, (t + (x : Real)) ^ (-1 - (n : Int)) ∂mu) -
              t * ∫ x : NNReal,
                (t + (x : Real)) ^ (-2 - (n : Int)) ∂mu) := by
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      calc
        _ = ((-1 : Real) ^ n * (-1 : Real) ^ n) * ((n : Real) + 1) * n.factorial *
              ((∫ x : NNReal, (t + (x : Real)) ^ (-1 - (n : Int)) ∂mu) -
                t * ∫ x : NNReal,
                  (t + (x : Real)) ^ (-2 - (n : Int)) ∂mu) := by ring
        _ = _ := by rw [hsign]; ring
    rw [heq]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hle)

private lemma continuousWithinAt_stieltjesBernsteinIntegral_zero
    {mu : Measure NNReal} (hzero : mu {0} = 0) (hmu : Integrable stieltjesWeight mu) :
    ContinuousWithinAt (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu)
      (Ici 0) 0 := by
  -- Expose the filter formulation required by dominated convergence.
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

private lemma isBernsteinFunction_stieltjesBernsteinIntegral {mu : Measure NNReal}
    (hzero : mu {0} = 0) (hmu : Integrable stieltjesWeight mu) :
    IsBernsteinFunction (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) := by
  have hjumpCont : ContinuousOn
      (fun t : Real => ∫ x : NNReal, t / (t + x) ∂mu) (Ici 0) := by
    intro t ht
    have ht' : 0 ≤ t := ht
    rcases ht'.eq_or_lt with rfl | ht
    · exact continuousWithinAt_stieltjesBernsteinIntegral_zero hzero hmu
    · exact ((contDiffOn_stieltjesBernsteinIntegral hmu).contDiffAt
        (isOpen_Ioi.mem_nhds ht)).continuousAt.continuousWithinAt
  rw [isBernsteinFunction_iff]
  exact ⟨hjumpCont, contDiffOn_stieltjesBernsteinIntegral hmu,
    fun t ht => integral_nonneg fun x => div_nonneg ht (add_nonneg ht x.coe_nonneg),
    isCompletelyMonotoneOnIoi_deriv_stieltjesBernsteinIntegral hmu⟩

/-- The transform built from normalized Stieltjes representing data is a Bernstein function. -/
theorem isBernsteinFunction_stieltjesBernsteinTransform {mu : Measure NNReal} {a b : NNReal}
    (hzero : mu {0} = 0) (hmu : Integrable stieltjesWeight mu) :
    IsBernsteinFunction (stieltjesBernsteinTransform mu a b) := by
  apply ((isBernsteinFunction_affine a.coe_nonneg b.coe_nonneg).add
    (isBernsteinFunction_stieltjesBernsteinIntegral hzero hmu)).congr
  intro t _
  rw [stieltjesBernsteinTransform_apply]
  simp only [Pi.add_apply]

namespace RepresentsStieltjes

variable {mu : Measure NNReal} {a b : NNReal} {f : Real → Real}

/-- Multiplying a represented Stieltjes function by its parameter gives the associated Bernstein
transform on the open half-line. -/
theorem stieltjesBernsteinTransform_eq_mul (h : RepresentsStieltjes mu a b f) {t : Real}
    (ht : 0 < t) : stieltjesBernsteinTransform mu a b t = t * f t := by
  rw [h.eq_div_add_add_integral_inv_add ht, stieltjesBernsteinTransform_apply]
  rw [stieltjesBernsteinIntegral_eq_mul_integral_inv_add]
  field_simp [ht.ne']

/-- A Stieltjes representation produces a Bernstein function that agrees with `t * f(t)` for
every positive `t` and has the canonical boundary value `a` at zero. -/
theorem isBernsteinFunction_stieltjesBernsteinTransform (h : RepresentsStieltjes mu a b f) :
    IsBernsteinFunction (stieltjesBernsteinTransform mu a b) :=
  TauCeti.isBernsteinFunction_stieltjesBernsteinTransform
    h.measure_singleton_zero h.integrable_weight

end RepresentsStieltjes

namespace IsStieltjesFunction

variable {f : Real → Real}

/-- Every Stieltjes function has a Bernstein extension of its product with the parameter on the
open positive half-line. -/
theorem exists_isBernsteinFunction_eq_mul (h : IsStieltjesFunction f) :
    ∃ g : Real → Real, IsBernsteinFunction g ∧ EqOn g (fun t => t * f t) (Ioi 0) := by
  rw [isStieltjesFunction_iff] at h
  obtain ⟨a, b, mu, hrep⟩ := h
  exact ⟨stieltjesBernsteinTransform mu a b,
    hrep.isBernsteinFunction_stieltjesBernsteinTransform,
    fun _ ht => hrep.stieltjesBernsteinTransform_eq_mul ht⟩

end IsStieltjesFunction

end TauCeti

end

end
