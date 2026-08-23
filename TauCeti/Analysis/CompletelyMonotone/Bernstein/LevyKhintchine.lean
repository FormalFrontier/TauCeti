/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Levy--Khintchine construction of Bernstein functions

This file develops the forward half of the Levy--Khintchine representation for Bernstein
functions. A measure `mu` on `ℝ≥0` is a Bernstein Levy measure when it has no atom at zero and
`min 1 x` is integrable. Its jump exponent is

`t ↦ ∫ x, (1 - exp (-t * x)) ∂mu`.

The integrability condition ensures that this integral is finite: it controls the kernel linearly
near zero and by a constant at infinity. The derivative at every positive time is the
Laplace transform of the measure with density `x` with respect to `mu`. That transform is
completely monotone, so the jump exponent, and hence its sum with nonnegative killing and drift
terms, is a Bernstein function.

## Main declarations

* `TauCeti.IsBernsteinLevyMeasure`: the standard integrability and no-atom-at-zero condition.
* `TauCeti.bernsteinLevyJumpExponent`: the jump part of a Bernstein function's
  Levy--Khintchine representation.
* `TauCeti.isBernsteinFunction_bernsteinLevyJumpExponent`: an integrable Levy jump exponent is
  a Bernstein function.
* `TauCeti.isBernsteinFunction_bernsteinLevyKhintchineExponent`: adding
  nonnegative killing and drift terms preserves the Bernstein property.

The converse direction -- extracting the unique killing coefficient, drift coefficient, and
Levy measure from an arbitrary Bernstein function -- remains separate.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 3.2.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Levy--Khintchine
  representation of Bernstein functions).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal NNReal Topology

namespace TauCeti

/-- A measure on `ℝ≥0` is a Bernstein Levy measure when it has no atom at zero and
`x ↦ min 1 x` is integrable. This is the standard Levy-measure condition for subordinators. -/
def IsBernsteinLevyMeasure (μ : Measure ℝ≥0) : Prop :=
  μ {0} = 0 ∧ Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ

/-- Characterization of a Bernstein Levy measure by its two defining conditions. -/
@[simp]
theorem isBernsteinLevyMeasure_iff {μ : Measure ℝ≥0} :
    IsBernsteinLevyMeasure μ ↔
      μ {0} = 0 ∧ Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ :=
  Iff.rfl

/-- The zero measure is a Bernstein Levy measure. -/
theorem isBernsteinLevyMeasure_zero : IsBernsteinLevyMeasure (0 : Measure ℝ≥0) := by
  simp [isBernsteinLevyMeasure_iff]

namespace IsBernsteinLevyMeasure

variable {μ ν : Measure ℝ≥0}

/-- A Bernstein Levy measure has no atom at zero. -/
@[grind =>]
lemma measure_singleton_zero (hμ : IsBernsteinLevyMeasure μ) : μ {0} = 0 := hμ.1

/-- The truncated coordinate is integrable against a Bernstein Levy measure. -/
@[grind =>]
lemma integrable_min_one (hμ : IsBernsteinLevyMeasure μ) :
    Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ := hμ.2

/-- Bernstein Levy measures are closed under addition. -/
theorem add (hμ : IsBernsteinLevyMeasure μ) (hν : IsBernsteinLevyMeasure ν) :
    IsBernsteinLevyMeasure (μ + ν) := by
  rw [isBernsteinLevyMeasure_iff]
  exact ⟨by simp [hμ.measure_singleton_zero, hν.measure_singleton_zero],
    hμ.integrable_min_one.add_measure hν.integrable_min_one⟩

end IsBernsteinLevyMeasure

/-- A Dirac mass away from zero is a Bernstein Levy measure. -/
theorem isBernsteinLevyMeasure_dirac {x : ℝ≥0} (hx : x ≠ 0) :
    IsBernsteinLevyMeasure (Measure.dirac x) := by
  rw [isBernsteinLevyMeasure_iff]
  refine ⟨by simp [hx], ?_⟩
  exact integrable_dirac' (f := fun y : ℝ≥0 => min 1 (y : ℝ)) (by fun_prop) (by simp)

/-- The jump exponent associated to a measure on `ℝ≥0`. Integrability of the truncated coordinate
guarantees integrability of its kernel at nonnegative parameters. -/
noncomputable def bernsteinLevyJumpExponent (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x : ℝ≥0, (1 - Real.exp (-(t * (x : ℝ)))) ∂μ

/-- The defining integral of the Bernstein Levy exponent. -/
@[simp]
lemma bernsteinLevyJumpExponent_apply (μ : Measure ℝ≥0) (t : ℝ) :
    bernsteinLevyJumpExponent μ t =
      ∫ x : ℝ≥0, (1 - Real.exp (-(t * (x : ℝ)))) ∂μ := by
  rw [bernsteinLevyJumpExponent]

/-- The Levy--Khintchine function with killing coefficient `a`, drift coefficient `b`, and
jump measure `μ`. -/
noncomputable def bernsteinLevyKhintchineExponent (a b : ℝ) (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  a + b * t + bernsteinLevyJumpExponent μ t

/-- The defining formula for the Bernstein Levy--Khintchine function. -/
@[simp]
lemma bernsteinLevyKhintchineExponent_apply (a b : ℝ) (μ : Measure ℝ≥0) (t : ℝ) :
    bernsteinLevyKhintchineExponent a b μ t = a + b * t + bernsteinLevyJumpExponent μ t := by
  rw [bernsteinLevyKhintchineExponent]

private lemma one_sub_exp_neg_mul_le_const_mul_min {t C : ℝ}
    (hC_one : 1 ≤ C) (hC_t : t ≤ C) (x : ℝ≥0) :
    1 - Real.exp (-(t * (x : ℝ))) ≤ C * min 1 (x : ℝ) := by
  by_cases hx : (x : ℝ) ≤ 1
  · rw [min_eq_right hx]
    have hkernel : 1 - Real.exp (-(t * (x : ℝ))) ≤ t * (x : ℝ) := by
      linarith [Real.one_sub_le_exp_neg (t * (x : ℝ))]
    calc
      1 - Real.exp (-(t * (x : ℝ))) ≤ t * (x : ℝ) := hkernel
      _ ≤ C * (x : ℝ) := mul_le_mul_of_nonneg_right hC_t x.coe_nonneg
  · rw [min_eq_left (le_of_not_ge hx)]
    calc
      1 - Real.exp (-(t * (x : ℝ))) ≤ 1 := by linarith [Real.exp_pos (-(t * (x : ℝ)))]
      _ ≤ C * 1 := by simpa using hC_one

private lemma mul_exp_neg_mul_le_const_mul_min {t : ℝ} (ht : 0 < t) (x : ℝ≥0) :
    (x : ℝ) * Real.exp (-(t * (x : ℝ))) ≤
      max 1 (Real.exp (-1) / t) * min 1 (x : ℝ) := by
  by_cases hx : (x : ℝ) ≤ 1
  · rw [min_eq_right hx]
    have hexp : Real.exp (-(t * (x : ℝ))) ≤ 1 := exp_neg_mul_le_one ht.le x
    calc
      (x : ℝ) * Real.exp (-(t * (x : ℝ))) ≤ (x : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hexp x.coe_nonneg
      _ ≤ max 1 (Real.exp (-1) / t) * (x : ℝ) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left 1 (Real.exp (-1) / t)) x.coe_nonneg
  · rw [min_eq_left (le_of_not_ge hx)]
    have hbound := Real.mul_exp_neg_le_exp_neg_one (t * (x : ℝ))
    have htne : t ≠ 0 := ne_of_gt ht
    calc
      (x : ℝ) * Real.exp (-(t * (x : ℝ))) =
          (t * (x : ℝ) * Real.exp (-(t * (x : ℝ)))) / t := by field_simp
      _ ≤ Real.exp (-1) / t := (div_le_div_iff_of_pos_right ht).mpr hbound
      _ ≤ max 1 (Real.exp (-1) / t) * 1 := by simp

/-- The Levy jump kernel is integrable at every nonnegative parameter. -/
theorem integrable_one_sub_exp_neg_mul_of_integrable_min_one {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => 1 - Real.exp (-(t * (x : ℝ)))) μ := by
  let C : ℝ := max 1 t
  refine (hμ.const_mul C).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (exp_neg_mul_le_one ht x))]
  exact one_sub_exp_neg_mul_le_const_mul_min (le_max_left _ _) (le_max_right _ _) x

/-- The derivative kernel of the Levy jump exponent is integrable at every positive
parameter. -/
theorem integrable_mul_exp_neg_mul_of_integrable_min_one {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) * Real.exp (-(t * (x : ℝ)))) μ := by
  let C : ℝ := max 1 (Real.exp (-1) / t)
  refine (hμ.const_mul C).mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg x.coe_nonneg (Real.exp_nonneg _))]
  exact mul_exp_neg_mul_le_const_mul_min ht x

/-- The jump exponent is nonnegative at nonnegative parameters. -/
theorem bernsteinLevyJumpExponent_nonneg (μ : Measure ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ bernsteinLevyJumpExponent μ t := by
  rw [bernsteinLevyJumpExponent_apply]
  exact integral_nonneg fun x => sub_nonneg.mpr (exp_neg_mul_le_one ht x)

/-- Every Levy jump exponent vanishes at zero. -/
theorem bernsteinLevyJumpExponent_zero (μ : Measure ℝ≥0) : bernsteinLevyJumpExponent μ 0 = 0 := by
  simp [bernsteinLevyJumpExponent_apply]

/-- The zero measure has identically zero Levy jump exponent. -/
theorem bernsteinLevyJumpExponent_zero_measure (t : ℝ) :
    bernsteinLevyJumpExponent (0 : Measure ℝ≥0) t = 0 := by
  simp [bernsteinLevyJumpExponent_apply]

/-- Weighting a Bernstein Levy measure by the coordinate gives the measure whose Laplace
transform is the derivative of its jump exponent. -/
private noncomputable def bernsteinLevyDerivativeMeasure (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  μ.withDensity fun x : ℝ≥0 => (x : ℝ≥0∞)

private lemma integrable_exp_neg_mul_bernsteinLevyDerivativeMeasure
    {μ : Measure ℝ≥0} (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (bernsteinLevyDerivativeMeasure μ) := by
  rw [bernsteinLevyDerivativeMeasure,
    integrable_withDensity_iff (by fun_prop) (by simp)]
  simpa only [ENNReal.coe_toReal, mul_comm] using
    integrable_mul_exp_neg_mul_of_integrable_min_one hμ ht

private lemma laplaceTransform_bernsteinLevyDerivativeMeasure
    (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform (bernsteinLevyDerivativeMeasure μ) t =
      ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [laplaceTransform_apply, bernsteinLevyDerivativeMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  simp only [ENNReal.coe_toReal, smul_eq_mul]

private theorem continuousOn_bernsteinLevyJumpExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) :
    ContinuousOn (bernsteinLevyJumpExponent μ) (Ici 0) := by
  intro t ht
  let C : ℝ := max 1 (t + 1)
  have hfilter : 𝓝[Ici 0] t ≤ 𝓝 t := nhdsWithin_le_nhds
  have hlt : Iio (t + 1) ∈ 𝓝[Ici 0] t :=
    hfilter (Iio_mem_nhds (lt_add_one t))
  rw [funext (bernsteinLevyJumpExponent_apply μ)]
  refine continuousWithinAt_of_dominated
    (μ := μ) (bound := fun x : ℝ≥0 => C * min 1 (x : ℝ)) ?_ ?_
      (hμ.const_mul C) ?_
  · filter_upwards with u
    exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ≥0 => 1 - Real.exp (-(u * (x : ℝ)))) μ)
  · filter_upwards [self_mem_nhdsWithin, hlt] with u hu hu_lt
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (exp_neg_mul_le_one hu x))]
    exact one_sub_exp_neg_mul_le_const_mul_min (le_max_left _ _)
      (hu_lt.le.trans (le_max_right _ _)) x
  · filter_upwards with x
    fun_prop

/-- At a positive parameter, a Levy jump exponent has derivative equal to the exponentially
damped first moment of its measure. -/
theorem hasDerivAt_bernsteinLevyJumpExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (bernsteinLevyJumpExponent μ)
      (∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ) t := by
  let s : Set ℝ := Ioi (t / 2)
  let bound : ℝ≥0 → ℝ := fun x => (x : ℝ) * Real.exp (-((t / 2) * (x : ℝ)))
  have ht_half : 0 < t / 2 := half_pos ht
  have hs : s ∈ 𝓝 t := Ioi_mem_nhds (half_lt_self ht)
  have hF_int := integrable_one_sub_exp_neg_mul_of_integrable_min_one hμ ht.le
  have hbound_int : Integrable bound μ :=
    integrable_mul_exp_neg_mul_of_integrable_min_one hμ ht_half
  have h_bound : ∀ᵐ x : ℝ≥0 ∂μ, ∀ u ∈ s,
      ‖(x : ℝ) * Real.exp (-(u * (x : ℝ)))‖ ≤ bound x := by
    filter_upwards with x
    intro u hu
    have hu' : t / 2 < u := by simpa only [s, mem_Ioi] using hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg x.coe_nonneg (Real.exp_nonneg _))]
    calc
      (x : ℝ) * Real.exp (-(u * (x : ℝ))) ≤
          (x : ℝ) * Real.exp (-((t / 2) * (x : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (neg_le_neg
            (mul_le_mul_of_nonneg_right hu'.le x.coe_nonneg))) x.coe_nonneg
      _ = bound x := rfl
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u (x : ℝ≥0) => 1 - Real.exp (-(u * (x : ℝ))))
    (F' := fun u (x : ℝ≥0) => (x : ℝ) * Real.exp (-(u * (x : ℝ))))
    (bound := bound) hs
    (by filter_upwards with u; exact (by fun_prop)) hF_int (by fun_prop) h_bound hbound_int
    (by
      filter_upwards with x
      intro u _hu
      have hinner := ((hasDerivAt_id u).mul_const (x : ℝ)).neg
      simpa only [id_eq, one_mul, mul_one, Pi.neg_apply, neg_mul, neg_neg, mul_comm] using
        hinner.exp.const_sub 1)
  rw [funext (bernsteinLevyJumpExponent_apply μ)]
  exact h.2

/-- At a positive parameter, the derivative of a Levy jump exponent is the exponentially
damped first moment of its Levy measure. -/
theorem deriv_bernsteinLevyJumpExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 < t) :
    deriv (bernsteinLevyJumpExponent μ) t =
      ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ :=
  (hasDerivAt_bernsteinLevyJumpExponent hμ ht).deriv

private theorem differentiableAt_bernsteinLevyJumpExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (bernsteinLevyJumpExponent μ) t :=
  (hasDerivAt_bernsteinLevyJumpExponent hμ ht).differentiableAt

private theorem isCompletelyMonotoneOnIoi_deriv_bernsteinLevyJumpExponent
    {μ : Measure ℝ≥0} (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) :
    IsCompletelyMonotoneOnIoi (deriv (bernsteinLevyJumpExponent μ)) := by
  have hcm : IsCompletelyMonotoneOnIoi (laplaceTransform (bernsteinLevyDerivativeMeasure μ)) :=
    isCompletelyMonotoneOnIoi_laplaceTransform _ fun _ ht =>
      integrable_exp_neg_mul_bernsteinLevyDerivativeMeasure hμ ht
  exact hcm.congr fun t ht => by
    rw [deriv_bernsteinLevyJumpExponent hμ ht,
      laplaceTransform_bernsteinLevyDerivativeMeasure]

/-- Integrability of `min 1 x` suffices for the Levy jump exponent to be a Bernstein function.
No condition at the origin is needed, because an atom at zero contributes the identically zero
jump kernel. -/
theorem isBernsteinFunction_bernsteinLevyJumpExponent_of_integrable_min_one
    {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) :
    IsBernsteinFunction (bernsteinLevyJumpExponent μ) := by
  have hderiv := isCompletelyMonotoneOnIoi_deriv_bernsteinLevyJumpExponent hμ
  have hcontDiff : ContDiffOn ℝ ∞ (bernsteinLevyJumpExponent μ) (Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun t ht =>
      (differentiableAt_bernsteinLevyJumpExponent hμ ht).differentiableWithinAt,
        hderiv.contDiffOn⟩
  rw [isBernsteinFunction_iff]
  exact ⟨continuousOn_bernsteinLevyJumpExponent hμ, hcontDiff,
    fun t ht => bernsteinLevyJumpExponent_nonneg μ ht, hderiv⟩

/-- A Bernstein Levy measure gives a Bernstein function through its jump exponent. -/
theorem isBernsteinFunction_bernsteinLevyJumpExponent {μ : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) :
    IsBernsteinFunction (bernsteinLevyJumpExponent μ) :=
  isBernsteinFunction_bernsteinLevyJumpExponent_of_integrable_min_one hμ.integrable_min_one

/-- Nonnegative killing and drift coefficients together with an integrable Levy jump measure give
a Bernstein function by the Levy--Khintchine formula. -/
theorem isBernsteinFunction_bernsteinLevyKhintchineExponent_of_integrable_min_one
    {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsBernsteinFunction (bernsteinLevyKhintchineExponent a b μ) := by
  apply (isBernsteinFunction_affine ha hb).add
    (isBernsteinFunction_bernsteinLevyJumpExponent_of_integrable_min_one hμ) |>.congr
  intro t _ht
  simp only [Pi.add_apply, bernsteinLevyKhintchineExponent_apply]

/-- Nonnegative killing and drift coefficients together with a Bernstein Levy measure give a
Bernstein function by the Levy--Khintchine formula. -/
theorem isBernsteinFunction_bernsteinLevyKhintchineExponent {μ : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsBernsteinFunction (bernsteinLevyKhintchineExponent a b μ) :=
  isBernsteinFunction_bernsteinLevyKhintchineExponent_of_integrable_min_one
    hμ.integrable_min_one ha hb

/-- At a nonnegative parameter, the Levy jump exponent of a sum of measures with integrable
truncated coordinates is the sum of their jump exponents. -/
theorem bernsteinLevyJumpExponent_add_measure {μ ν : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    (hν : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) ν)
    {t : ℝ} (ht : 0 ≤ t) :
    bernsteinLevyJumpExponent (μ + ν) t =
      bernsteinLevyJumpExponent μ t + bernsteinLevyJumpExponent ν t := by
  simp only [bernsteinLevyJumpExponent_apply]
  exact integral_add_measure
    (integrable_one_sub_exp_neg_mul_of_integrable_min_one hμ ht)
    (integrable_one_sub_exp_neg_mul_of_integrable_min_one hν ht)

/-- At a positive parameter, the derivative of a Levy--Khintchine exponent is its drift
coefficient plus the exponentially damped first moment of its jump measure. -/
theorem deriv_bernsteinLevyKhintchineExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    deriv (bernsteinLevyKhintchineExponent a b μ) t =
      b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ := by
  have haffine : HasDerivAt (fun u => a + b * u) b t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  rw [funext (bernsteinLevyKhintchineExponent_apply a b μ)]
  exact (haffine.add (hasDerivAt_bernsteinLevyJumpExponent hμ ht)).deriv

/-- A one-atom Levy measure gives the prototype jump exponent `1 - exp (-t x)`. -/
theorem bernsteinLevyJumpExponent_dirac (x : ℝ≥0) (t : ℝ) :
    bernsteinLevyJumpExponent (Measure.dirac x) t =
      1 - Real.exp (-(t * (x : ℝ))) := by
  simp [bernsteinLevyJumpExponent_apply]

/-- At zero, the Levy--Khintchine function is its killing coefficient. -/
theorem bernsteinLevyKhintchineExponent_zero (a b : ℝ) (μ : Measure ℝ≥0) :
    bernsteinLevyKhintchineExponent a b μ 0 = a := by
  simp [bernsteinLevyKhintchineExponent_apply]

end TauCeti

end
