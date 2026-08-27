/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.LevyKhintchine.Representation
import TauCeti.Analysis.CompletelyMonotone.Bernstein.OpenHalfLine

/-!
# Uniqueness of the Levy--Khintchine representation

This file completes the Levy--Khintchine representation of Bernstein functions by proving that
its killing coefficient, drift coefficient, and Levy measure are unique. The killing coefficient
is the value of the exponent at zero. For the other two parameters, differentiating on the
positive half-line gives the Laplace transform of

`b delta_0 + x mu(dx)`.

Uniqueness of open-half-line Laplace representations identifies these derivative measures. Their
mass at zero recovers the drift `b`; after cancelling that atom, multiplication by `x` is
invertible away from zero, and the Levy condition `mu {0} = 0` recovers `mu`.

## Main declarations

* `TauCeti.eq_of_eqOn_bernsteinLevyKhintchineExponent`: two Levy--Khintchine triplets defining
  the same function on `[0, infinity)` are equal.
* `TauCeti.IsBernsteinFunction.existsUnique_eqOn_bernsteinLevyKhintchineExponent`: every
  Bernstein function has a unique Levy--Khintchine triplet.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 3.2.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Levy--Khintchine
  representation of Bernstein functions).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- The measure whose Laplace transform is the derivative of a Levy--Khintchine exponent:
the drift is an atom at zero, and the jump measure is weighted by the coordinate. -/
private noncomputable def bernsteinLevyKhintchineDerivativeMeasure
    (b : ℝ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  ENNReal.ofReal b • Measure.dirac 0 + bernsteinLevyDerivativeMeasure μ

private lemma integrable_exp_neg_mul_bernsteinLevyKhintchineDerivativeMeasure
    {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) {b t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (bernsteinLevyKhintchineDerivativeMeasure b μ) := by
  have hatom : Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (ENNReal.ofReal b • Measure.dirac 0) :=
    (integrable_dirac' (by fun_prop) (by simp)).smul_measure (by simp)
  have hjump : Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (bernsteinLevyDerivativeMeasure μ) :=
    integrable_exp_neg_mul_bernsteinLevyDerivativeMeasure hμ.integrable_min_one ht
  exact hatom.add_measure hjump

private lemma laplaceTransform_bernsteinLevyKhintchineDerivativeMeasure
    {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 < t) :
    laplaceTransform (bernsteinLevyKhintchineDerivativeMeasure b μ) t =
      b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ := by
  have hatom : Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (ENNReal.ofReal b • Measure.dirac 0) :=
    (integrable_dirac' (by fun_prop) (by simp)).smul_measure (by simp)
  have hjump : Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (bernsteinLevyDerivativeMeasure μ) :=
    integrable_exp_neg_mul_bernsteinLevyDerivativeMeasure hμ.integrable_min_one ht
  rw [bernsteinLevyKhintchineDerivativeMeasure,
    laplaceTransform_add_measure _ _ hatom hjump,
    laplaceTransform_smul_measure, laplaceTransform_dirac,
    ENNReal.toReal_ofReal hb, laplaceTransform_bernsteinLevyDerivativeMeasure]
  simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]

private lemma representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure
    {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) {b : ℝ} (hb : 0 ≤ b) :
    RepresentsLaplaceOnIoi (bernsteinLevyKhintchineDerivativeMeasure b μ)
      (fun t => b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ) := by
  refine representsLaplaceOnIoi_iff.mpr ⟨?_, ?_⟩
  · exact fun _ ht => integrable_exp_neg_mul_bernsteinLevyKhintchineDerivativeMeasure hμ ht
  · exact fun _ ht =>
      (laplaceTransform_bernsteinLevyKhintchineDerivativeMeasure hμ hb ht).symm

private lemma bernsteinLevyKhintchineDerivativeMeasure_singleton_zero
    {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) (b : ℝ) :
    bernsteinLevyKhintchineDerivativeMeasure b μ {0} = ENNReal.ofReal b := by
  rw [bernsteinLevyKhintchineDerivativeMeasure,
    bernsteinLevyDerivativeMeasure_eq_withDensity,
    Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_of_mem (Set.mem_singleton 0), Pi.one_apply,
    smul_eq_mul, mul_one, withDensity_apply _ (measurableSet_singleton 0)]
  rw [Measure.restrict_eq_zero.mpr hμ.measure_singleton_zero]
  simp

private lemma withDensity_coordinate_inv
    {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) :
    (bernsteinLevyDerivativeMeasure μ).withDensity
        (fun x => (x : ℝ≥0∞)⁻¹) = μ := by
  rw [bernsteinLevyDerivativeMeasure_eq_withDensity]
  apply withDensity_inv_same (by fun_prop)
  · rw [ae_iff]
    simpa only [ENNReal.coe_eq_zero, not_ne_iff, ofPred_eq_eq_singleton] using
      hμ.measure_singleton_zero
  · filter_upwards with x
    simp

/-- **Uniqueness of Levy--Khintchine triplets.** If two triplets give the same function on the
nonnegative half-line, then their killing coefficients, drift coefficients, and Levy measures
are respectively equal. -/
theorem eq_of_eqOn_bernsteinLevyKhintchineExponent
    {a b a' b' : ℝ} {μ ν : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) (hν : IsBernsteinLevyMeasure ν)
    (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (heq : Set.EqOn (bernsteinLevyKhintchineExponent a b μ)
      (bernsteinLevyKhintchineExponent a' b' ν) (Ici 0)) :
    a = a' ∧ b = b' ∧ μ = ν := by
  have ha : a = a' := by
    simpa only [bernsteinLevyKhintchineExponent_zero] using heq (mem_Ici.mpr le_rfl)
  have hderiv := (heq.mono Ioi_subset_Ici_self).deriv isOpen_Ioi
  have hlaplace : Set.EqOn
      (fun t => b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ)
      (fun t => b' + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂ν)
      (Ioi 0) := by
    intro t ht
    simpa only [deriv_bernsteinLevyKhintchineExponent hμ.integrable_min_one a b ht,
      deriv_bernsteinLevyKhintchineExponent hν.integrable_min_one a' b' ht] using hderiv ht
  have hderivativeMeasure : bernsteinLevyKhintchineDerivativeMeasure b μ =
      bernsteinLevyKhintchineDerivativeMeasure b' ν := by
    exact (representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure hμ hb).unique
      ((representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure hν hb').congr hlaplace)
  have hb_eq : b = b' := by
    have hmass := congrArg (fun ρ : Measure ℝ≥0 => ρ {0}) hderivativeMeasure
    rw [bernsteinLevyKhintchineDerivativeMeasure_singleton_zero hμ,
      bernsteinLevyKhintchineDerivativeMeasure_singleton_zero hν,
      ENNReal.ofReal_eq_ofReal_iff hb hb'] at hmass
    exact hmass
  have hweighted : bernsteinLevyDerivativeMeasure μ = bernsteinLevyDerivativeMeasure ν := by
    rw [bernsteinLevyKhintchineDerivativeMeasure,
      bernsteinLevyKhintchineDerivativeMeasure, hb_eq] at hderivativeMeasure
    let ρ := ENNReal.ofReal b' • Measure.dirac (0 : ℝ≥0)
    let _ : IsFiniteMeasure ρ := ⟨by simp [ρ]⟩
    exact (Measure.add_right_inj
      ρ _ _).mp hderivativeMeasure
  have hmeasure : μ = ν := by
    calc
      μ = (bernsteinLevyDerivativeMeasure μ).withDensity
          (fun x => (x : ℝ≥0∞)⁻¹) := (withDensity_coordinate_inv hμ).symm
      _ = (bernsteinLevyDerivativeMeasure ν).withDensity
          (fun x => (x : ℝ≥0∞)⁻¹) := by rw [hweighted]
      _ = ν := withDensity_coordinate_inv hν
  exact ⟨ha, hb_eq, hmeasure⟩

/-- **Every Bernstein function has a unique Levy--Khintchine triplet.** The components of the
triple are respectively the killing coefficient, drift coefficient, and Levy measure. -/
theorem IsBernsteinFunction.existsUnique_eqOn_bernsteinLevyKhintchineExponent
    {f : ℝ → ℝ} (hf : IsBernsteinFunction f) :
    ∃! p : ℝ × ℝ × Measure ℝ≥0,
      0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ IsBernsteinLevyMeasure p.2.2 ∧
        Set.EqOn f (bernsteinLevyKhintchineExponent p.1 p.2.1 p.2.2) (Ici 0) := by
  obtain ⟨a, b, μ, ha, hb, hμ, heq⟩ := hf.exists_eqOn_bernsteinLevyKhintchineExponent
  refine ⟨(a, b, μ), ⟨ha, hb, hμ, heq⟩, ?_⟩
  rintro ⟨a', b', ν⟩ ⟨ha', hb', hν, heq'⟩
  have htriplet := eq_of_eqOn_bernsteinLevyKhintchineExponent hμ hν hb hb' fun t ht =>
    (heq ht).symm.trans (heq' ht)
  rcases htriplet with ⟨rfl, rfl, rfl⟩
  rfl

end TauCeti

end
