/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.LevyKhintchine.Representation
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
import TauCeti.Analysis.CompletelyMonotone.Bernstein.OpenHalfLine

/-!
# Uniqueness in the Levy--Khintchine representation

This file proves the uniqueness half of the Levy--Khintchine representation of Bernstein
functions. The derivative of the exponent with drift `b` and Levy measure `mu` is the Laplace
transform of

`b delta_0 + x mu(dx)`.

Uniqueness of Laplace transforms on the positive half-line therefore identifies these derivative
measures. Their atom at zero determines `b`; after removing that atom, multiplication by `x` is
invertible almost everywhere because a Bernstein Levy measure has no atom at zero. The killing
coefficient is already the value of the exponent at zero.

## Main declarations

* `TauCeti.bernsteinLevyKhintchineDerivativeMeasure`: the measure represented by the derivative,
  combining the drift atom and the coordinate-weighted Levy measure.
* `TauCeti.bernsteinLevyKhintchineExponent_eqOn_iff`: two admissible Levy--Khintchine exponents
  agree on `[0, infinity)` exactly when their three parameters agree.
* `TauCeti.IsBernsteinFunction.existsUnique_bernsteinLevyKhintchineExponent`: every Bernstein
  function has a unique Levy--Khintchine triplet.

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

/-- The measure whose Laplace transform is the derivative of a Levy--Khintchine exponent.
The drift is its atom at zero and the jump measure is weighted by the coordinate. -/
noncomputable def bernsteinLevyKhintchineDerivativeMeasure
    (b : ℝ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  b.toNNReal • Measure.dirac 0 + μ.withDensity fun x => (x : ℝ≥0∞)

/-- The derivative measure is the sum of the drift atom and the coordinate-weighted Levy
measure. -/
theorem bernsteinLevyKhintchineDerivativeMeasure_def (b : ℝ) (μ : Measure ℝ≥0) :
    bernsteinLevyKhintchineDerivativeMeasure b μ =
      b.toNNReal • Measure.dirac 0 + μ.withDensity fun x => (x : ℝ≥0∞) := (rfl)

private lemma integrable_exp_neg_mul_bernsteinLevyKhintchineDerivativeMeasure
    {b : ℝ} {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))))
      (bernsteinLevyKhintchineDerivativeMeasure b μ) := by
  rw [bernsteinLevyKhintchineDerivativeMeasure_def]
  apply Integrable.add_measure
  · exact (integrable_dirac' (by fun_prop) (by simp)).smul_measure (by simp)
  · rw [integrable_withDensity_iff (by fun_prop) (by simp)]
    simpa only [ENNReal.coe_toReal, mul_comm] using
      integrable_mul_exp_neg_mul_of_integrable_min_one hμ ht

private lemma laplaceTransform_bernsteinLevyKhintchineDerivativeMeasure
    {b : ℝ} (hb : 0 ≤ b) {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) {t : ℝ} (ht : 0 < t) :
    laplaceTransform (bernsteinLevyKhintchineDerivativeMeasure b μ) t =
      b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [bernsteinLevyKhintchineDerivativeMeasure_def, laplaceTransform_add_measure]
  · rw [laplaceTransform_apply, integral_smul_nnreal_measure, integral_dirac,
      laplaceTransform_apply,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
    simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, mul_one, ENNReal.coe_toReal,
      NNReal.smul_def, Real.coe_toNNReal b hb, smul_eq_mul]
  · exact (integrable_dirac' (by fun_prop) (by simp)).smul_measure (by simp)
  · rw [integrable_withDensity_iff (by fun_prop) (by simp)]
    simpa only [ENNReal.coe_toReal, mul_comm] using
      integrable_mul_exp_neg_mul_of_integrable_min_one hμ ht

/-- The derivative measure represents the derivative of its Levy--Khintchine exponent on the
positive half-line. -/
theorem representsLaplaceOnIoi_deriv_bernsteinLevyKhintchineExponent
    {a b : ℝ} (hb : 0 ≤ b) {μ : Measure ℝ≥0} (hμ : IsBernsteinLevyMeasure μ) :
    RepresentsLaplaceOnIoi (bernsteinLevyKhintchineDerivativeMeasure b μ)
      (deriv (bernsteinLevyKhintchineExponent a b μ)) := by
  rw [representsLaplaceOnIoi_iff]
  refine ⟨fun _ ht => integrable_exp_neg_mul_bernsteinLevyKhintchineDerivativeMeasure
    hμ.integrable_min_one ht, fun t ht => ?_⟩
  rw [deriv_bernsteinLevyKhintchineExponent hμ.integrable_min_one a b ht,
    laplaceTransform_bernsteinLevyKhintchineDerivativeMeasure hb hμ.integrable_min_one ht]

private lemma withDensity_coordinate_injective
    {μ ν : Measure ℝ≥0} (hμ : μ {0} = 0) (hν : ν {0} = 0)
    (h : μ.withDensity (fun x => (x : ℝ≥0∞)) =
      ν.withDensity fun x => (x : ℝ≥0∞)) : μ = ν := by
  have hμ_ne_zero : ∀ᵐ x : ℝ≥0 ∂μ, (x : ℝ≥0∞) ≠ 0 := by
    simpa [ae_iff] using hμ
  have hν_ne_zero : ∀ᵐ x : ℝ≥0 ∂ν, (x : ℝ≥0∞) ≠ 0 := by
    simpa [ae_iff] using hν
  calc
    μ = (μ.withDensity fun x => (x : ℝ≥0∞)).withDensity
        (fun x => ((x : ℝ≥0∞))⁻¹) := by
      symm
      exact withDensity_inv_same (by fun_prop) hμ_ne_zero (by simp)
    _ = (ν.withDensity fun x => (x : ℝ≥0∞)).withDensity
        (fun x => ((x : ℝ≥0∞))⁻¹) := by rw [h]
    _ = ν := withDensity_inv_same (by fun_prop) hν_ne_zero (by simp)

private lemma drift_eq_of_derivativeMeasure_eq
    {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) {μ ν : Measure ℝ≥0}
    (h : bernsteinLevyKhintchineDerivativeMeasure b μ =
      bernsteinLevyKhintchineDerivativeMeasure d ν) : b = d := by
  have hμ_zero : (μ.withDensity fun x => (x : ℝ≥0∞)) {0} = 0 :=
    (withDensity_apply_eq_zero (by fun_prop)).mpr (by simp)
  have hν_zero : (ν.withDensity fun x => (x : ℝ≥0∞)) {0} = 0 :=
    (withDensity_apply_eq_zero (by fun_prop)).mpr (by simp)
  have hzero : (b.toNNReal : ℝ≥0∞) = (d.toNNReal : ℝ≥0∞) := by
    calc
      (b.toNNReal : ℝ≥0∞) = bernsteinLevyKhintchineDerivativeMeasure b μ {0} := by
        simp [bernsteinLevyKhintchineDerivativeMeasure_def, hμ_zero]
      _ = bernsteinLevyKhintchineDerivativeMeasure d ν {0} :=
        congrArg (fun σ : Measure ℝ≥0 => σ {0}) h
      _ = (d.toNNReal : ℝ≥0∞) := by
        simp [bernsteinLevyKhintchineDerivativeMeasure_def, hν_zero]
  exact (Real.toNNReal_eq_toNNReal_iff hb hd).mp (ENNReal.coe_injective hzero)

private lemma levyMeasure_eq_of_derivativeMeasure_eq
    {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) {μ ν : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) (hν : IsBernsteinLevyMeasure ν)
    (h : bernsteinLevyKhintchineDerivativeMeasure b μ =
      bernsteinLevyKhintchineDerivativeMeasure d ν) : μ = ν := by
  have hbd := drift_eq_of_derivativeMeasure_eq hb hd h
  subst d
  rw [bernsteinLevyKhintchineDerivativeMeasure_def,
    bernsteinLevyKhintchineDerivativeMeasure_def] at h
  have hweighted : μ.withDensity (fun x => (x : ℝ≥0∞)) =
      ν.withDensity fun x => (x : ℝ≥0∞) :=
    (Measure.add_right_inj (b.toNNReal • Measure.dirac 0) _ _).mp h
  exact withDensity_coordinate_injective hμ.measure_singleton_zero hν.measure_singleton_zero
    hweighted

/-- Two admissible Levy--Khintchine exponents agree on the nonnegative half-line exactly when
their killing coefficients, drift coefficients, and Levy measures agree. -/
theorem bernsteinLevyKhintchineExponent_eqOn_iff
    {a b c d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) {μ ν : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) (hν : IsBernsteinLevyMeasure ν) :
    EqOn (bernsteinLevyKhintchineExponent a b μ)
        (bernsteinLevyKhintchineExponent c d ν) (Ici 0) ↔
      a = c ∧ b = d ∧ μ = ν := by
  constructor
  · intro hexponent
    have ha : a = c := by
      simpa only [bernsteinLevyKhintchineExponent_zero] using hexponent (mem_Ici.mpr le_rfl)
    have hderiv : EqOn (deriv (bernsteinLevyKhintchineExponent a b μ))
        (deriv (bernsteinLevyKhintchineExponent c d ν)) (Ioi 0) :=
      (hexponent.mono Ioi_subset_Ici_self).deriv isOpen_Ioi
    have hrepμ := representsLaplaceOnIoi_deriv_bernsteinLevyKhintchineExponent
      (a := a) hb hμ
    have hrepν := representsLaplaceOnIoi_deriv_bernsteinLevyKhintchineExponent
      (a := c) hd hν
    have hmeasure : bernsteinLevyKhintchineDerivativeMeasure b μ =
        bernsteinLevyKhintchineDerivativeMeasure d ν :=
      hrepμ.unique (hrepν.congr hderiv)
    exact ⟨ha, drift_eq_of_derivativeMeasure_eq hb hd hmeasure,
        levyMeasure_eq_of_derivativeMeasure_eq hb hd hμ hν hmeasure⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact fun _ _ => rfl

/-- Every Bernstein function has a Levy--Khintchine triplet, and any other admissible triplet
representing it on the nonnegative half-line has the same killing coefficient, drift coefficient,
and Levy measure. -/
theorem IsBernsteinFunction.existsUnique_bernsteinLevyKhintchineExponent
    {f : ℝ → ℝ} (hf : IsBernsteinFunction f) :
    ∃ a b : ℝ, ∃ μ : Measure ℝ≥0,
      0 ≤ a ∧ 0 ≤ b ∧ IsBernsteinLevyMeasure μ ∧
        EqOn f (bernsteinLevyKhintchineExponent a b μ) (Ici 0) ∧
        ∀ c d : ℝ, ∀ ν : Measure ℝ≥0,
          0 ≤ d → IsBernsteinLevyMeasure ν →
          EqOn f (bernsteinLevyKhintchineExponent c d ν) (Ici 0) →
          c = a ∧ d = b ∧ ν = μ := by
  obtain ⟨a, b, μ, ha, hb, hμ, hrep⟩ :=
    hf.exists_eqOn_bernsteinLevyKhintchineExponent
  refine ⟨a, b, μ, ha, hb, hμ, hrep, fun c d ν hd hν hrep' => ?_⟩
  have hexponent : EqOn (bernsteinLevyKhintchineExponent c d ν)
      (bernsteinLevyKhintchineExponent a b μ) (Ici 0) := hrep'.symm.trans hrep
  exact (bernsteinLevyKhintchineExponent_eqOn_iff hd hb hν hμ).mp hexponent

end TauCeti

end
