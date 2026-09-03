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
is the value of the exponent at zero, which agreement on the positive half-line already fixes
because the exponent is continuous at that endpoint. For the other two parameters,
differentiating on the positive half-line gives the Laplace transform of

`b delta_0 + x mu(dx)`.

Uniqueness of open-half-line Laplace representations identifies these derivative measures. Their
mass at zero recovers the drift `b`; after cancelling that atom, multiplication by `x` is
invertible away from zero, and the Levy condition `mu {0} = 0` recovers `mu`.

## Main declarations

* `TauCeti.eq_of_eqOn_bernsteinLevyKhintchineExponent`: two Levy--Khintchine triplets defining
  the same function on `(0, infinity)` are equal.
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
  (b.toNNReal : ℝ≥0∞) • Measure.dirac 0 + bernsteinLevyDerivativeMeasure μ

private lemma representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure
    {μ : Measure ℝ≥0} (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ)
    {b : ℝ} (hb : 0 ≤ b) :
    RepresentsLaplaceOnIoi (bernsteinLevyKhintchineDerivativeMeasure b μ)
      (fun t => b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ) :=
  ((((representsLaplace_dirac (0 : ℝ≥0)).representsLaplaceOnIoi).smul b.toNNReal).add
    (representsLaplaceOnIoi_bernsteinLevyDerivativeMeasure hμ)).congr fun _ _ => by
      simp [Real.coe_toNNReal b hb]

private lemma bernsteinLevyKhintchineDerivativeMeasure_singleton_zero
    (b : ℝ) (μ : Measure ℝ≥0) :
    bernsteinLevyKhintchineDerivativeMeasure b μ {0} = (b.toNNReal : ℝ≥0∞) := by
  have hjump : bernsteinLevyDerivativeMeasure μ {0} = 0 := by
    rw [bernsteinLevyDerivativeMeasure_apply μ (measurableSet_singleton 0)]
    simp
  rw [bernsteinLevyKhintchineDerivativeMeasure, Measure.add_apply, hjump]
  simp

/-- The Levy--Khintchine exponent of a measure with integrable truncated coordinate is
continuous on the nonnegative half-line. -/
private lemma continuousOn_bernsteinLevyKhintchineExponent {μ : Measure ℝ≥0}
    (hμ : Integrable (fun x : ℝ≥0 => min 1 (x : ℝ)) μ) (a b : ℝ) :
    ContinuousOn (bernsteinLevyKhintchineExponent a b μ) (Ici 0) := by
  rw [funext (bernsteinLevyKhintchineExponent_apply a b μ)]
  exact (Continuous.continuousOn (by fun_prop)).add
    (continuousOn_bernsteinLevyJumpExponent hμ)

/-- **Uniqueness of Levy--Khintchine triplets.** If two triplets give the same function on the
positive half-line, then their killing coefficients, drift coefficients, and Levy measures
are respectively equal. -/
theorem eq_of_eqOn_bernsteinLevyKhintchineExponent
    {a b a' b' : ℝ} {μ ν : Measure ℝ≥0}
    (hμ : IsBernsteinLevyMeasure μ) (hν : IsBernsteinLevyMeasure ν)
    (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (heq : Set.EqOn (bernsteinLevyKhintchineExponent a b μ)
      (bernsteinLevyKhintchineExponent a' b' ν) (Ioi 0)) :
    a = a' ∧ b = b' ∧ μ = ν := by
  have ha : a = a' := by
    have heqIci := heq.of_subset_closure
      (continuousOn_bernsteinLevyKhintchineExponent hμ.integrable_min_one a b)
      (continuousOn_bernsteinLevyKhintchineExponent hν.integrable_min_one a' b')
      Ioi_subset_Ici_self (by rw [closure_Ioi])
    simpa only [bernsteinLevyKhintchineExponent_zero] using heqIci (mem_Ici.mpr le_rfl)
  have hderiv := heq.deriv isOpen_Ioi
  have hlaplace : Set.EqOn
      (fun t => b + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂μ)
      (fun t => b' + ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ))) ∂ν)
      (Ioi 0) := by
    intro t ht
    simpa only [deriv_bernsteinLevyKhintchineExponent hμ.integrable_min_one a b ht,
      deriv_bernsteinLevyKhintchineExponent hν.integrable_min_one a' b' ht] using hderiv ht
  have hderivativeMeasure : bernsteinLevyKhintchineDerivativeMeasure b μ =
      bernsteinLevyKhintchineDerivativeMeasure b' ν :=
    (representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure
        hμ.integrable_min_one hb).unique
      ((representsLaplaceOnIoi_bernsteinLevyKhintchineDerivativeMeasure
        hν.integrable_min_one hb').congr hlaplace)
  have hb_eq : b = b' := by
    have hmass := congrArg (fun ρ : Measure ℝ≥0 => ρ {0}) hderivativeMeasure
    rw [bernsteinLevyKhintchineDerivativeMeasure_singleton_zero,
      bernsteinLevyKhintchineDerivativeMeasure_singleton_zero, ENNReal.coe_inj] at hmass
    simpa only [Real.coe_toNNReal b hb, Real.coe_toNNReal b' hb'] using
      congrArg (fun c : ℝ≥0 => (c : ℝ)) hmass
  have hweighted : bernsteinLevyDerivativeMeasure μ = bernsteinLevyDerivativeMeasure ν := by
    simp only [bernsteinLevyKhintchineDerivativeMeasure, hb_eq] at hderivativeMeasure
    have : IsFiniteMeasure ((b'.toNNReal : ℝ≥0∞) • Measure.dirac (0 : ℝ≥0)) :=
      Measure.smul_finite _ (by simp)
    simpa using hderivativeMeasure
  have hmeasure : μ = ν := by
    calc
      μ = (bernsteinLevyDerivativeMeasure μ).withDensity
          (fun x => (x : ℝ≥0∞)⁻¹) :=
        (withDensity_inv_bernsteinLevyDerivativeMeasure hμ.measure_singleton_zero).symm
      _ = (bernsteinLevyDerivativeMeasure ν).withDensity
          (fun x => (x : ℝ≥0∞)⁻¹) := by rw [hweighted]
      _ = ν := withDensity_inv_bernsteinLevyDerivativeMeasure hν.measure_singleton_zero
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
    (heq (Ioi_subset_Ici_self ht)).symm.trans (heq' (Ioi_subset_Ici_self ht))
  rcases htriplet with ⟨rfl, rfl, rfl⟩
  rfl

end TauCeti

end
