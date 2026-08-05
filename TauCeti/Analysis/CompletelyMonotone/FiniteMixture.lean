/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite mixtures of completely monotone exponential functions

The extreme rays of the cone of completely monotone functions are the exponential functions
`t ↦ exp (-p * t)` with `p ≥ 0`. This file develops their finite positive mixtures. It packages
a finite mixture both as an explicit sum and as the Laplace transform of the corresponding
finite sum of weighted Dirac measures.

This is the finite-support case of the measure representation in Bernstein's theorem. In
particular, a single atom of unit weight at `p = 1` represents `t ↦ exp (-t)`, one of the
acceptance examples in the one-parameter-semigroups roadmap.

## Main declarations

* `TauCeti.finiteExponentialMixture`: a finite positive mixture of exponential extreme rays.
* `TauCeti.finiteExponentialMixtureMeasure`: the corresponding finite sum of weighted Dirac
  measures on `ℝ≥0`.
* `TauCeti.isCompletelyMonotone_finiteExponentialMixture`: every finite exponential mixture is
  completely monotone.
* `TauCeti.finiteExponentialMixture_eq_integral`: the explicit sum is the Laplace transform of
  its discrete representing measure.
* `TauCeti.integral_exp_neg_mul_dirac_one`: the acceptance example
  `exp (-t) ↔ δ₁`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- A finite positive mixture of the exponential extreme rays `t ↦ exp (-p * t)`.

The weights and rates are indexed by a finset. Both take values in `ℝ≥0`, making their
nonnegativity intrinsic to the data. -/
noncomputable def finiteExponentialMixture {ι : Type*} (s : Finset ι) (w p : ι → ℝ≥0) (t : ℝ) : ℝ :=
  ∑ i ∈ s, (w i : ℝ) * Real.exp (-(p i : ℝ) * t)

/-- The empty exponential mixture is the zero function. -/
@[simp]
theorem finiteExponentialMixture_empty {ι : Type*} (w p : ι → ℝ≥0) :
    finiteExponentialMixture ∅ w p = 0 := by
  ext t
  simp [finiteExponentialMixture]

/-- A singleton exponential mixture is one weighted exponential extreme ray. -/
@[simp]
theorem finiteExponentialMixture_singleton {ι : Type*} (i : ι) (w p : ι → ℝ≥0) (t : ℝ) :
    finiteExponentialMixture {i} w p t =
      (w i : ℝ) * Real.exp (-(p i : ℝ) * t) := by
  simp [finiteExponentialMixture]

/-- Every finite positive mixture of exponential extreme rays is completely monotone. -/
theorem isCompletelyMonotone_finiteExponentialMixture {ι : Type*} (s : Finset ι) (w p : ι → ℝ≥0) :
    IsCompletelyMonotone (finiteExponentialMixture s w p) := by
  apply IsCompletelyMonotone.sum
  intro i hi
  have hexp : IsCompletelyMonotone (fun t : ℝ => Real.exp (-(p i : ℝ) * t)) :=
    isCompletelyMonotone_exp_neg_mul (p i).coe_nonneg
  have hweighted := hexp.smul (w i).coe_nonneg
  exact hweighted.congr fun t _ => by
    simp [Pi.smul_apply, smul_eq_mul]

/-- The finite positive measure that places weight `w i` at each rate `p i`.

Repeated rates are intentionally allowed: measure addition combines their weights. -/
noncomputable def finiteExponentialMixtureMeasure {ι : Type*} (s : Finset ι)
    (w p : ι → ℝ≥0) : Measure ℝ≥0 :=
  ∑ i ∈ s, (w i : ℝ≥0∞) • Measure.dirac (p i)

/-- The representing measure of a measurable set is the sum of the weights at rates in the set. -/
@[simp]
theorem finiteExponentialMixtureMeasure_apply {ι : Type*} (s : Finset ι)
    (w p : ι → ℝ≥0) {A : Set ℝ≥0} (hA : MeasurableSet A) :
    finiteExponentialMixtureMeasure s w p A =
      ∑ i ∈ s, A.indicator (fun _ => (w i : ℝ≥0∞)) (p i) := by
  simp only [finiteExponentialMixtureMeasure, Measure.finsetSum_apply, hA,
    Measure.smul_apply, Measure.dirac_apply']
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p i ∈ A <;> simp [hi, smul_eq_mul]

/-- The empty exponential mixture has the zero representing measure. -/
@[simp]
theorem finiteExponentialMixtureMeasure_empty {ι : Type*} (w p : ι → ℝ≥0) :
    finiteExponentialMixtureMeasure ∅ w p = 0 := by
  simp [finiteExponentialMixtureMeasure]

/-- A singleton mixture has the corresponding weighted Dirac representing measure. -/
@[simp]
theorem finiteExponentialMixtureMeasure_singleton {ι : Type*} (i : ι) (w p : ι → ℝ≥0) :
    finiteExponentialMixtureMeasure {i} w p =
      (w i : ℝ≥0∞) • Measure.dirac (p i) := by
  simp [finiteExponentialMixtureMeasure]

/-- A finite exponential mixture is the Laplace transform of its discrete representing measure. -/
theorem finiteExponentialMixture_eq_integral {ι : Type*} (s : Finset ι) (w p : ι → ℝ≥0) (t : ℝ) :
    finiteExponentialMixture s w p t =
      ∫ q : ℝ≥0, Real.exp (-t * (q : ℝ)) ∂finiteExponentialMixtureMeasure s w p := by
  rw [finiteExponentialMixtureMeasure, integral_finsetSum_measure]
  · rw [finiteExponentialMixture]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac]
    simp [mul_comm]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The Laplace transform of the unit Dirac mass at `1` is `t ↦ exp (-t)`.

This is the discrete representing-measure acceptance example for Bernstein's theorem. -/
theorem integral_exp_neg_mul_dirac_one (t : ℝ) :
    (∫ q : ℝ≥0, Real.exp (-t * (q : ℝ)) ∂Measure.dirac 1) = Real.exp (-t) := by
  simp

/-- The exponential `t ↦ exp (-t)` is the unit-weight, unit-rate finite exponential mixture. -/
theorem finiteExponentialMixture_singleton_one (t : ℝ) :
    finiteExponentialMixture ({()} : Finset Unit) (fun _ => 1) (fun _ => 1) t =
      Real.exp (-t) := by
  simp [finiteExponentialMixture]

end TauCeti
