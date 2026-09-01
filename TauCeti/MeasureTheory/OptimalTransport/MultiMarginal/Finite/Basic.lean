/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic
public import TauCeti.Probability.ProbabilityMassFunction.Finite

/-!
# Finite multi-marginal couplings

For finitely many finite spaces, a multi-marginal transport plan can be represented by a
probability mass function on the dependent product whose coordinate pushforwards are prescribed.
This file packages that finite model, its independent product coupling, its real-valued cost, and
the bridge to the measure-theoretic `TauCeti.MultiCoupling` API.

These definitions supply the finite coupling infrastructure used by the multi-marginal duality
development in Layer 2, item 6 of the optimal-transport roadmap.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace TauCeti

universe u v

variable {ι : Type u} {X : ι → Type v} {μ : ∀ i, PMF (X i)}

/-- A finite multi-marginal coupling is a probability mass function on the dependent product
whose pushforward by each coordinate evaluation is the prescribed marginal. -/
abbrev FiniteMultiCoupling (μ : ∀ i, PMF (X i)) :=
  {π : PMF (∀ i, X i) // ∀ i, π.map (Function.eval i) = μ i}

namespace FiniteMultiCoupling

/-- Two finite multi-marginal couplings are equal when their point masses agree. -/
@[ext]
theorem ext {π σ : FiniteMultiCoupling μ} (h : ∀ x, π.1 x = σ.1 x) : π = σ := by
  apply Subtype.ext
  exact PMF.ext h

/-- The marginal condition, in its canonical pushforward form. -/
@[simp]
theorem map_eval (π : FiniteMultiCoupling μ) (i : ι) : π.1.map (Function.eval i) = μ i :=
  π.2 i

/-- The measure of a finite multi-marginal coupling is a measure-theoretic multi-coupling of the
measures associated to its marginals. -/
theorem isMultiCoupling_toMeasure [∀ i, MeasurableSpace (X i)] (π : FiniteMultiCoupling μ) :
    Measure.IsMultiCoupling π.1.toMeasure (fun i ↦ (μ i).toMeasure) := by
  constructor
  intro i
  rw [PMF.toMeasure_map (Function.eval i) π.1 (measurable_pi_apply i), π.map_eval i]

/-- A finite multi-marginal coupling, regarded as the bundled measure-theoretic coupling of the
probability measures associated to its marginals. -/
def toMultiCoupling [∀ i, MeasurableSpace (X i)]
    (π : FiniteMultiCoupling μ) :
    MultiCoupling (fun i ↦ (⟨(μ i).toMeasure, inferInstance⟩ : ProbabilityMeasure (X i))) :=
  ⟨⟨π.1.toMeasure, inferInstance⟩, π.isMultiCoupling_toMeasure⟩

/-- The measure underlying the bundled coupling associated to a finite coupling is the measure
of its probability mass function. -/
@[simp]
theorem coe_toMultiCoupling [∀ i, MeasurableSpace (X i)]
    (π : FiniteMultiCoupling μ) :
    (π.toMultiCoupling : ProbabilityMeasure (∀ i, X i)).toMeasure = π.1.toMeasure := (rfl)

section Independent

variable [Fintype ι] [∀ i, Fintype (X i)]
attribute [local instance] Classical.decEq

/-- The independent finite multi-marginal coupling. -/
def independent (μ : ∀ i, PMF (X i)) : FiniteMultiCoupling μ := by
  let _ : ∀ i, MeasurableSpace (X i) := fun _ ↦ ⊤
  let ν : ∀ i, ProbabilityMeasure (X i) := fun i ↦ ⟨(μ i).toMeasure, inferInstance⟩
  let π : MultiCoupling ν := MultiCoupling.pi ν
  refine ⟨π.1.toMeasure.toPMF, fun i ↦ ?_⟩
  rw [← PMF.toMeasure_inj]
  rw [← PMF.toMeasure_map (Function.eval i) π.1.toMeasure.toPMF (measurable_pi_apply i)]
  rw [Measure.toPMF_toMeasure]
  exact π.2.marginal_eq i

/-- The point mass of the independent coupling is the product of its marginal point masses. -/
@[simp]
theorem independent_apply (μ : ∀ i, PMF (X i)) (x : ∀ i, X i) :
    (independent μ).1 x = ∏ i, μ i (x i) := by
  simp only [independent, Measure.toPMF_apply]
  let _ : ∀ i, MeasurableSpace (X i) := fun _ ↦ ⊤
  have hpi :
      ((MultiCoupling.pi (fun i ↦
          (⟨(μ i).toMeasure, inferInstance⟩ : ProbabilityMeasure (X i))) :
        ProbabilityMeasure (∀ i, X i)).toMeasure) =
        Measure.pi (fun i ↦ (μ i).toMeasure) := by
    erw [MultiCoupling.coe_pi]
    exact ProbabilityMeasure.toMeasure_pi _
  rw [hpi]
  rw [Measure.pi_singleton]
  simp

end Independent

/-- Every finite family of probability mass functions has a finite multi-marginal coupling. -/
instance instNonempty [Finite ι] [∀ i, Finite (X i)] :
    Nonempty (FiniteMultiCoupling μ) := by
  let _ := Fintype.ofFinite ι
  let _ : ∀ i, Fintype (X i) := fun _ ↦ Fintype.ofFinite _
  let _ := Fintype.ofFinite (∀ i, X i)
  exact ⟨independent μ⟩

section Cost

variable [Fintype (∀ i, X i)]

/-- The real cost of a finite multi-marginal coupling. -/
def cost (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) : ℝ :=
  ∑ x, c x * (π.1 x).toReal

/-- The defining finite-sum formula for the cost of a multi-marginal coupling. -/
theorem cost_def (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) :
    π.cost c = ∑ x, c x * (π.1 x).toReal := (rfl)

/-- Adding a constant to the cost adds that constant to every plan's cost. -/
@[simp]
theorem cost_add_const (c : (∀ i, X i) → ℝ) (π : FiniteMultiCoupling μ) (a : ℝ) :
    π.cost (fun x ↦ c x + a) = π.cost c + a := by
  rw [cost_def, cost_def]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, PMF.sum_toReal_eq_one, mul_one]

/-- The finite-sum cost is the integral of the cost against the measure associated to the
coupling. -/
theorem cost_eq_integral [∀ i, MeasurableSpace (X i)]
    [MeasurableSingletonClass (∀ i, X i)] (π : FiniteMultiCoupling μ)
    (c : (∀ i, X i) → ℝ) : π.cost c = ∫ x, c x ∂π.1.toMeasure := by
  rw [PMF.integral_eq_sum, cost_def]
  simp only [smul_eq_mul, mul_comm]

end Cost

end FiniteMultiCoupling

end TauCeti
