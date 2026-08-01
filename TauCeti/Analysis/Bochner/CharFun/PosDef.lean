/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order

/-!
# A finite measure's characteristic function is positive definite

This file proves the "easy" (necessary) direction of Bochner's theorem: the characteristic
function `charFun μ` of a finite measure `μ` on a real inner product space `E` is a
*positive-definite function*. Concretely, for every finite family `(cᵢ, tᵢ)` the Hermitian
form

`∑ᵢ ∑ⱼ cᵢ · conj cⱼ · charFun μ (tᵢ - tⱼ)`

is a nonnegative real number (`charFun_sum_mul_conj_nonneg`), equivalently the matrix
`(charFun μ (tᵢ - tⱼ))ᵢⱼ` is positive semidefinite (`charFun_posSemidef`). The proof is the
classical computation: the Hermitian form equals the honest integral

`∫ y, ‖∑ᵢ cᵢ · exp (⟪y, tᵢ⟫ * I)‖² ∂μ`

of a nonnegative integrand (`charFun_sum_mul_conj_eq_integral`), because
`exp (⟪y, tᵢ⟫ * I) · conj (exp (⟪y, tⱼ⟫ * I)) = exp (⟪y, tᵢ - tⱼ⟫ * I)` makes the double sum
factor through a squared modulus.

This is the roadmap's bridge lemma `pd_quadratic_form_of_measure`
(`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C — "Positive-definite functions and
Bochner's theorem", the `API to develop` bullet "a finite measure's Fourier transform is
continuous positive-definite"). It is stated directly on Mathlib's `MeasureTheory.charFun`, so
it needs no positive-definiteness *predicate*; it is exactly the half of Bochner's theorem
that is provable without the harder measure-extraction (Riesz–Markov / Lévy–Prokhorov)
machinery.

`charFun` and `innerProbChar` are from
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`; positive semidefiniteness
of complex matrices is Mathlib's `Matrix.PosSemidef`.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate

open scoped ComplexOrder Matrix

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

private theorem integrable_innerProbChar (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ := by
  have h : (fun y => exp (⟪y, a⟫ * I)) = ⇑(innerProbChar a) := by
    ext y; rw [innerProbChar_apply]
  rw [h]; exact (innerProbChar a).integrable (μ := μ)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem exp_mul_conj_exp_inner (y a b : E) :
    exp (⟪y, a⟫ * I) * conj (exp (⟪y, b⟫ * I)) = exp (⟪y, a - b⟫ * I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [inner_sub_right, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem normSq_finset_sum_exp_eq_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (t : ι → E) (y : E) : ((normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) : ℝ) : ℂ)
      = ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) := by
  have hconj : conj (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I))
      = ∑ j ∈ s, conj (c j) * conj (exp (⟪y, t j⟫ * I)) := by
    rw [map_sum]; simp only [map_mul]
  rw [← mul_conj, hconj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← exp_mul_conj_exp_inner y (t i) (t j)]
  ring

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` equals the integral of a
squared modulus. This is the engine behind positive-definiteness: the right-hand side is the
integral of a manifestly nonnegative function. -/
theorem charFun_sum_mul_conj_eq_integral {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j)
      = ((∫ y, normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) ∂μ : ℝ) : ℂ) := by
  -- integrability of the building blocks
  have hterm : ∀ i j : ι,
      Integrable (fun y => c i * conj (c j) * exp (⟪y, t i - t j⟫ * I)) μ :=
    fun i j => (integrable_innerProbChar (t i - t j)).const_mul _
  have hrow : ∀ i : ι,
      Integrable (fun y => ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I)) μ :=
    fun i => integrable_finsetSum s fun j _ => hterm i j
  calc ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j)
      = ∑ i ∈ s, ∑ j ∈ s, ∫ y, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [charFun_apply, integral_const_mul]
    _ = ∑ i ∈ s, ∫ y, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (integral_finsetSum s fun j _ => hterm i j).symm
    _ = ∫ y, ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * exp (⟪y, t i - t j⟫ * I) ∂μ :=
        (integral_finsetSum s fun i _ => hrow i).symm
    _ = ∫ y, ((normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) : ℝ) : ℂ) ∂μ :=
        integral_congr_ae (.of_forall fun y => (normSq_finset_sum_exp_eq_sum s c t y).symm)
    _ = ((∫ y, normSq (∑ i ∈ s, c i * exp (⟪y, t i⟫ * I)) ∂μ : ℝ) : ℂ) := integral_complex_ofReal

/-- The Hermitian form of `charFun μ` over a finite family `(cᵢ, tᵢ)` is a nonnegative real:
`charFun μ` is a positive-definite function. This is `pd_quadratic_form_of_measure`. -/
theorem charFun_sum_mul_conj_nonneg {ι : Type*} (s : Finset ι) (c : ι → ℂ) (t : ι → E) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * charFun μ (t i - t j) := by
  rw [charFun_sum_mul_conj_eq_integral, Complex.zero_le_real]
  exact integral_nonneg fun y => normSq_nonneg _

/-- The `Fintype`-indexed form of positive-definiteness: summing over all of a finite index
type. -/
theorem charFun_fintype_sum_mul_conj_nonneg {ι : Type*} [Fintype ι] (c : ι → ℂ) (t : ι → E) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * charFun μ (t i - t j) :=
  charFun_sum_mul_conj_nonneg Finset.univ c t

/-- The matrix `(charFun μ (tᵢ - tⱼ))ᵢⱼ` of a finite measure is positive semidefinite: the
matrix reformulation of the positive-definiteness of `charFun μ`. -/
theorem charFun_posSemidef {ι : Type*} (t : ι → E) :
    (Matrix.of fun i j => charFun μ (t i - t j)).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · -- Hermitian: `conj (charFun μ (tⱼ - tᵢ)) = charFun μ (tᵢ - tⱼ)`
    have h : ∀ i j : ι, conj (charFun μ (t j - t i)) = charFun μ (t i - t j) := by
      intro i j
      have hsub : t j - t i = -(t i - t j) := by abel
      rw [hsub, charFun_neg, Complex.conj_conj]
    ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.of_apply, ← starRingEnd_apply] using h i j
  · -- the Hermitian form is nonnegative
    simp only [Finsupp.sum, Matrix.of_apply, ← starRingEnd_apply]
    have h := charFun_sum_mul_conj_nonneg (μ := μ) x.support (fun i => conj (x i)) t
    have heq : (∑ i ∈ x.support, ∑ j ∈ x.support, conj (x i) * charFun μ (t i - t j) * x j)
        = ∑ i ∈ x.support, ∑ j ∈ x.support,
            conj (x i) * conj (conj (x j)) * charFun μ (t i - t j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.conj_conj]; ring
    rw [heq]; exact h

end TauCeti
