/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Chebyshev `T` transfer to cosine integrals

This file packages the cosine-side consequences of Mathlib's change of variables
for the Chebyshev orthogonality measure.  The roadmap's Chebyshev Hilbert-basis
target later identifies the normalized Chebyshev functions on `measureT` with
the cosine basis under `x = cos θ`; the lemmas here expose the one-dimensional
integral API needed for that transfer, including the normalized angular modes.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- The cosine-side representative corresponding to the Chebyshev polynomial `Tₙ`. -/
noncomputable def chebyshevCosine (n : ℕ) (θ : ℝ) : ℝ :=
  Real.cos (n * θ)

/-- The defining equation for the cosine-side Chebyshev representative. -/
lemma chebyshevCosine_def (n : ℕ) (θ : ℝ) : chebyshevCosine n θ = Real.cos (n * θ) :=
  chebyshevCosine.eq_1 n θ

@[simp]
lemma chebyshevCosine_zero (θ : ℝ) : chebyshevCosine 0 θ = 1 := by
  simp [chebyshevCosine_def]

@[simp]
lemma chebyshevCosine_one (θ : ℝ) : chebyshevCosine 1 θ = Real.cos θ := by
  simp [chebyshevCosine_def]

/-- Chebyshev polynomials restrict along `x = cos θ` to the cosine functions. -/
lemma eval_T_real_cos_eq_chebyshevCosine (n : ℕ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) = chebyshevCosine n θ := by
  simp [chebyshevCosine_def, Polynomial.Chebyshev.T_real_cos]

/-- The cosine-side representatives are continuous. -/
lemma continuous_chebyshevCosine (n : ℕ) : Continuous (chebyshevCosine n) := by
  have h : Continuous (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  exact h.congr fun θ => (chebyshevCosine_def n θ).symm

/-- Transfer a single Chebyshev `T` integral from `measureT` to the angular
cosine-side integral. -/
lemma integral_eval_T_real_measureT_eq_integral_chebyshevCosine (n : ℕ) :
    ∫ x, (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, chebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [chebyshevCosine_def]

/-- Transfer a product of two Chebyshev `T` polynomials from `measureT` to the
angular cosine-side integral. -/
lemma integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul
    (m n : ℕ) :
    ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [chebyshevCosine_def]

/-- The cosine-side integral of the constant Chebyshev mode. -/
lemma integral_chebyshevCosine_zero :
    ∫ θ in (0)..Real.pi, chebyshevCosine 0 θ = Real.pi := by
  rw [← integral_eval_T_real_measureT_eq_integral_chebyshevCosine]
  exact integral_eval_T_real_measureT_zero

/-- Nonzero cosine modes have zero integral over `[0, π]`. -/
lemma integral_chebyshevCosine_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ θ in (0)..Real.pi, chebyshevCosine n θ = 0 := by
  rw [← integral_eval_T_real_measureT_eq_integral_chebyshevCosine]
  exact integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hn)

/-- The diagonal cosine-side `L²` integral, using the same squared-norm
constant as the Chebyshev `T` polynomials. -/
lemma integral_chebyshevCosine_mul_self (n : ℕ) :
    ∫ θ in (0)..Real.pi, chebyshevCosine n θ * chebyshevCosine n θ =
      chebyshevTNormSq n := by
  rw [← integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul]
  exact integral_eval_T_real_mul_self_measureT n

/-- Off-diagonal cosine modes are orthogonal over `[0, π]`. -/
lemma integral_chebyshevCosine_mul_chebyshevCosine_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ = 0 := by
  rw [← integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul]
  exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn

/-- Cosine-side Chebyshev orthogonality in the Kronecker-delta form expected by
the later Chebyshev Hilbert-basis construction. -/
lemma integral_chebyshevCosine_mul_chebyshevCosine_eq_ite (m n : ℕ) :
    ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ =
      if m = n then chebyshevTNormSq n else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_chebyshevCosine_mul_self]
  · simp [hmn, integral_chebyshevCosine_mul_chebyshevCosine_of_ne hmn]

/-! ### Normalized cosine modes -/

/-- The normalized angular cosine mode corresponding to the normalized Chebyshev `Tₙ` mode. -/
noncomputable def normalizedChebyshevCosine (n : ℕ) (θ : ℝ) : ℝ :=
  chebyshevCosine n θ / Real.sqrt (chebyshevTNormSq n)

/-- The defining equation for the normalized angular cosine representative. -/
lemma normalizedChebyshevCosine_def (n : ℕ) (θ : ℝ) :
    normalizedChebyshevCosine n θ =
      chebyshevCosine n θ / Real.sqrt (chebyshevTNormSq n) :=
  normalizedChebyshevCosine.eq_1 n θ

@[simp]
lemma normalizedChebyshevCosine_zero (θ : ℝ) :
    normalizedChebyshevCosine 0 θ = 1 / Real.sqrt Real.pi := by
  simp [normalizedChebyshevCosine_def]

lemma normalizedChebyshevCosine_one (θ : ℝ) :
    normalizedChebyshevCosine 1 θ = Real.cos θ / Real.sqrt (Real.pi / 2) := by
  simp [normalizedChebyshevCosine_def]

@[simp]
lemma normalizedChebyshevCosine_of_ne_zero {n : ℕ} (hn : n ≠ 0) (θ : ℝ) :
    normalizedChebyshevCosine n θ = Real.cos (n * θ) / Real.sqrt (Real.pi / 2) := by
  simp [normalizedChebyshevCosine_def, chebyshevCosine_def, chebyshevTNormSq_of_ne_zero hn]

/-- The normalized angular Chebyshev representatives are continuous. -/
lemma continuous_normalizedChebyshevCosine (n : ℕ) :
    Continuous (normalizedChebyshevCosine n) :=
  (continuous_chebyshevCosine n).div_const _

/-- Pulling back a normalized Chebyshev `T` polynomial along `x = cos θ` gives the normalized
angular cosine mode. -/
lemma normalized_eval_T_real_cos_eq_normalizedChebyshevCosine (n : ℕ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) / Real.sqrt (chebyshevTNormSq n) =
      normalizedChebyshevCosine n θ := by
  rw [eval_T_real_cos_eq_chebyshevCosine]
  simp [normalizedChebyshevCosine_def]

/-- Transfer a product of normalized Chebyshev `T` polynomials from `measureT` to the normalized
angular cosine-side integral. -/
lemma integral_normalized_eval_T_real_mul_measureT_eq_integral_normalizedChebyshevCosine_mul
    (m n : ℕ) :
    ∫ x, ((T ℝ m).eval x / Real.sqrt (chebyshevTNormSq m)) *
        ((T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n)) ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ *
        normalizedChebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [normalizedChebyshevCosine_def, chebyshevCosine_def]

/-- The diagonal normalized angular cosine modes have integral one over `[0, π]`. -/
lemma integral_normalizedChebyshevCosine_mul_self (n : ℕ) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine n θ * normalizedChebyshevCosine n θ = 1 := by
  have hfun : (fun θ : ℝ => normalizedChebyshevCosine n θ * normalizedChebyshevCosine n θ) =
      fun θ : ℝ => (Real.sqrt (chebyshevTNormSq n) * Real.sqrt (chebyshevTNormSq n))⁻¹ *
        (chebyshevCosine n θ * chebyshevCosine n θ) := by
    funext θ
    simp only [normalizedChebyshevCosine_def]
    field_simp [(Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos n)]
  rw [hfun, intervalIntegral.integral_const_mul, integral_chebyshevCosine_mul_self]
  have hsqrt : Real.sqrt (chebyshevTNormSq n) * Real.sqrt (chebyshevTNormSq n) =
      chebyshevTNormSq n := by
    rw [← sq, Real.sq_sqrt (chebyshevTNormSq_pos n).le]
  rw [hsqrt]
  field_simp [chebyshevTNormSq_ne_zero n]

/-- Distinct normalized angular cosine modes are orthogonal over `[0, π]`. -/
lemma integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_of_ne {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ = 0 := by
  have hfun : (fun θ : ℝ => normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ) =
      fun θ : ℝ => (Real.sqrt (chebyshevTNormSq m) * Real.sqrt (chebyshevTNormSq n))⁻¹ *
        (chebyshevCosine m θ * chebyshevCosine n θ) := by
    funext θ
    simp only [normalizedChebyshevCosine_def]
    field_simp [(Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos m),
      (Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos n)]
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_chebyshevCosine_mul_chebyshevCosine_of_ne hmn, mul_zero]

/-- Normalized angular Chebyshev-cosine orthogonality in Kronecker-delta form. -/
lemma integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_eq_ite (m n : ℕ) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_normalizedChebyshevCosine_mul_self]
  · simp [hmn, integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_of_ne hmn]

end TauCeti
