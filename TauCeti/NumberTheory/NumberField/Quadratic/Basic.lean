/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Basics for quadratic number fields

Shared facts about a quadratic number field `K` presented by an algebraic integer `θ : 𝓞 K` whose
minimal polynomial over `ℤ` is `X² - d`. These feed both the prime-splitting law
(`Quadratic/Splitting.lean`) and the conjugation automorphism (`Quadratic/Conjugation/Basic.lean`).

## Main results

* `TauCeti.NumberField.minpoly_rat_quadratic`: the minimal polynomial of `θ` over `ℚ` is `X² - d`.
* `TauCeti.NumberField.finrank_rat_eq_two`: `K` has degree `2` over `ℚ`.
* `TauCeti.NumberField.coe_gen_sq`: the generator squares to the radicand, `θ² = d` in `K`.
* `TauCeti.NumberField.trace_coe_eq_zero`: the trace of the generator is `0`.
* `TauCeti.NumberField.discr_one_gen`: the discriminant of `{1, θ}` over `ℚ` is `4d`.
-/

public section

open Polynomial NumberField Module
open scoped Matrix

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The minimal polynomial of `θ` over `ℚ` is `X² - d`, obtained from its minimal polynomial over
`ℤ` by base change along `ℤ → ℚ`. -/
theorem minpoly_rat_quadratic (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    minpoly ℚ (θ : K) = X ^ 2 - C ((d : ℤ) : ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K (IsIntegralClosure.isIntegral ℤ K θ), hmin]
  simp [Polynomial.map_sub, Polynomial.map_pow]

/-- The quadratic field `K = ℚ(θ)` has degree `2` over `ℚ`: its power basis has dimension
`natDegree (X² - d) = 2`. -/
theorem finrank_rat_eq_two (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : finrank ℚ K = 2 := by
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  rw [(PowerBasis.ofAdjoinEqTop' hint hgen).finrank,
    ← (PowerBasis.ofAdjoinEqTop' hint hgen).natDegree_minpoly, PowerBasis.ofAdjoinEqTop'_gen,
    minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C]

omit [NumberField K] in
/-- The generator squares to the radicand in `K`: `θ² = d`. -/
theorem coe_gen_sq (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = algebraMap ℤ K d := by
  have h : θ ^ 2 = algebraMap ℤ (𝓞 K) d := by
    have hae := minpoly.aeval ℤ θ
    rw [hmin] at hae
    have h2 : θ ^ 2 - algebraMap ℤ (𝓞 K) d = 0 := by
      simpa [map_sub, map_pow, aeval_X, aeval_C] using hae
    linear_combination h2
  have := congrArg (algebraMap (𝓞 K) K) h
  rwa [map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K] at this

/-- The trace of the generator vanishes: `Tr(θ) = 0` (the `X`-coefficient of `X² - d` is `0`). -/
theorem trace_coe_eq_zero (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Algebra.trace ℚ K (θ : K) = 0 := by
  have hint : IsIntegral ℚ (θ : K) := θ.isIntegral_coe.tower_top
  have hpbmin : minpoly ℚ (PowerBasis.ofAdjoinEqTop' hint hgen).gen = X ^ 2 - C ((d : ℤ) : ℚ) := by
    rw [PowerBasis.ofAdjoinEqTop'_gen]; exact minpoly_rat_quadratic hmin
  have hnc : ((X : ℚ[X]) ^ 2 - C ((d : ℤ) : ℚ)).nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by rw [natDegree_X_pow_sub_C]; norm_num),
      natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]
    norm_num
  rw [← PowerBasis.ofAdjoinEqTop'_gen hint hgen, PowerBasis.trace_gen_eq_nextCoeff_minpoly,
    hpbmin, hnc, neg_zero]

/-- The discriminant of the `ℚ`-family `{1, θ}` is `4d`, from the `2×2` trace form
(`Tr 1 = 2`, `Tr θ = 0`, `Tr θ² = 2d`). -/
theorem discr_one_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (θ : K)] = ((4 * d : ℤ) : ℚ) := by
  have hfr := finrank_rat_eq_two hmin hgen
  have hd' : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
    rw [coe_gen_sq hmin, IsScalarTower.algebraMap_apply ℤ ℚ K]; norm_num
  have htr1 : Algebra.trace ℚ K (1 : K) = 2 := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, hfr]; simp
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, one_mul]
  rw [← pow_two, hd', htr1, trace_coe_eq_zero hmin hgen, Algebra.trace_algebraMap, hfr]
  simp only [nsmul_eq_mul]; push_cast; ring

/-- The discriminant of the `ℚ`-family `{1, (1+θ)/2}` is `d`: a change of basis from `{1, θ}` by
the matrix `!![1, 0; 1/2, 1/2]` (determinant `1/2`), so `disc = (1/2)² · 4d = d`. -/
theorem discr_one_half_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (1 + (θ : K)) / 2] = ((d : ℤ) : ℚ) := by
  have hP : ![(1 : K), (1 + (θ : K)) / 2]
      = (!![1, 0; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ K) *ᵥ
          ![(1 : K), (θ : K)] := by
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [hP, Algebra.discr_of_matrix_mulVec, discr_one_gen hmin hgen, Matrix.det_fin_two_of]
  push_cast; ring

end TauCeti.NumberField
