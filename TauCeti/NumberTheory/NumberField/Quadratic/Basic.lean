/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.FieldTheory.Trace
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

/-!
# Basics for quadratic number fields

Shared facts about a quadratic number field `K` presented by an algebraic integer `θ : 𝓞 K` whose
minimal polynomial over `ℤ` is `X² - d`. These feed the prime-splitting law
(`Quadratic/Splitting.lean`), the conjugation automorphism (`Quadratic/Conjugation/Basic.lean`), the
ring-of-integers/discriminant computation (`Quadratic/RingOfIntegers.lean`), and the field-norm
computation (`Quadratic/Norm.lean`).

## Main results

* `NumberField.minpoly_rat_quadratic`: the minimal polynomial of `θ` over `ℚ` is `X² - d`.
* `NumberField.finrank_rat_eq_two`: `K` has degree `2` over `ℚ`.
* `NumberField.gen_sq`: the integral generator squares to the radicand in `𝓞 K`.
* `NumberField.coe_gen_sq`: the generator squares to the radicand, `θ² = d` in `K`.
* `NumberField.coe_gen_sq_ratCast`: the same over `ℚ`, `θ² = (d : ℚ)` in `K`.
* `NumberField.gen_notMem_range`: the generator is not rational, `θ ∉ ℚ`.
* `NumberField.coe_gen_ne_zero`: the generator is nonzero.
* `NumberField.exists_eq_add_mul_gen`: every element of `K` is `b + aθ`.
* `NumberField.not_isSquare_radicand`: the radicand is not a rational square.
* `NumberField.trace_gen_eq_zero`: the trace of the generator is `0`.
* `NumberField.discr_one_gen`: the discriminant of `{1, θ}` over `ℚ` is `4d`.
* `NumberField.discr_one_halfGen`: the discriminant of `{1, (1+θ)/2}` over `ℚ` is `d`.

The trace and discriminant computations reuse the generic quadratic-extension API
`NumberField.trace_eq_zero_of_sq_ratCast` and
`TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap` from `TauCeti.FieldTheory.Trace`.
-/

public section

open Polynomial NumberField Module
open scoped Matrix

namespace NumberField

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
/-- The integral generator squares to the radicand: `θ² = d` in `𝓞 K`. -/
@[simp] theorem gen_sq (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    θ ^ 2 = algebraMap ℤ (𝓞 K) d := by
  have hae := minpoly.aeval ℤ θ
  rw [hmin] at hae
  have h2 : θ ^ 2 - algebraMap ℤ (𝓞 K) d = 0 := by
    simpa [map_sub, map_pow, aeval_X, aeval_C] using hae
  linear_combination h2

omit [NumberField K] in
/-- The generator squares to the radicand in `K`: `θ² = d`. -/
@[simp] theorem coe_gen_sq (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = algebraMap ℤ K d := by
  have := congrArg (algebraMap (𝓞 K) K) (gen_sq hmin)
  rwa [map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K] at this

omit [NumberField K] in
/-- The generator squares to the radicand viewed over `ℚ`: `θ² = (d : ℚ)` in `K`. This is
`coe_gen_sq` transported along `ℤ → ℚ → K`, the form fed to the generic square-root-basis API. -/
theorem coe_gen_sq_ratCast [CharZero K] (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
  rw [coe_gen_sq hmin, IsScalarTower.algebraMap_apply ℤ ℚ K]; norm_num

/-- The generator is irrational: `θ ∉ ℚ`. -/
theorem gen_notMem_range (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ∉ (algebraMap ℚ K).range := by
  -- Were `θ = q ∈ ℚ`, its `ℚ`-minimal polynomial would divide `X - q`, so have degree `≤ 1`,
  -- contradicting `minpoly ℚ θ = X² - d`.
  rintro ⟨q, hq⟩
  have hdvd : minpoly ℚ (algebraMap ℚ K q) ∣ (X - C q) := minpoly.dvd ℚ _ (by simp)
  have h1 : (minpoly ℚ (algebraMap ℚ K q)).natDegree ≤ 1 := by
    simpa [natDegree_X_sub_C] using Polynomial.natDegree_le_of_dvd hdvd (X_sub_C_ne_zero q)
  rw [hq, minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C] at h1
  norm_num at h1

/-- The generator of a quadratic presentation is **nonzero**: it is irrational
(`gen_notMem_range`), whereas `0` is rational. -/
theorem coe_gen_ne_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) : (θ : K) ≠ 0 := fun h0 =>
  gen_notMem_range hmin ⟨0, by rw [map_zero, h0]⟩

/-- **Every element of a quadratic field is `b + aθ`** for rationals `a, b`. -/
theorem exists_eq_add_mul_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : K) :
    ∃ a b : ℚ, x = algebraMap ℚ K b + algebraMap ℚ K a * (θ : K) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  exact Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul ℚ K
    (gen_notMem_range hmin) x

/-- **The radicand of a quadratic presentation is not a rational square.** Were `d = q²`, the
factorization `(θ - q)(θ + q) = θ² - d = 0` would force `θ = ±q ∈ ℚ`. -/
theorem not_isSquare_radicand (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    ¬ IsSquare (((d : ℤ) : ℚ)) := by
  rintro ⟨q, hq⟩
  have hθ : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  have hq' : algebraMap ℚ K ((d : ℤ) : ℚ) = algebraMap ℚ K q * algebraMap ℚ K q := by
    rw [← map_mul, ← hq]
  have hfac : ((θ : K) - algebraMap ℚ K q) * ((θ : K) + algebraMap ℚ K q) = 0 := by
    linear_combination hθ + hq'
  rcases mul_eq_zero.mp hfac with h | h
  · exact gen_notMem_range hmin ⟨q, by linear_combination -h⟩
  · exact gen_notMem_range hmin ⟨-q, by rw [map_neg]; linear_combination -h⟩

/-- The trace of the generator vanishes: `Tr(θ) = 0`. -/
theorem trace_gen_eq_zero (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    Algebra.trace ℚ K (θ : K) = 0 := by
  -- Specialise the generic `trace_eq_zero_of_sq_ratCast` to `θ² = d` and the irrationality of `θ`.
  have hd' : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  exact trace_eq_zero_of_sq_ratCast hd' (gen_notMem_range hmin)

/-- The discriminant of the `ℚ`-family `{1, θ}` is `4d`. -/
theorem discr_one_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (θ : K)] = ((4 * d : ℤ) : ℚ) := by
  -- Specialise the generic square-root-basis discriminant `discr_one_elem_eq_of_sq_algebraMap`.
  have hd' : (θ : K) ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := coe_gen_sq_ratCast hmin
  rw [TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap (finrank_rat_eq_two hmin hgen) hd'
    (gen_notMem_range hmin)]
  push_cast; ring

/-- The discriminant of the `ℚ`-family `{1, (1+θ)/2}` is `d`. -/
theorem discr_one_halfGen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.discr ℚ ![(1 : K), (1 + (θ : K)) / 2] = ((d : ℤ) : ℚ) := by
  -- Change of basis from `{1, θ}` by `!![1, 0; 1/2, 1/2]` (determinant `1/2`): `(1/2)² · 4d = d`.
  have hP : ![(1 : K), (1 + (θ : K)) / 2]
      = (!![1, 0; 1 / 2, 1 / 2] : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ K) *ᵥ
          ![(1 : K), (θ : K)] := by
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [hP, Algebra.discr_of_matrix_mulVec, discr_one_gen hmin hgen, Matrix.det_fin_two_of]
  push_cast; ring

end NumberField
