/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Basics for quadratic number fields

Shared facts about a quadratic number field `K` presented by an algebraic integer `θ : 𝓞 K` whose
minimal polynomial over `ℤ` is `X² - d`. These feed both the prime-splitting law
(`Quadratic/Splitting.lean`) and the conjugation automorphism (`Quadratic/Conjugation/Basic.lean`).

## Main results

* `TauCeti.NumberField.minpoly_rat_quadratic`: the minimal polynomial of `θ` over `ℚ` is `X² - d`.
* `TauCeti.NumberField.finrank_rat_eq_two`: `K` has degree `2` over `ℚ`.
* `TauCeti.NumberField.coe_gen_sq`: the generator squares to the radicand, `θ² = d` in `K`.
-/

public section

open Polynomial NumberField Module

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

end TauCeti.NumberField
