/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Square roots of integers as algebraic integers

An element `x` of a field `K` with `x² = d` for an integer `d` is integral over `ℤ` (its square
is an integer, which is integral); this file packages such an `x` as an element
`NumberField.integralSqrt hx` of the ring of integers `𝓞 K`, together with its two
defining identities: its image in `K` is `x`, and it squares to `d` in `𝓞 K`.

This is the shared square-root packaging used by the multiquadratic Layer 1 files: the
splitting law (`TauCeti.NumberTheory.Multiquadratic.MultiquadraticSplitting`) moves the
generators `√dᵢ` into `𝓞 K` to compare residues, and the Frobenius computation
(`TauCeti.NumberTheory.NumberField.Frobenius`) applies the arithmetic-Frobenius congruence,
which lives on `𝓞 K`, to a square root.

When `d` is not a rational square, `X² - d` is irreducible over `ℚ`, so it is the minimal
polynomial of `x` over `ℚ`; since `ℤ` is integrally closed in `ℚ` and `x` is integral, it is also
the minimal polynomial over `ℤ`. That last identity is the standing hypothesis `hmin` of the
quadratic-field API in `TauCeti.NumberTheory.NumberField.Quadratic` and of the multiquadratic
files built on it, so it is recorded here once.

## Main definitions and results

* `NumberField.integralSqrt`: the packaging in `𝓞 K`, with
  `NumberField.algebraMap_integralSqrt` and `NumberField.integralSqrt_sq`.
* `NumberField.minpoly_integralSqrt`: its minimal polynomial over `ℤ` is `X² - d`,
  provided `d` is not a rational square.
-/

public section

open Polynomial

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] {x : K} {d : ℤ}

/-- A square root `x` of an integer `d`, packaged as an element of the ring of integers: since
`x ^ 2 = d` is the image of an integer, it is integral over `ℤ` (`IsIntegral.of_pow`). -/
noncomputable def integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) : 𝓞 K :=
  ⟨x, IsIntegral.of_pow two_pos (hx ▸ isIntegral_algebraMap)⟩

/-- Under `𝓞 K ↪ K`, `NumberField.integralSqrt hx` maps back to `x`. -/
@[simp] theorem algebraMap_integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) :
    algebraMap (𝓞 K) K (integralSqrt hx) = x :=
  NumberField.RingOfIntegers.map_mk x _

/-- `NumberField.integralSqrt hx` squares to the radicand `d` in `𝓞 K`. -/
@[simp] theorem integralSqrt_sq (hx : x ^ 2 = algebraMap ℤ K d) :
    integralSqrt hx ^ 2 = algebraMap ℤ (𝓞 K) d := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, algebraMap_integralSqrt, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  exact hx

/-- **The minimal polynomial of a square root of a nonsquare integer.** If `x ^ 2 = d` for an
integer `d` that is not a square in `ℚ`, then `X ^ 2 - d` is the minimal polynomial over `ℤ` of
`NumberField.integralSqrt hx`. Over `ℚ` this is Kummer irreducibility
(`X_pow_sub_C_irreducible_of_prime`); the descent to `ℤ` is
`minpoly.isIntegrallyClosed_eq_field_fractions`. -/
theorem minpoly_integralSqrt [NumberField K] (hx : x ^ 2 = algebraMap ℤ K d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) : minpoly ℤ (integralSqrt hx) = X ^ 2 - C d := by
  have hxQ : x ^ 2 = algebraMap ℚ K ((d : ℤ) : ℚ) := by
    rw [hx, IsScalarTower.algebraMap_apply ℤ ℚ K]
    norm_num
  have hirr : Irreducible (X ^ 2 - C ((d : ℤ) : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime (by decide) fun y hy =>
      hnsq ⟨y, by simpa [pow_two] using hy.symm⟩
  have haeval : aeval x (X ^ 2 - C ((d : ℤ) : ℚ)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hxQ, sub_self]
  have hminQ : minpoly ℚ x = X ^ 2 - C ((d : ℤ) : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr haeval
      (monic_X_pow_sub_C ((d : ℤ) : ℚ) (by norm_num))).symm
  have hfrac := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K
    (IsIntegralClosure.isIntegral ℤ K (integralSqrt hx))
  apply Polynomial.map_injective (algebraMap ℤ ℚ) Int.cast_injective
  rw [← hfrac, algebraMap_integralSqrt hx, hminQ]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_intCast]
  norm_num

end NumberField
