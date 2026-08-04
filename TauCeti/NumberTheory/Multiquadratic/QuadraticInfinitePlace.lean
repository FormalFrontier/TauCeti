/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The infinite place of a quadratic field `ℚ(√d)`

For a quadratic number field `K = ℚ(√d)` (given by `θ : 𝓞 K` with `minpoly ℤ θ = X² - d` and
`Algebra.adjoin ℚ {θ} = ⊤`) with `d < 0`, the field is totally complex: every real embedding
would send `θ` to a real square root of `d < 0`, which is impossible. Equivalently, the
archimedean place of `ℚ` is ramified in `ℚ(√d)` exactly for imaginary `d` — the archimedean half
of the ramification data the genus-field identification needs.

## Main results

* `TauCeti.NumberField.isTotallyComplex_of_neg`.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {θ : 𝓞 K} {d : ℤ}

/-- **An imaginary quadratic field is totally complex.** For `d < 0`, `K = ℚ(√d)` has no real
infinite place. -/
theorem isTotallyComplex_of_neg (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : d < 0) :
    IsTotallyComplex K := by
  -- A real embedding would carry `θ` to a real square root of `d < 0`, which is impossible.
  rw [isTotallyComplex_iff]
  intro w
  rw [isComplex_iff]
  intro hφ
  have hφsq : (embedding w) (θ : K) ^ 2 = (d : ℂ) := by
    rw [← map_pow, coe_gen_sq hmin]; simp [map_intCast]
  have hψsq : (hφ.embedding (θ : K)) ^ 2 = (d : ℝ) := by
    have h : (((hφ.embedding (θ : K)) ^ 2 : ℝ) : ℂ) = (d : ℂ) := by
      push_cast [hφ.coe_embedding_apply]; rw [hφsq]
    exact_mod_cast h
  nlinarith [sq_nonneg (hφ.embedding (θ : K)), hψsq, show (d : ℝ) < 0 from by exact_mod_cast hd]

end TauCeti.NumberField
