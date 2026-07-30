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
(`Quadratic/Splitting.lean`) and the conjugation automorphism (`Quadratic/Conjugation.lean`).

## Main results

* `TauCeti.NumberField.minpoly_rat_quadratic`: the minimal polynomial of `θ` over `ℚ` is `X² - d`.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The minimal polynomial of `θ` over `ℚ` is `X² - d`, obtained from its minimal polynomial over
`ℤ` by base change along `ℤ → ℚ`. -/
theorem minpoly_rat_quadratic {θ : 𝓞 K} {d : ℤ} (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    minpoly ℚ (θ : K) = X ^ 2 - C ((d : ℤ) : ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K (IsIntegralClosure.isIntegral ℤ K θ), hmin]
  simp [Polynomial.map_sub, Polynomial.map_pow]

end TauCeti.NumberField
