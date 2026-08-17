/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# The discriminant of a quadratic field is its fundamental discriminant

For a quadratic number field `K = ℚ(√d)` — presented by an algebraic integer `θ : 𝓞 K` with
`minpoly ℤ θ = X² - d` and `Algebra.adjoin ℚ {θ} = ⊤` — with `d` squarefree, the field
discriminant equals the fundamental discriminant of `d`:

`NumberField.discr K = fundamentalDiscriminant d` (`= d` for `d ≡ 1 mod 4`, else `4d`).

This ties the ring-of-integers discriminant computations
(`NumberField.discr_eq_four_mul_of_mod_four_ne_one` and
`NumberField.discr_eq_of_squarefree_of_mod_four_eq_one`) to the integer-level
`TauCeti.Multiquadratic.fundamentalDiscriminant`.

## Main results

* `TauCeti.Multiquadratic.discr_eq_fundamentalDiscriminant`.
-/

public section

open Polynomial
open scoped NumberField

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The discriminant of a quadratic field `ℚ(√d)` (squarefree `d`) is the fundamental
discriminant of `d`.** -/
theorem discr_eq_fundamentalDiscriminant (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d) :
    NumberField.discr K = fundamentalDiscriminant d := by
  rw [fundamentalDiscriminant_def]
  split_ifs with h
  · exact NumberField.discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf h
  · exact NumberField.discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf h

end TauCeti.Multiquadratic
