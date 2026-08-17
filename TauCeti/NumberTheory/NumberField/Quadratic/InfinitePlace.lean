/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace

/-!
# The infinite place of a quadratic field `ℚ(√d)`

For `d < 0`, the imaginary quadratic field `ℚ(√d)` is totally complex: a special case of
`TauCeti.NumberField.isTotallyComplex_of_sq_ratCast_of_neg` via the generator `θ` with `θ² = d`.

## Main results

* `TauCeti.NumberField.isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg`.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **An imaginary quadratic field is totally complex.** Any number field `K` containing an
algebraic integer `θ` with `minpoly ℤ θ = X² - d` and `d < 0` is totally complex — in particular the
imaginary quadratic field `ℚ(√d)`. -/
theorem isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hd : d < 0) : IsTotallyComplex K :=
  isTotallyComplex_of_sq_ratCast_of_neg (x := (θ : K)) (r := (d : ℚ))
    (coe_gen_sq_ratCast hmin) (by exact_mod_cast hd)

end TauCeti.NumberField
