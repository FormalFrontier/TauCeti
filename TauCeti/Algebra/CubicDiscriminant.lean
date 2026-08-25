/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant

/-!
# Divisors of a monic cubic and of its discriminant

Two divisibility transfers for the monic cubic `f(x) = x³ + a₂x² + a₄x + a₆` over a commutative
ring. A common divisor of `f(x)` and of the quartic `3x⁴ + 4a₂x³ + 6a₄x² + 12a₆x + (4a₂a₆ − a₄²)`
divides `f'(x)²`; and a common divisor of `f(x)` and `f'(x)²` divides `Cubic.discr ⟨1, a₂, a₄, a₆⟩`.

Both are certified by explicit polynomial identities in `x`, so no hypothesis beyond the two
divisibilities is needed — no domain, no ellipticity, nothing about the ring beyond commutativity.

Composing them is the algebraic half of the sharp discriminant bound in Nagell–Lutz: a divisor of
the cubic which also divides that quartic divides the cubic's discriminant.

## Main results

* `TauCeti.Cubic.dvd_derivative_sq`
* `TauCeti.Cubic.dvd_discr`

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
the roadmap at `dev/modular-curves @ 9fec8eba7652`,
`LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean`, where the two identities appear inline
inside the discriminant argument rather than as separate lemmas.
-/

public section

namespace TauCeti.Cubic

variable {R : Type*} [CommRing R] {d a₂ a₄ a₆ x : R}

/-- If `d` divides both the monic cubic `f(x) = x³ + a₂x² + a₄x + a₆` and the quartic
`3x⁴ + 4a₂x³ + 6a₄x² + 12a₆x + (4a₂a₆ − a₄²)`, then it divides `f'(x)²`.

The two are related by `f'(x)² + (that quartic) = (12x + 4a₂) · f(x)`, an identity in `x`. -/
theorem dvd_derivative_sq (hf : d ∣ x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hq : d ∣ 3 * x ^ 4 + 4 * a₂ * x ^ 3 + 6 * a₄ * x ^ 2 + 12 * a₆ * x + (4 * a₂ * a₆ - a₄ ^ 2)) :
    d ∣ (3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 := by
  have hid : (3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 =
      (12 * x + 4 * a₂) * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) -
        (3 * x ^ 4 + 4 * a₂ * x ^ 3 + 6 * a₄ * x ^ 2 + 12 * a₆ * x + (4 * a₂ * a₆ - a₄ ^ 2)) := by
    ring
  exact hid ▸ dvd_sub (Dvd.dvd.mul_left hf _) hq

/-- If `d` divides both the monic cubic `f(x) = x³ + a₂x² + a₄x + a₆` and `f'(x)²`, then it divides
the cubic's discriminant.

`Cubic.discr ⟨1, a₂, a₄, a₆⟩` is an explicit combination of `f(x)` and `f'(x)²`, an identity in
`x`. -/
theorem dvd_discr (hf : d ∣ x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hderiv : d ∣ (3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2) :
    d ∣ (_root_.Cubic.mk 1 a₂ a₄ a₆).discr := by
  have hid : (_root_.Cubic.mk 1 a₂ a₄ a₆).discr =
      (27 * x ^ 3 + 27 * a₂ * x ^ 2 + 27 * a₄ * x - 4 * a₂ ^ 3 + 18 * a₂ * a₄ - 27 * a₆) *
          (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
        - (3 * x ^ 2 + 2 * a₂ * x - a₂ ^ 2 + 4 * a₄) * (3 * x ^ 2 + 2 * a₂ * x + a₄) ^ 2 := by
    simp only [_root_.Cubic.discr]; ring
  exact hid ▸ dvd_sub (Dvd.dvd.mul_left hf _) (Dvd.dvd.mul_left hderiv _)

end TauCeti.Cubic
