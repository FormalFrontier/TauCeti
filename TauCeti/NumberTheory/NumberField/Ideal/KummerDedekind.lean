/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# Counting the primes above a rational prime by Kummer–Dedekind

Mathlib's number-field Kummer–Dedekind theorem
(`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) is a bijection between the primes of
`𝓞 K` above a rational prime `p` and the monic irreducible factors of `minpoly ℤ θ` modulo `p`,
valid whenever `p` does not divide the conductor exponent of the algebraic integer `θ`. This file
records its cardinality form: the number of primes above `p` is the number of those factors. This is
the shape in which splitting laws are read off a generator, for instance the quadratic laws of
`TauCeti.NumberTheory.NumberField.Quadratic.Splitting`.

## Main result

* `NumberField.ncard_primesOver_eq_card_monicFactorsMod`: the number of primes of `𝓞 K` above `p`
  equals the number of monic irreducible factors of `minpoly ℤ θ` mod `p`, for `p ∤ exponent θ`.
-/

public section

open Ideal RingOfIntegers
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The Kummer–Dedekind count.** When `p` does not divide the conductor exponent of `θ`, the
primes of `𝓞 K` above `p` are counted by the monic irreducible factors of `minpoly ℤ θ` mod `p`. -/
theorem ncard_primesOver_eq_card_monicFactorsMod (θ : 𝓞 K) {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ exponent θ) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = (monicFactorsMod θ p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp)]
  exact Nat.card_eq_finsetCard _

end NumberField
