/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Semiconj
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# Commuting binomial coefficients with divided powers

Suppose that `a * x = x * (a + c)` in an associative algebra over `ℚ`, with `c` commuting with
`x`.  This file combines polynomial semiconjugacy with normalized powers to prove

```text
(a choose m) x⁽ⁿ⁾ = x⁽ⁿ⁾ (a + n c choose m),
x⁽ⁿ⁾ (a choose m) = (a - n c choose m) x⁽ⁿ⁾.
```

These identities are the Cartan/root-vector reordering rules used in a PBW basis of the Kostant
integral form.  Their significance is integral: although `x⁽ⁿ⁾` contains the denominator `n!`,
moving it past a Cartan binomial coefficient introduces no new rational coefficient.

## Main results

* `TauCeti.Associative.ringChoose_mul_dividedPower`: move a binomial coefficient to the right.
* `TauCeti.Associative.dividedPower_mul_ringChoose`: move a binomial coefficient to the left.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

universe u

variable {A : Type u} [Ring A] [Algebra ℚ A] [BinomialRing A]

/-- A generalized binomial coefficient can be moved to the right across a divided power by
shifting its argument by `n • c`. -/
theorem ringChoose_mul_dividedPower (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    Ring.choose a m * dividedPower n x =
      dividedPower n x * Ring.choose (a + n • c) m := by
  rw [dividedPower_def, mul_smul_comm, smul_mul_assoc, ringChoose_mul_pow m h hc n]

/-- A generalized binomial coefficient can be moved to the left across a divided power by
shifting its argument by `-n • c`. -/
theorem dividedPower_mul_ringChoose (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    dividedPower n x * Ring.choose a m =
      Ring.choose (a - n • c) m * dividedPower n x := by
  rw [dividedPower_def, smul_mul_assoc, mul_smul_comm, pow_mul_ringChoose m h hc n]

end TauCeti.Associative
