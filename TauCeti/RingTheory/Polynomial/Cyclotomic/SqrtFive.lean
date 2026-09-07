/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The fifth cyclotomic polynomial over a field containing `√5`

Over any field `E` of characteristic different from `2` containing a square root `s` of `5`, the
fifth cyclotomic polynomial factors as

`Φ_5 = (X² − αX + 1) (X² − βX + 1)`, with `α = (s − 1)/2` and `β = (−s − 1)/2`,

because `α + β = −1` and `αβ = (1 − s²)/4 = −1`. In particular `Φ_5` is not irreducible over `E`.

The hypothesis `2 ≠ 0` is genuinely needed: over `ZMod 2` one has `1 ^ 2 = 5` while `Φ_5` is
irreducible, since `2` has order `4` modulo `5`.

## Main results

* `Polynomial.cyclotomic_five_eq_mul_of_sq_eq_five`: the explicit factorisation.
* `Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five`: `Φ_5` is reducible over `E`.

## References

Over `K = ℚ(√5)` the fifth cyclotomic polynomial is reducible. This is why irreducibility of
`Φ_q` over a general base needs a hypothesis such as unramifiedness: `5` ramifies in `ℚ(√5)`.

That `ℚ(√5)` is the quadratic subfield of `ℚ(ζ_5)` is Sharifi, *Algebraic Number Theory*,
Lemma 3.2.2.
-/

public section

namespace Polynomial

variable {E : Type*} [Field E] [NeZero (2 : E)]

/-- **`Φ_5` factors over a field containing `√5`.** With `s ^ 2 = 5`, the two factors are
`X² − ((s − 1)/2) X + 1` and `X² − ((−s − 1)/2) X + 1`; their product is `X⁴ + X³ + X² + X + 1`
because the two linear coefficients sum to `1` and multiply to `−1`.

Source: Sharifi, *Algebraic Number Theory*, Lemma 3.2.2 (`ℚ(√5) ⊆ ℚ(µ_5)`), made explicit; the
identity is checked by expanding the product. -/
theorem cyclotomic_five_eq_mul_of_sq_eq_five {s : E} (hs : s ^ 2 = 5) :
    cyclotomic 5 E = (X ^ 2 - C ((s - 1) / 2) * X + 1) * (X ^ 2 - C ((-s - 1) / 2) * X + 1) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 : (2 : E) ≠ 0 := NeZero.ne 2
  have e1 : (s - 1) / 2 + (-s - 1) / 2 = -1 := by field_simp; ring
  have e2 : (s - 1) / 2 * ((-s - 1) / 2) = -1 := by field_simp; linear_combination (-1 : E) * hs
  have key : C ((s - 1) / 2) + C ((-s - 1) / 2) = (-1 : E[X]) := by rw [← C_add, e1, C_neg, C_1]
  have key2 : C ((s - 1) / 2) * C ((-s - 1) / 2) = (-1 : E[X]) := by rw [← C_mul, e2, C_neg, C_1]
  rw [cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
  linear_combination (X ^ 3 + X) * key - X ^ 2 * key2

/-- **`Φ_5` is reducible over a field containing `√5`.** By
`cyclotomic_five_eq_mul_of_sq_eq_five` it splits off two quadratic factors, and a quadratic is
never a unit, so `Φ_5` is not irreducible over `E`.

This bounds no degree by itself: `E` may already contain `ζ_5`, in which case `Φ_5` splits into
linear factors. What the statement gives is reducibility, and hence that `Φ_5` is *not* the
minimal polynomial of a primitive fifth root of unity over `E`. -/
theorem not_irreducible_cyclotomic_five_of_sq_eq_five (h5 : ∃ x : E, x ^ 2 = 5) :
    ¬ Irreducible (cyclotomic 5 E) := by
  obtain ⟨s, hs⟩ := h5
  intro hirr
  have hdeg : ∀ a : E, (X ^ 2 - C a * X + 1 : E[X]).natDegree = 2 := fun a ↦ by
    simpa [sub_eq_add_neg] using
      natDegree_quadratic (a := (1 : E)) (b := -a) (c := 1) one_ne_zero
  rcases hirr.isUnit_or_isUnit (cyclotomic_five_eq_mul_of_sq_eq_five hs) with h | h <;>
    simpa [hdeg] using natDegree_eq_zero_of_isUnit h

end Polynomial

