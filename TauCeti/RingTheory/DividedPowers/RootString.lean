/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.G2PositiveRoots

/-!
# Normal ordering divided powers along the chain `β`, `α + β`, `2α + β`

Let `x`, `y`, `z`, and `w` belong to an associative algebra over `ℚ`, with

```text
x * y = y * x + z,   x * z = z * x + 2 • w,
```

`w` commuting with `x`, `y` commuting with `z`, and `z` commuting with `w`. This is the situation
of two roots
`α`, `β` for which `α + β` and `2α + β` are roots while `3α + β` and `α + 2β` are not: with `x` and
`y` the root vectors of `α` and `β` in a Chevalley basis, `z` is `N_{α β}` times the root vector of
`α + β`, and the second divided power `(ad x)² y / 2` of the inner derivation is again an *integral*
multiple `w` of the root vector of `2α + β`.

The resulting straightening rule is again coefficient-one,

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c ≤ n, b + 2c ≤ m,  y⁽ⁿ⁻ᵇ⁻ᶜ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁾,
```

so it holds in a Kostant integral form and, after base change, over a ring of any characteristic.
The class-two rule `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq` is the
degenerate case `w = 0`, and covers every pair of non-proportional roots in a simply-laced root
system; the rule proved here covers the additional chains in types `B`, `C`, and `F₄`.

Type `G₂` needs the longer string containing `3α + β`, together with the extra root `3α + 2β`.
That case is `TauCeti.Associative.dividedPower_mul_dividedPower_of_g2PositiveRoots`, and the rule
proved here is derived from it: setting the root vectors of `3α + β` and of `3α + 2β` to zero
turns the `G₂` hypotheses into the ones above and kills every summand whose exponents at those
two roots are not both zero.

## Main results

* `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul`: the
  coefficient-one straightening rule for the chain `β`, `α + β`, `2α + β`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w : A}

/-! ## The straightening rule -/

/-- The pairs of exponents in the straightening rule for the chain
`β`, `α + β`, `2α + β`. -/
def chainLeTwoIndex (m n : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m}

/-- Membership in `chainLeTwoIndex` in terms of its two mathematical inequalities. -/
@[simp]
theorem mem_chainLeTwoIndex {m n : ℕ} {p : ℕ × ℕ} :
    p ∈ chainLeTwoIndex m n ↔ p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m := by
  simp only [chainLeTwoIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- **Coefficient-one normal ordering along the chain `β`, `α + β`, `2α + β`.** Suppose

```text
x * y = y * x + z,   x * z = z * x + 2 • w,
```

that `w` commutes with `x`, `y` commutes with `z`, and `z` commutes with `w`. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c ≤ n, b + 2c ≤ m,  y⁽ⁿ⁻ᵇ⁻ᶜ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁾.
```

Every coefficient in the divided-power basis is `1`, so the identity survives restriction to a
Kostant integral lattice and base change to a ring of arbitrary characteristic. Taking `w = 0`
and discarding the terms with `c ≠ 0` recovers the class-two rule
`dividedPower_mul_dividedPower_of_commutator_eq`. This rule is itself the case `v = s = 0` of
`dividedPower_mul_dividedPower_of_g2PositiveRoots`, which is how it is proved here. -/
theorem dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w)
    (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ chainLeTwoIndex m n,
        dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w *
          dividedPower (m - p.1 - 2 * p.2) x := by
  -- Killing the root vectors of `3α + β` and `3α + 2β` turns the `G₂` normalizations into the
  -- hypotheses above, and every commutation hypothesis of the `G₂` rule involving them holds.
  have hxw0 : x * w = w * x + 3 • (0 : A) := by simp [hxw.eq]
  have hwz0 : w * z = z * w + 3 • (0 : A) := by simp [hzw.symm.eq]
  rw [dividedPower_mul_dividedPower_of_g2PositiveRoots hxy hxz hxw0 hwz0 (Commute.zero_right x)
    (Commute.zero_right x) hyz (Commute.zero_right w) (Commute.zero_right z)
    (Commute.zero_right w) (Commute.zero_right (0 : A)) m n]
  -- Only the summands with no `3α + β` and no `3α + 2β` factor survive, and they are indexed by
  -- `chainLeTwoIndex m n` embedded as the quadruples `(b, c, 0, 0)`.
  set emb : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun p => (p.1, p.2, 0, 0) with hemb
  have hinj : ∀ p ∈ chainLeTwoIndex m n, ∀ q ∈ chainLeTwoIndex m n, emb p = emb q → p = q := by
    rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simpa [hemb, Prod.ext_iff] using h
  have hsub : (chainLeTwoIndex m n).image emb ⊆ g2PositiveRootIndex m n := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [mem_chainLeTwoIndex] at hp
    simp only [hemb, mem_g2PositiveRootIndex]
    omega
  have hzero : ∀ q ∈ g2PositiveRootIndex m n, q ∉ (chainLeTwoIndex m n).image emb →
      dividedPower (n - q.1 - q.2.1 - q.2.2.1 - 2 * q.2.2.2) y * dividedPower q.1 z *
          dividedPower q.2.1 w * dividedPower q.2.2.1 (0 : A) * dividedPower q.2.2.2 (0 : A) *
          dividedPower (m - q.1 - 2 * q.2.1 - 3 * q.2.2.1 - 3 * q.2.2.2) x = 0 := by
    rintro ⟨b, c, d, e⟩ hq hq'
    rw [mem_g2PositiveRootIndex] at hq
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rcases Nat.eq_zero_or_pos e with rfl | he
      · exact absurd (Finset.mem_image.mpr
          ⟨(b, c), mem_chainLeTwoIndex.mpr (by omega), rfl⟩) hq'
      · rw [dividedPower_eval_zero he.ne', mul_zero, zero_mul]
    · rw [dividedPower_eval_zero hd.ne', mul_zero, zero_mul, zero_mul]
  rw [← Finset.sum_subset hsub hzero, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [hemb]

end TauCeti.Associative
