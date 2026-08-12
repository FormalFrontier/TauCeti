/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.DividedPowers.RatAlgebra
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-!
# Divided powers in associative algebras

For an element `x` of an associative algebra over `ℚ`, its `n`-th divided power is

```text
x⁽ⁿ⁾ = xⁿ / n!.
```

Unlike Mathlib's `DividedPowers.RatAlgebra.dpow`, this definition does not require the ambient
algebra to be commutative. This is the form used by the Kostant integral form of a universal
enveloping algebra. The multiplication and commuting-sum formulas below show why these rational
elements can generate an integral algebra and a coalgebra: their structure constants are integers.

This is a prerequisite for the explicit Chevalley--Demazure construction in Layer 9 of the
ReductiveGroups roadmap. That construction starts from divided powers of Chevalley root vectors in
the generally noncommutative universal enveloping algebra. No integral-form or group-scheme
definition is made here.

## Main definitions and results

* `TauCeti.Associative.dividedPower`: the normalized power `x ^ n / n!`.
* `TauCeti.Associative.mul_dividedPower`: products of divided powers of one element have a
  binomial coefficient as structure constant.
* `TauCeti.Associative.dividedPower_add`: divided powers turn a sum of commuting elements into an
  antidiagonal sum.
* `TauCeti.Associative.dividedPower_sub`: the corresponding signed expansion for a difference.
* `TauCeti.Associative.map_dividedPower`: divided powers are natural under algebra homomorphisms.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

section Semiring

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The `n`-th divided power `xⁿ / n!` of an element of an associative `ℚ`-algebra.

The scalar is placed through the `ℚ`-algebra structure, so this definition applies to
noncommutative algebras such as universal enveloping algebras. -/
@[expose] noncomputable def dividedPower (n : ℕ) (x : A) : A :=
  (n.factorial : ℚ)⁻¹ • x ^ n

/-- The defining equation of `dividedPower`, for consumers that need to normalize it. -/
theorem dividedPower_def (n : ℕ) (x : A) :
    dividedPower n x = (n.factorial : ℚ)⁻¹ • x ^ n := rfl

@[simp]
theorem dividedPower_zero (x : A) : dividedPower 0 x = 1 := by
  simp [dividedPower_def]

@[simp]
theorem dividedPower_one (x : A) : dividedPower 1 x = x := by
  simp [dividedPower_def]

@[simp]
theorem dividedPower_eval_zero {n : ℕ} (hn : n ≠ 0) : dividedPower n (0 : A) = 0 := by
  simp [dividedPower_def, hn]

/-- Multiplying a divided power by its factorial recovers the ordinary power. -/
theorem factorial_smul_dividedPower (n : ℕ) (x : A) :
    (n.factorial : ℚ) • dividedPower n x = x ^ n := by
  rw [dividedPower_def, ← mul_smul]
  rw [Rat.mul_inv_cancel]
  · exact one_smul ℚ (x ^ n)
  · exact_mod_cast n.factorial_ne_zero

/-- Divided powers are preserved by homomorphisms of associative `ℚ`-algebras. -/
@[simp]
theorem map_dividedPower {B : Type*} [Semiring B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (n : ℕ) (x : A) :
    f (dividedPower n x) = dividedPower n (f x) := by
  simp [dividedPower_def]

/-- Scaling an element scales its `n`-th divided power by the `n`-th power of the scalar. -/
@[simp]
theorem dividedPower_smul (q : ℚ) (n : ℕ) (x : A) :
    dividedPower n (q • x) = q ^ n • dividedPower n x := by
  simp only [dividedPower_def, smul_pow]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- Divided powers preserve commutation of their underlying elements. -/
theorem commute_dividedPower {x y : A} (hxy : Commute x y) (m n : ℕ) :
    Commute (dividedPower m x) (dividedPower n y) := by
  simpa only [dividedPower_def] using
    ((hxy.pow_pow m n).smul_left (m.factorial : ℚ)⁻¹).smul_right (n.factorial : ℚ)⁻¹

/-- The rational coefficient identity behind multiplication of divided powers. -/
private theorem inv_factorial_mul_inv_factorial (m n : ℕ) :
    (m.factorial : ℚ)⁻¹ * (n.factorial : ℚ)⁻¹ =
      (Nat.choose (m + n) m : ℚ) * ((m + n).factorial : ℚ)⁻¹ := by
  rw [Nat.cast_add_choose ℚ]
  field_simp

/-- Products of divided powers of the same element have integral structure constants:
`x⁽ᵐ⁾ x⁽ⁿ⁾ = choose (m + n) m • x⁽ᵐ⁺ⁿ⁾`. -/
theorem mul_dividedPower (m n : ℕ) (x : A) :
    dividedPower m x * dividedPower n x =
      Nat.choose (m + n) m • dividedPower (m + n) x := by
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  simp only [dividedPower_def, smul_mul_smul, ← pow_add, smul_smul]
  rw [inv_factorial_mul_inv_factorial]

/-- The first-order recurrence for divided powers. -/
theorem succ_smul_dividedPower (n : ℕ) (x : A) :
    (n + 1) • dividedPower (n + 1) x = dividedPower n x * x := by
  simpa using (mul_dividedPower n 1 x).symm

/-- The left-handed first-order recurrence for divided powers. -/
theorem mul_dividedPower_eq_succ_smul (n : ℕ) (x : A) :
    x * dividedPower n x = (n + 1) • dividedPower (n + 1) x := by
  rw [succ_smul_dividedPower]
  rw [dividedPower_def, mul_smul_comm, Algebra.smul_mul_assoc]
  congr 1
  exact ((Commute.refl x).pow_right n).eq

/-- The rational coefficient identity that cancels the binomial coefficient in the divided-power
expansion of a commuting sum. -/
private theorem inv_factorial_mul_choose (n i j : ℕ) (hij : i + j = n) :
    (n.factorial : ℚ)⁻¹ * Nat.choose n i =
      (i.factorial : ℚ)⁻¹ * (j.factorial : ℚ)⁻¹ := by
  subst n
  rw [Nat.cast_add_choose ℚ]
  field_simp

/-- The divided-power binomial formula for commuting elements of an associative algebra:
`(x + y)⁽ⁿ⁾ = ∑ i+j=n x⁽ⁱ⁾ y⁽ʲ⁾`.

This is the coalgebra formula used for primitive elements: after applying a comultiplication with
`Δ(x) = x ⊗ 1 + 1 ⊗ x`, the two summands commute. -/
theorem dividedPower_add {x y : A} (hxy : Commute x y) (n : ℕ) :
    dividedPower n (x + y) =
      ∑ ij ∈ antidiagonal n, dividedPower ij.1 x * dividedPower ij.2 y := by
  rw [dividedPower_def, hxy.add_pow']
  simp only [smul_sum]
  apply sum_congr rfl
  intro ij hij
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, dividedPower_def, dividedPower_def,
    smul_mul_smul]
  rw [inv_factorial_mul_choose n ij.1 ij.2 (mem_antidiagonal.mp hij)]

end Semiring

section Ring

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Divided powers of a negated element acquire the expected sign. -/
@[simp]
theorem dividedPower_neg (n : ℕ) (x : A) :
    dividedPower n (-x) = (-1 : ℚ) ^ n • dividedPower n x := by
  simpa only [neg_one_smul] using dividedPower_smul (-1) n x

/-- The signed divided-power binomial formula for commuting elements of an associative algebra. -/
theorem dividedPower_sub {x y : A} (hxy : Commute x y) (n : ℕ) :
    dividedPower n (x - y) =
      ∑ ij ∈ antidiagonal n,
        (-1 : ℚ) ^ ij.2 • (dividedPower ij.1 x * dividedPower ij.2 y) := by
  rw [sub_eq_add_neg, dividedPower_add (hxy.neg_right) n]
  apply sum_congr rfl
  intro ij _
  rw [dividedPower_neg, mul_smul_comm]

end Ring

/-- In a commutative `ℚ`-algebra, `dividedPower` agrees with every Mathlib divided-power
structure on the unit ideal. -/
theorem dividedPower_eq_dpow {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (hR : DividedPowers (⊤ : Ideal R)) (n : ℕ) (x : R) :
    dividedPower n x = hR.dpow n x := by
  rw [dividedPower_def, ← Ring.inverse_eq_inv']
  exact (DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul (⊤ : Ideal R) hR
    Submodule.mem_top).symm

end TauCeti.Associative
