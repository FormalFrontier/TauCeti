/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Module.Rat
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# Primitive elements in a bialgebra

This file records integral-coefficient formulas for the comultiplication of powers, divided
powers, and binomial coefficients of a primitive element. The two tensor factors commute even
when the bialgebra itself is noncommutative. It also computes the counit of the latter two
families when the underlying element has counit zero.

## Main results

* `TauCeti.Bialgebra.comul_pow_of_primitive`: the comultiplication of a power of a primitive
  element is its binomial expansion.
* `TauCeti.Bialgebra.comul_dividedPower_of_primitive`: the comultiplication of a divided power
  has coefficient one on every antidiagonal term.
* `TauCeti.Bialgebra.comul_choose_of_primitive`: the comultiplication of a binomial coefficient
  has the same coefficient-one formula.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra

universe u w

attribute [local instance] TauCeti.moduleNNRat

/-- The comultiplication of a power of a primitive element is its binomial expansion. -/
theorem comul_pow_of_primitive
    {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Bialgebra R A]
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a) (n : ℕ) :
    (Coalgebra.comul (R := R)) (a ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((a ^ mn.1) ⊗ₜ[R] (a ^ mn.2)) := by
  rw [Bialgebra.comul_pow, h]
  have hcomm : Commute (a ⊗ₜ[R] 1) (1 ⊗ₜ[R] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [hcomm.add_pow']
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

section DividedPower

variable {A : Type w} [Semiring A] [Bialgebra ℚ A]

/-- The comultiplication of a divided power of a primitive element has integral structure
constants:
`Δ(a⁽ⁿ⁾) = ∑ i+j=n, a⁽ⁱ⁾ ⊗ a⁽ʲ⁾`.

This is the formula used for the divided-power generators of a Kostant integral form. -/
theorem comul_dividedPower_of_primitive
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] a) (n : ℕ) :
    (Coalgebra.comul (R := ℚ)) (Associative.dividedPower n a) =
      ∑ ij ∈ Finset.antidiagonal n,
        Associative.dividedPower ij.1 a ⊗ₜ[ℚ] Associative.dividedPower ij.2 a := by
  rw [← Bialgebra.comulAlgHom_apply, Associative.map_dividedPower,
    Bialgebra.comulAlgHom_apply, h]
  have hcomm : Commute (a ⊗ₜ[ℚ] 1) (1 ⊗ₜ[ℚ] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [Associative.dividedPower_add hcomm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← Algebra.TensorProduct.includeLeft_apply (S := ℚ) a,
    ← Algebra.TensorProduct.includeRight_apply (R := ℚ) (A := A) a]
  rw [← Associative.map_dividedPower
      (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] A),
    ← Associative.map_dividedPower
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] A ⊗[ℚ] A)]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- A counit that kills an element also kills all its positive divided powers. -/
theorem counit_dividedPower_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Associative.dividedPower (n + 1) a) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Associative.map_dividedPower,
    Bialgebra.counitAlgHom_apply, h]
  exact Associative.dividedPower_eval_zero (Nat.succ_ne_zero n)

end DividedPower

section Choose

variable {A : Type w} [Ring A] [Bialgebra ℚ A]

/-- The comultiplication of a binomial coefficient in a primitive element has integral
structure constants:
`Δ((a choose n)) = ∑ i+j=n, (a choose i) ⊗ (a choose j)`.

This is the formula used for the Cartan generators of a Kostant integral form. -/
theorem comul_choose_of_primitive
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] a) (n : ℕ) :
    (Coalgebra.comul (R := ℚ)) (Ring.choose a n) =
      ∑ ij ∈ Finset.antidiagonal n,
        Ring.choose a ij.1 ⊗ₜ[ℚ] Ring.choose a ij.2 := by
  rw [← Bialgebra.comulAlgHom_apply, Ring.map_choose, Bialgebra.comulAlgHom_apply, h]
  have hcomm : Commute (a ⊗ₜ[ℚ] 1) (1 ⊗ₜ[ℚ] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [Ring.add_choose_eq n hcomm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← Algebra.TensorProduct.includeLeft_apply (S := ℚ) a,
    ← Algebra.TensorProduct.includeRight_apply (R := ℚ) (A := A) a]
  rw [← Ring.map_choose
      (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] A),
    ← Ring.map_choose
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] A ⊗[ℚ] A)]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- A counit that kills an element also kills all its positive binomial coefficients. -/
theorem counit_choose_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Ring.choose a (n + 1)) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Ring.map_choose, Bialgebra.counitAlgHom_apply, h]
  exact Ring.choose_zero_succ ℚ n

end Choose

end TauCeti.Bialgebra
