/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight

/-!
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction` and defines its pointwise twist by a
completely multiplicative ideal weight.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.MultiplicativeIdealWeight.vonMangoldtTransform` is the weighted function
  `A ↦ χ(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.MultiplicativeIdealWeight.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the weighted transform as the good prime powers for the weight.

The definition chooses a prime base from a proof that `A` is a prime power.  The prime base is
unique for ideals: if positive powers of two prime ideals agree, each prime divides the other, and
associated ideals are equal.  The public evaluation theorem therefore removes the choice from
every computation.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The logarithmic-derivative identity named in
that target additionally requires the Euler-product package of Layer 3; this file supplies its
coefficient and exact prime-power support in advance.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open NumberField IsDedekindDomain
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

/-- Two prime ideals with equal positive powers are equal. -/
private theorem prime_eq_of_pow_eq_pow {P Q : Ideal (𝓞 K)} (hP : Prime P) (hQ : Prime Q)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hpow : P ^ m = Q ^ n) : P = Q := by
  apply dvd_antisymm
  · exact hP.dvd_of_dvd_pow (by rw [← hpow]; exact dvd_pow_self P hm.ne')
  · exact hQ.dvd_of_dvd_pow (by rw [hpow]; exact dvd_pow_self Q hn.ne')

/-- The **ideal von Mangoldt function**.  It takes the value `log N(P)` on every positive power of
a prime ideal `P`, and vanishes on ideals which are not prime powers.

The codomain is `ℂ`, matching `IdealArithmeticFunction`, although every value is real. -/
noncomputable def vonMangoldt : IdealArithmeticFunction K := fun A ↦ by
  classical
  exact if h : IsPrimePow (A : Ideal (𝓞 K)) then
      (Real.log (Ideal.absNorm h.choose) : ℂ)
    else 0

/-- The ideal von Mangoldt function vanishes at the unit ideal. -/
@[simp]
theorem vonMangoldt_one : (vonMangoldt : IdealArithmeticFunction K) 1 = 0 := by
  rw [vonMangoldt, dite_eq_right]
  exact isUnit_one.not_isPrimePow

/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem vonMangoldt_apply_of_eq_prime_pow {A : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hP : Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm P) := by
  let hA : IsPrimePow (A : Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  simp only [vonMangoldt, hA, dite_true]
  have hchosen : hA.choose = P := by
    apply prime_eq_of_pow_eq_pow hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 hn
    exact hA.choose_spec.choose_spec.2.2.trans hpow.symm
  rw [hchosen]

/-- The ideal von Mangoldt function at a positive power of a prime nonzero ideal. -/
theorem vonMangoldt_apply_prime_pow {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    (vonMangoldt : IdealArithmeticFunction K) (P ^ n) =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  apply vonMangoldt_apply_of_eq_prime_pow hP hn
  simp

/-- The ideal von Mangoldt function at a prime ideal. -/
theorem vonMangoldt_apply_prime {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) P =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  simpa using vonMangoldt_apply_prime_pow hP (n := 1) zero_lt_one

/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem vonMangoldt_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 := by
  simp [vonMangoldt, hA]

/-- The norm of a prime ideal is strictly greater than one. -/
private theorem one_lt_absNorm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hpos : 0 < Ideal.absNorm P :=
    Ideal.absNorm_pos_of_nonZeroDivisors ⟨P, mem_nonZeroDivisors_of_ne_zero hP0⟩
  have hne : Ideal.absNorm P ≠ 1 := by
    intro h
    exact hP.not_isUnit (_root_.Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

/-- The support of the ideal von Mangoldt function is exactly the set of prime-power ideals. -/
theorem vonMangoldt_ne_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A ≠ 0 ↔ IsPrimePow (A : Ideal (𝓞 K)) := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (vonMangoldt_of_not_isPrimePow hnot)
  · rintro ⟨P, n, hP, hn, hpow⟩
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow]
    apply Complex.ofReal_ne_zero.mpr
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (Nat.zero_lt_one.trans (one_lt_absNorm_of_prime hP))
    · exact_mod_cast (one_lt_absNorm_of_prime hP).ne'

/-- The ideal von Mangoldt function vanishes exactly away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 ↔ ¬ IsPrimePow (A : Ideal (𝓞 K)) :=
  by simpa only [not_ne_iff] using not_congr (vonMangoldt_ne_zero_iff (K := K) (A := A))

/-- Every value of the ideal von Mangoldt function is real. -/
theorem vonMangoldt_im {A : (Ideal (𝓞 K))⁰} :
    ((vonMangoldt : IdealArithmeticFunction K) A).im = 0 := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow, Complex.ofReal_im]
  · rw [vonMangoldt_of_not_isPrimePow hA, Complex.zero_im]

/-- The (real) values of the ideal von Mangoldt function are nonnegative. -/
theorem vonMangoldt_re_nonneg {A : (Ideal (𝓞 K))⁰} :
    0 ≤ ((vonMangoldt : IdealArithmeticFunction K) A).re := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow, Complex.ofReal_re]
    exact Real.log_nonneg (by exact_mod_cast (one_lt_absNorm_of_prime hP).le)
  · rw [vonMangoldt_of_not_isPrimePow hA, Complex.zero_re]

end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

/-- The **von Mangoldt transform** attached to a completely multiplicative ideal weight `χ`:
the ideal arithmetic function `A ↦ χ(A) Λ(A)`. -/
noncomputable def vonMangoldtTransform (χ : MultiplicativeIdealWeight K) :
    IdealArithmeticFunction K :=
  χ.toIdealArithmeticFunction * IdealArithmeticFunction.vonMangoldt

/-- Evaluation of the weighted von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (χ : MultiplicativeIdealWeight K)
    (A : (Ideal (𝓞 K))⁰) :
    χ.vonMangoldtTransform A = χ A * IdealArithmeticFunction.vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply, toIdealArithmeticFunction_apply]

/-- The weighted von Mangoldt transform vanishes at the unit ideal. -/
@[simp]
theorem vonMangoldtTransform_one (χ : MultiplicativeIdealWeight K) :
    χ.vonMangoldtTransform 1 = 0 := by
  rw [vonMangoldtTransform_apply, IdealArithmeticFunction.vonMangoldt_one, mul_zero]

/-- The weighted von Mangoldt transform on a positive power of a prime ideal. -/
theorem vonMangoldtTransform_apply_prime_pow (χ : MultiplicativeIdealWeight K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    χ.vonMangoldtTransform (P ^ n) =
      χ P ^ n * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [vonMangoldtTransform_apply,
    IdealArithmeticFunction.vonMangoldt_apply_prime_pow hP hn]
  congr 1
  exact map_pow χ (P : Ideal (𝓞 K)) n

/-- The support of the weighted von Mangoldt transform consists exactly of the prime powers on
which the weight is good. -/
theorem vonMangoldtTransform_ne_zero_iff (χ : MultiplicativeIdealWeight K)
    {A : (Ideal (𝓞 K))⁰} :
    χ.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ χ.IsGood (A : Ideal (𝓞 K)) := by
  rw [vonMangoldtTransform_apply, mul_ne_zero_iff,
    IdealArithmeticFunction.vonMangoldt_ne_zero_iff, χ.apply_ne_zero_iff_isGood, and_comm]

/-- In particular, the weighted von Mangoldt transform is supported on prime powers. -/
theorem vonMangoldtTransform_eq_zero_of_not_isPrimePow (χ : MultiplicativeIdealWeight K)
    {A : (Ideal (𝓞 K))⁰} (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    χ.vonMangoldtTransform A = 0 := by
  rw [vonMangoldtTransform_apply, IdealArithmeticFunction.vonMangoldt_of_not_isPrimePow hA,
    mul_zero]

/-- The transform of the trivial ideal weight is the ideal von Mangoldt function. -/
@[simp]
theorem one_vonMangoldtTransform :
    (1 : MultiplicativeIdealWeight K).vonMangoldtTransform =
      IdealArithmeticFunction.vonMangoldt := by
  rw [vonMangoldtTransform, toIdealArithmeticFunction_one, one_mul]

end MultiplicativeIdealWeight

namespace UnitaryIdealWeight

/-- The von Mangoldt transform of a unitary ideal weight, obtained from its underlying completely
multiplicative weight. -/
noncomputable def vonMangoldtTransform (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.vonMangoldtTransform

/-- Evaluation of the von Mangoldt transform of a unitary ideal weight. -/
theorem vonMangoldtTransform_apply (χ : UnitaryIdealWeight K) (A : (Ideal (𝓞 K))⁰) :
    χ.vonMangoldtTransform A = χ.1 A * IdealArithmeticFunction.vonMangoldt A :=
  χ.1.vonMangoldtTransform_apply A

/-- The support of the unitary weighted transform consists exactly of its good prime powers. -/
theorem vonMangoldtTransform_ne_zero_iff (χ : UnitaryIdealWeight K)
    {A : (Ideal (𝓞 K))⁰} :
    χ.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ χ.1.IsGood (A : Ideal (𝓞 K)) :=
  χ.1.vonMangoldtTransform_ne_zero_iff

end UnitaryIdealWeight

end TauCeti
