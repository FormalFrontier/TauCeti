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
packages that function as an `IdealArithmeticFunction` and defines its pointwise product with an
ideal arithmetic function.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

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

open NumberField
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

open Classical in
/-- The **ideal von Mangoldt function**.  It takes the value `log N(P)` on every positive power of
a prime ideal `P`, and vanishes on ideals which are not prime powers.

The codomain is `ℂ`, matching `IdealArithmeticFunction`, although every value is real. -/
noncomputable def vonMangoldt : IdealArithmeticFunction K := fun A ↦
  if h : IsPrimePow (A : Ideal (𝓞 K)) then
    (Real.log (Ideal.absNorm h.choose) : ℂ)
  else 0

/-- The ideal von Mangoldt function vanishes at the unit ideal. -/
@[simp]
theorem vonMangoldt_one : (vonMangoldt : IdealArithmeticFunction K) 1 = 0 := by
  rw [vonMangoldt, Submonoid.coe_one, dite_eq_right]
  exact isUnit_one.not_isPrimePow

/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem vonMangoldt_apply_of_eq_prime_pow {A : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hP : Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm P) := by
  have hA : IsPrimePow (A : Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  have hchosen : hA.choose = P := by
    exact eq_of_prime_pow_eq hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 (hA.choose_spec.choose_spec.2.2.trans hpow.symm)
  rw [vonMangoldt, dite_eq_left hA, hchosen]

/-- The ideal von Mangoldt function at a positive power of a prime nonzero ideal. -/
@[simp]
theorem vonMangoldt_apply_prime_pow {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    (vonMangoldt : IdealArithmeticFunction K) (P ^ n) =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  apply vonMangoldt_apply_of_eq_prime_pow hP hn
  simp

/-- The ideal von Mangoldt function at a prime ideal. -/
@[simp]
theorem vonMangoldt_apply_prime {P : (Ideal (𝓞 K))⁰}
    (hP : Prime (P : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) P =
      Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  simpa using vonMangoldt_apply_prime_pow hP (n := 1) zero_lt_one

/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 := by
  simp [vonMangoldt, hA]

private theorem one_lt_absNorm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero,
    Ideal.absNorm_eq_one_iff.not.mpr fun htop ↦
      hP.not_isUnit (Ideal.isUnit_iff.mpr htop)⟩

/-- The support of the ideal von Mangoldt function is exactly the set of prime-power ideals. -/
theorem vonMangoldt_ne_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A ≠ 0 ↔ IsPrimePow (A : Ideal (𝓞 K)) := by
  constructor
  · intro hne
    by_contra hnot
    exact hne (vonMangoldt_eq_zero_of_not_isPrimePow hnot)
  · rintro ⟨P, n, hP, hn, hpow⟩
    rw [vonMangoldt_apply_of_eq_prime_pow hP hn hpow]
    apply Complex.ofReal_ne_zero.mpr
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast Nat.zero_lt_one.trans (one_lt_absNorm_of_prime hP)
    · exact_mod_cast (one_lt_absNorm_of_prime hP).ne'

/-- The ideal von Mangoldt function vanishes exactly away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_iff {A : (Ideal (𝓞 K))⁰} :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 ↔ ¬ IsPrimePow (A : Ideal (𝓞 K)) :=
  by simpa only [not_ne_iff] using not_congr (vonMangoldt_ne_zero_iff (K := K) (A := A))

private theorem exists_ofReal_eq_vonMangoldt (A : (Ideal (𝓞 K))⁰) :
    ∃ r : ℝ, 0 ≤ r ∧ (vonMangoldt : IdealArithmeticFunction K) A = (r : ℂ) := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    refine ⟨Real.log (Ideal.absNorm P), Real.log_nonneg ?_,
      vonMangoldt_apply_of_eq_prime_pow hP hn hpow⟩
    exact_mod_cast (one_lt_absNorm_of_prime hP).le
  · exact ⟨0, le_rfl, vonMangoldt_eq_zero_of_not_isPrimePow hA⟩

/-- Every value of the ideal von Mangoldt function is real. -/
theorem vonMangoldt_im {A : (Ideal (𝓞 K))⁰} :
    ((vonMangoldt : IdealArithmeticFunction K) A).im = 0 := by
  obtain ⟨r, -, hr⟩ := exists_ofReal_eq_vonMangoldt A
  rw [hr, Complex.ofReal_im]

/-- The (real) values of the ideal von Mangoldt function are nonnegative. -/
theorem vonMangoldt_re_nonneg {A : (Ideal (𝓞 K))⁰} :
    0 ≤ ((vonMangoldt : IdealArithmeticFunction K) A).re := by
  obtain ⟨r, hr, hvalue⟩ := exists_ofReal_eq_vonMangoldt A
  rw [hvalue, Complex.ofReal_re]
  exact hr

/-- The **von Mangoldt transform** of an ideal arithmetic function `f`: the pointwise product
`A ↦ f(A) Λ(A)`. -/
noncomputable def vonMangoldtTransform (f : IdealArithmeticFunction K) :
    IdealArithmeticFunction K :=
  f * vonMangoldt

/-- Evaluation of the von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]

/-- The von Mangoldt transform on a positive power of a prime ideal. -/
@[simp]
theorem vonMangoldtTransform_apply_prime_pow (f : IdealArithmeticFunction K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    f.vonMangoldtTransform (P ^ n) =
      f (P ^ n) * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [vonMangoldtTransform_apply, vonMangoldt_apply_prime_pow hP hn]

/-- The support of a von Mangoldt transform is the intersection of the support of the original
function with the prime-power ideals. -/
@[simp]
theorem vonMangoldtTransform_ne_zero_iff (f : IdealArithmeticFunction K)
    {A : (Ideal (𝓞 K))⁰} :
    f.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ f A ≠ 0 := by
  rw [vonMangoldtTransform_apply, mul_ne_zero_iff, vonMangoldt_ne_zero_iff, and_comm]

/-- The transform of the constant-one ideal arithmetic function is the ideal von Mangoldt
function. -/
@[simp]
theorem vonMangoldtTransform_one :
    (1 : IdealArithmeticFunction K).vonMangoldtTransform = vonMangoldt := by
  rw [vonMangoldtTransform, one_mul]

end IdealArithmeticFunction

namespace MultiplicativeIdealWeight

/-- The von Mangoldt transform of a completely multiplicative weight on a positive power of a
prime ideal. -/
theorem vonMangoldtTransform_apply_prime_pow (χ : MultiplicativeIdealWeight K)
    {P : (Ideal (𝓞 K))⁰} (hP : Prime (P : Ideal (𝓞 K))) {n : ℕ} (hn : 0 < n) :
    χ.toIdealArithmeticFunction.vonMangoldtTransform (P ^ n) =
      χ P ^ n * Real.log (Ideal.absNorm (P : Ideal (𝓞 K))) := by
  rw [IdealArithmeticFunction.vonMangoldtTransform_apply_prime_pow _ hP hn,
    toIdealArithmeticFunction_apply]
  rw [SubmonoidClass.coe_pow, map_pow]

/-- The support of the von Mangoldt transform of a completely multiplicative weight consists
exactly of the prime powers on which the weight is good. -/
@[simp 1100]
theorem vonMangoldtTransform_ne_zero_iff (χ : MultiplicativeIdealWeight K)
    {A : (Ideal (𝓞 K))⁰} :
    χ.toIdealArithmeticFunction.vonMangoldtTransform A ≠ 0 ↔
      IsPrimePow (A : Ideal (𝓞 K)) ∧ χ.IsGood (A : Ideal (𝓞 K)) := by
  rw [IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff,
    toIdealArithmeticFunction_apply, χ.apply_ne_zero_iff_isGood]

end MultiplicativeIdealWeight

end TauCeti
