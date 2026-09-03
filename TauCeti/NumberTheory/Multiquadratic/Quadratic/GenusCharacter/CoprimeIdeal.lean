/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Genus characters on coprime ideals

For a factor `t` of a prime-discriminant factorization, the genus character
`genusCharFun t` is multiplicative but can vanish on integers sharing a prime factor with `t`.
This file packages its nonvanishing restriction as a genuine homomorphism on the monoid of
nonzero integral ideals whose absolute norm is coprime to the modulus `∏ P ∈ t, P`.

The homomorphism is the arithmetic input for descending genus characters to the narrow class
group. The descent theorem
`genusCharFun_absNorm_eq_of_span_mul_eq_span_mul` proves invariance under a narrow-principal
comparison when its two principal factors are also coprime to the modulus; the coprime
representative API supplies representatives satisfying the ideal-level condition.

The construction follows the genus-character packaging in D. A. Cox, *Primes of the Form
`x² + ny²`*, §3.B, and F. Lemmermeyer, *Reciprocity Laws*, §2.2. No external implementation is
vendored here.

## Main definitions and results

* `genusCharFunCoprimeIdealSubmonoid`: nonzero integral ideals coprime to the genus modulus.
* `genusCharFunCoprimeIdealHom`: the genus character as a homomorphism from that submonoid to
  `ℤˣ`, whose values are the units `1` and `-1`.
* `genusCharFunCoprimeIdealHom_apply`: the underlying integer value is the genus character of the
  ideal's absolute norm.
-/

public section

open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The monoid of nonzero integral ideals whose absolute norm is coprime to the modulus formed by
the prime discriminants in `t`. The prime-discriminant hypotheses needed for nonvanishing are
separate arguments to `genusCharFunCoprimeIdealHom`. -/
def genusCharFunCoprimeIdealSubmonoid (t : Finset ℤ) :
    Submonoid ((Ideal (𝓞 K))⁰) where
  carrier := {I | IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P)}
  one_mem' := by
    -- Unfold the carrier predicate to expose the ideal norm's monoid-one law.
    change IsCoprime (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P)
    rw [map_one]
    exact isCoprime_one_left
  mul_mem' := by
    intro I J hI hJ
    have hI' : IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := by
      simpa only [Set.mem_ofPred_eq] using hI
    have hJ' : IsCoprime (Ideal.absNorm (J : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := by
      simpa only [Set.mem_ofPred_eq] using hJ
    simpa only [Set.mem_ofPred_eq, Submonoid.coe_mul, map_mul, Nat.cast_mul] using
      hI'.mul_left hJ'

/-- Membership in the coprime-ideal submonoid is coprimality of the absolute norm with the
genus modulus. -/
@[simp] theorem mem_genusCharFunCoprimeIdealSubmonoid_iff {t : Finset ℤ}
    (I : (Ideal (𝓞 K))⁰) :
    I ∈ genusCharFunCoprimeIdealSubmonoid (K := K) t ↔
      IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := Iff.rfl

/-- The genus character on ideals coprime to its modulus, with values in the units of `ℤ`.
Its value on an ideal is `genusCharFun t (N I)`, viewed as the unit `1` or `-1`; the
prime-discriminant hypotheses ensure that this integer is nonzero. -/
noncomputable def genusCharFunCoprimeIdealHom {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P) :
    genusCharFunCoprimeIdealSubmonoid (K := K) t →* ℤˣ where
  toFun I := Units.mkOfMulEqOne (genusCharFun t (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ))
      (genusCharFun t (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ)) (by
    have hI : IsCoprime (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) (∏ P ∈ t, P) := I.property
    have hsign := genusCharFun_eq_one_or_eq_neg_one ht hI
    rcases hsign with hsign | hsign <;> simp [hsign])
  map_one' := by
    apply Units.ext
    rw [Units.val_mkOfMulEqOne]
    simp
  map_mul' I J := by
    apply Units.ext
    rw [Units.val_mkOfMulEqOne, Units.val_mul, Units.val_mkOfMulEqOne,
      Units.val_mkOfMulEqOne]
    have habs : Ideal.absNorm ((I : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) =
        Ideal.absNorm (I : Ideal (𝓞 K)) * Ideal.absNorm (J : Ideal (𝓞 K)) :=
      map_mul Ideal.absNorm _ _
    simp only [Submonoid.coe_mul]
    rw [habs, Nat.cast_mul, genusCharFun_mul_right]

/-- The underlying integer of the coprime-ideal genus character is the genus character of the
ideal's absolute norm. -/
@[simp] theorem genusCharFunCoprimeIdealHom_apply {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (I : genusCharFunCoprimeIdealSubmonoid (K := K) t) :
    (genusCharFunCoprimeIdealHom ht I : ℤ) =
      genusCharFun t (Ideal.absNorm (I : Ideal (𝓞 K)) : ℤ) := by
  simp only [genusCharFunCoprimeIdealHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_mkOfMulEqOne]

/-- The coprime-ideal genus character has value `1` or `-1`. -/
theorem genusCharFunCoprimeIdealHom_eq_one_or_eq_neg_one {t : Finset ℤ}
    (ht : ∀ P ∈ t, IsPrimeDiscriminant P)
    (I : genusCharFunCoprimeIdealSubmonoid (K := K) t) :
    genusCharFunCoprimeIdealHom ht I = 1 ∨ genusCharFunCoprimeIdealHom ht I = -1 := by
  rcases genusCharFun_eq_one_or_eq_neg_one ht I.property with h | h
  · left
    apply Units.ext
    simpa only [Units.val_one, genusCharFunCoprimeIdealHom_apply] using h
  · right
    apply Units.ext
    simpa only [Units.val_neg, Units.val_one, genusCharFunCoprimeIdealHom_apply] using h

end TauCeti.Multiquadratic
