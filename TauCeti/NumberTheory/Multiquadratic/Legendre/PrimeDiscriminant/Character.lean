/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.EvenPrimeDiscriminant
public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Basic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The character attached to a prime discriminant

Genus theory attaches to a prime discriminant `P` the primitive real character modulo `|P|`
cutting out the quadratic field `ℚ(√P)`. Mathlib has no Kronecker symbol, so this file assembles
that character from the pieces Mathlib does have: it is `ZMod.χ₄`, `ZMod.χ₈` and `ZMod.χ₈'` at the
three even prime discriminants `-4`, `8` and `-8`, and the Legendre symbol `(· / p)`, written as a
Jacobi symbol, at an odd prime discriminant `p* = ±p`.

`primeDiscriminantCharFun_mul_right` and `primeDiscriminantCharFun_eq_one_or_eq_neg_one` record
that it is a `±1`-valued completely multiplicative function on the integers coprime to `P`, and
`primeDiscriminantCharFun_mod_right'` that its value depends only on the residue class modulo
`|P|`. The rest of this directory studies the Legendre symbols `legendreSym q P` of prime
discriminants at an odd prime `q`; `primeDiscriminantCharFun_eq_legendreSym` identifies the
character with them, so the splitting laws proved there are statements about the character.

The genus characters of a fundamental discriminant — the products of these characters over the
prime discriminants of a factorization `D = P₁ ⋯ P_t` — are built on this in
`TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Basic`. The material is classical;
see
D. A. Cox, *Primes of the Form x² + ny²*, §3.B, and F. Lemmermeyer, *Reciprocity Laws: From Euler
to Eisenstein*, §2.2.

## Main definitions

* `TauCeti.Multiquadratic.primeDiscriminantCharFun`: the real quadratic character modulo `|P|`
  attached to a prime discriminant `P`, as an unbundled function `ℤ → ℤ`.

## Main results

* `TauCeti.Multiquadratic.primeDiscriminantCharFun_mul_right` and
  `TauCeti.Multiquadratic.primeDiscriminantCharFun_eq_one_or_eq_neg_one`: the character is
  completely multiplicative, and takes the values `±1` on the integers coprime to `P`.
* `TauCeti.Multiquadratic.primeDiscriminantCharFun_eq_zero_iff`: it vanishes exactly off those
  integers.
* `TauCeti.Multiquadratic.primeDiscriminantCharFun_mod_right'`: it is a character modulo `|P|`.
* `TauCeti.Multiquadratic.primeDiscriminantCharFun_eq_legendreSym`: at an odd prime `q` its value
  is the Legendre symbol `legendreSym q P`.
-/

public section

namespace TauCeti.Multiquadratic

/-! ### The character attached to a prime discriminant -/

/-- The real quadratic character attached to a prime discriminant `P`: the primitive character
modulo `|P|` cutting out the quadratic field `ℚ(√P)`. At the even prime discriminants `-4`, `8`
and `-8` it is `ZMod.χ₄`, `ZMod.χ₈` and `ZMod.χ₈'`; at an odd prime discriminant `p*` it is the
Legendre symbol `(· / p)`, written as a Jacobi symbol. The value at an integer sharing a factor
with `P` is `0`.

The function is total: the prime-discriminant hypothesis is not bundled into it, but is carried by
the API below, which supplies the facts specific to prime discriminants. -/
def primeDiscriminantCharFun (P n : ℤ) : ℤ :=
  if P = -4 then ZMod.χ₄ (n : ZMod 4)
  else if P = 8 then ZMod.χ₈ (n : ZMod 8)
  else if P = -8 then ZMod.χ₈' (n : ZMod 8)
  else jacobiSym n P.natAbs

/-- The defining four-case description of the character attached to a prime discriminant. -/
theorem primeDiscriminantCharFun_def (P n : ℤ) :
    primeDiscriminantCharFun P n =
      if P = -4 then ZMod.χ₄ (n : ZMod 4)
      else if P = 8 then ZMod.χ₈ (n : ZMod 8)
      else if P = -8 then ZMod.χ₈' (n : ZMod 8)
      else jacobiSym n P.natAbs := by
  rw [primeDiscriminantCharFun]

/-- The character of the prime discriminant `-4` is `ZMod.χ₄`. -/
@[simp] theorem primeDiscriminantCharFun_neg_four (n : ℤ) :
    primeDiscriminantCharFun (-4) n = ZMod.χ₄ (n : ZMod 4) := by
  simp [primeDiscriminantCharFun_def]

/-- The character of the prime discriminant `8` is `ZMod.χ₈`. -/
@[simp] theorem primeDiscriminantCharFun_eight (n : ℤ) :
    primeDiscriminantCharFun 8 n = ZMod.χ₈ (n : ZMod 8) := by
  norm_num [primeDiscriminantCharFun_def]

/-- The character of the prime discriminant `-8` is `ZMod.χ₈'`. -/
@[simp] theorem primeDiscriminantCharFun_neg_eight (n : ℤ) :
    primeDiscriminantCharFun (-8) n = ZMod.χ₈' (n : ZMod 8) := by
  norm_num [primeDiscriminantCharFun_def]

/-- Away from the three even prime discriminants the character is a Jacobi symbol. -/
theorem primeDiscriminantCharFun_eq_jacobiSym_of_not_isEvenPrimeDiscriminant {P : ℤ}
    (hP : ¬ IsEvenPrimeDiscriminant P) (n : ℤ) :
    primeDiscriminantCharFun P n = jacobiSym n P.natAbs := by
  simp only [IsEvenPrimeDiscriminant, not_or] at hP
  simp [primeDiscriminantCharFun_def, hP.1, hP.2.1, hP.2.2]

/-- The character of the odd prime discriminant `p*` is the Legendre symbol `(· / p)`. In
particular it depends only on `p`, not on the sign normalization `p* = (-1) ^ ((p - 1) / 2) * p`. -/
@[simp] theorem primeDiscriminantCharFun_oddPrimeDiscriminant {p : ℕ} (hodd : Odd p) (n : ℤ) :
    primeDiscriminantCharFun (oddPrimeDiscriminant p) n = jacobiSym n p := by
  rw [primeDiscriminantCharFun_eq_jacobiSym_of_not_isEvenPrimeDiscriminant
    (not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hodd), oddPrimeDiscriminant_natAbs]

/-- The character attached to a prime discriminant is completely multiplicative. -/
@[simp] theorem primeDiscriminantCharFun_mul_right (P m n : ℤ) :
    primeDiscriminantCharFun P (m * n) =
      primeDiscriminantCharFun P m * primeDiscriminantCharFun P n := by
  unfold primeDiscriminantCharFun
  split_ifs <;> push_cast <;> simp [map_mul, jacobiSym.mul_left]

/-- The character attached to a prime discriminant takes the value `1` at `1`. -/
@[simp] theorem primeDiscriminantCharFun_one (P : ℤ) : primeDiscriminantCharFun P 1 = 1 := by
  unfold primeDiscriminantCharFun
  split_ifs <;> simp

/-- The character attached to `P` depends only on the residue class modulo `|P|`. -/
theorem primeDiscriminantCharFun_mod_right' {P m n : ℤ}
    (h : m % P.natAbs = n % P.natAbs) :
    primeDiscriminantCharFun P m = primeDiscriminantCharFun P n := by
  unfold primeDiscriminantCharFun
  split_ifs with hP4 hP8 hPneg8
  · subst P
    norm_num at h
    rw [ZMod.χ₄_int_mod_four m, ZMod.χ₄_int_mod_four n, h]
  · subst P
    norm_num at h
    rw [ZMod.χ₈_int_mod_eight m, ZMod.χ₈_int_mod_eight n, h]
  · subst P
    norm_num at h
    have h4 : m % 4 = n % 4 := by omega
    rw [ZMod.χ₈'_int_eq_χ₄_mul_χ₈, ZMod.χ₈'_int_eq_χ₄_mul_χ₈, ZMod.χ₄_int_mod_four m,
      ZMod.χ₄_int_mod_four n, ZMod.χ₈_int_mod_eight m, ZMod.χ₈_int_mod_eight n, h, h4]
  · exact jacobiSym.mod_left' h

/-- An integer is coprime to an even prime discriminant exactly when it is odd: the only prime
dividing `-4`, `8` or `-8` is `2`. -/
theorem isCoprime_evenPrimeDiscriminant_iff_not_two_dvd {P n : ℤ}
    (hP : IsEvenPrimeDiscriminant P) : IsCoprime n P ↔ ¬ (2 ∣ n) := by
  constructor
  · intro hcop hdvd
    have h2 : (2 : ℤ) ∣ P := by rcases hP with rfl | rfl | rfl <;> norm_num
    have hu := hcop.isUnit_of_dvd' hdvd h2
    rw [Int.isUnit_iff] at hu
    omega
  · intro hn
    have hcop : IsCoprime n (2 : ℤ) := (Int.prime_two.coprime_iff_not_dvd.mpr hn).symm
    rcases hP with rfl | rfl | rfl
    · simpa using (hcop.pow_right (n := 2)).neg_right
    · simpa using hcop.pow_right (n := 3)
    · simpa using (hcop.pow_right (n := 3)).neg_right

/-- The character attached to a prime discriminant takes the values `±1` on the integers
coprime to it. -/
theorem primeDiscriminantCharFun_eq_one_or_eq_neg_one {P n : ℤ} (hP : IsPrimeDiscriminant P)
    (hcop : IsCoprime n P) :
    primeDiscriminantCharFun P n = 1 ∨ primeDiscriminantCharFun P n = -1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
  · have h2 := (isCoprime_evenPrimeDiscriminant_iff_not_two_dvd hev).mp hcop
    rcases hev with rfl | rfl | rfl
    · rw [primeDiscriminantCharFun_neg_four, ZMod.χ₄_int_eq_if_mod_four, ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [primeDiscriminantCharFun_eight, ZMod.χ₈_int_eq_if_mod_eight, ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [primeDiscriminantCharFun_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight,
        ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [primeDiscriminantCharFun_oddPrimeDiscriminant hodd, ← jacobiSym.legendreSym.to_jacobiSym]
    refine legendreSym.eq_one_or_neg_one p ?_
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact oddPrimeDiscriminant_dvd_iff.mpr.mt
      ((prime_oddPrimeDiscriminant hp).coprime_iff_not_dvd.mp hcop.symm)

/-- The character attached to a prime discriminant vanishes exactly on the integers that are not
coprime to it. -/
@[simp] theorem primeDiscriminantCharFun_eq_zero_iff {P n : ℤ} (hP : IsPrimeDiscriminant P) :
    primeDiscriminantCharFun P n = 0 ↔ ¬ IsCoprime n P := by
  constructor
  · intro hz hcop
    rcases primeDiscriminantCharFun_eq_one_or_eq_neg_one hP hcop with h | h <;> omega
  · intro hcop
    rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
    · have hdvd : (2 : ℤ) ∣ n := by
        by_contra hn
        exact hcop ((isCoprime_evenPrimeDiscriminant_iff_not_two_dvd hev).mpr hn)
      rcases hev with rfl | rfl | rfl
      · rw [primeDiscriminantCharFun_neg_four, ZMod.χ₄_int_eq_if_mod_four]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
      · rw [primeDiscriminantCharFun_eight, ZMod.χ₈_int_eq_if_mod_eight]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
      · rw [primeDiscriminantCharFun_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
    · have : Fact p.Prime := ⟨hp⟩
      rw [Int.isCoprime_iff_nat_coprime, oddPrimeDiscriminant_natAbs] at hcop
      rw [primeDiscriminantCharFun_oddPrimeDiscriminant hodd,
        jacobiSym.eq_zero_iff_not_coprime]
      simpa [Int.gcd_eq_natAbs, Nat.coprime_iff_gcd_eq_one] using hcop

/-- The character attached to a prime discriminant `P` agrees at an odd prime `q` with the
Legendre symbol `legendreSym q P`, the splitting symbol of `P` at `q` studied in
`TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Basic` and
`TauCeti.NumberTheory.Multiquadratic.Legendre.EvenPrimeDiscriminant`. -/
theorem primeDiscriminantCharFun_eq_legendreSym {P : ℤ} (hP : IsPrimeDiscriminant P) {q : ℕ}
    [Fact q.Prime] (hq : q ≠ 2) : primeDiscriminantCharFun P q = legendreSym q P := by
  rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
  · rw [legendreSym_evenPrimeDiscriminant_eq_legendreSym_radicand hev hq,
      legendreSym_evenPrimeDiscriminantRadicand hev hq]
    rcases hev with rfl | rfl | rfl <;> push_cast <;> norm_num
  · have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hodd; omega
    rw [primeDiscriminantCharFun_oddPrimeDiscriminant hodd,
      legendreSym_oddPrimeDiscriminant_eq_legendreSym hp2 hq,
      jacobiSym.legendreSym.to_jacobiSym]

end TauCeti.Multiquadratic
