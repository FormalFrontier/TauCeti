/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Genus characters of a quadratic discriminant

Genus theory attaches to a fundamental discriminant `D` a family of real quadratic characters, one
for each prime discriminant occurring in a factorization `D = P₁ ⋯ P_t`
(`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`); the products of these over subsets
are the *genus characters* of `D`. This file defines them and proves the arithmetic fact that makes
them characters of the class group: **an integer coprime to `D` and represented by the principal
form of discriminant `D` has all its genus characters equal to `1`.**

The character attached to a prime discriminant `P` is the primitive real character modulo `|P|`
cutting out `ℚ(√P)`: it is `ZMod.χ₄`, `ZMod.χ₈` and `ZMod.χ₈'` at the three even prime
discriminants `-4`, `8` and `-8`, and the Legendre symbol `(· / p)` at an odd prime discriminant
`p* = ±p`. Mathlib has no Kronecker symbol, so `primeDiscriminantChar` is defined by those four
cases; `primeDiscriminantChar_mul` and `primeDiscriminantChar_eq_one_or_eq_neg_one` record that it
is a `±1`-valued multiplicative function on the integers coprime to `P`.

The proof of the relation splits along the same cases and is elementary. Write `D = P * Q`. If
`P = p*` is odd and `4n = x² - D y²`, then `x² ≡ 4n (mod p)`, so `n` is a nonzero quadratic residue
modulo `p`. If `P` is even, then `Q ≡ 1 (mod 4)` — that congruence is exactly what singles out the
correct even prime discriminant, `24 = (-8) * (-3)` rather than `8 * 3` — and `n` is odd; dividing
`x` by `2` turns the hypothesis into `n = u² - (P / 4) * Q * y²`, and a congruence modulo `8` pins
`n` down to `1 (mod 4)`, to `±1 (mod 8)`, or to `1, 3 (mod 8)` respectively, which is precisely the
triviality of `χ₄`, `χ₈` or `χ₈'` at `n`.

Because `4 * N(z) = A² - D * B²` for every algebraic integer `z` of the quadratic field
`K = ℚ(√d)` with `D = fundamentalDiscriminant d`, the relation says that the genus characters of
`D` are trivial on the norms of `K` coprime to `D`. That is the first step towards reading them as
characters of the narrow class group of `K`, whose independence is the lower bound `t - 1` in the
genus-theoretic `2`-rank formula. Contrapositively,
`norm_ne_of_primeDiscriminantChar_eq_neg_one` is the classical obstruction: an integer with a
nontrivial genus character is not a norm.

The genus characters and this relation are classical; see D. A. Cox, *Primes of the Form x² + ny²*,
§3.B, and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main definitions

* `TauCeti.Multiquadratic.primeDiscriminantChar`: the real quadratic character modulo `|P|`
  attached to a prime discriminant `P`.
* `TauCeti.Multiquadratic.genusChar`: the genus character indexed by a finite set of prime
  discriminants, the product of the characters it contains.

## Main results

* `TauCeti.Multiquadratic.primeDiscriminantChar_eq_one_of_four_mul_eq_sq_sub_mul_sq`: the
  genus-character relation for a single prime discriminant `P` in a factorization `D = P * Q`.
* `TauCeti.Multiquadratic.primeDiscriminantChar_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq` and
  `TauCeti.Multiquadratic.genusChar_eq_one_of_four_mul_eq_sq_sub_mul_sq`: the same relation for a
  prime discriminant, and for a genus character, of a prime-discriminant factorization of `D`.
* `TauCeti.Multiquadratic.exists_sq_sub_fundamentalDiscriminant_mul_sq_eq_four_mul_norm`: the norm
  form of a quadratic field, written with its fundamental discriminant.
* `TauCeti.Multiquadratic.primeDiscriminantChar_norm_eq_one`: the character at `P` is trivial on
  the norms of algebraic integers of `ℚ(√d)` that are coprime to `P`, and
  `TauCeti.Multiquadratic.norm_ne_of_primeDiscriminantChar_eq_neg_one` is the resulting obstruction.
-/

public section

open Polynomial

open scoped NumberField

namespace TauCeti.Multiquadratic

/-! ### The character attached to a prime discriminant -/

/-- The real quadratic character attached to a prime discriminant `P`: the primitive character
modulo `|P|` cutting out the quadratic field `ℚ(√P)`. At the even prime discriminants `-4`, `8`
and `-8` it is `ZMod.χ₄`, `ZMod.χ₈` and `ZMod.χ₈'`; at an odd prime discriminant `p*` it is the
Legendre symbol `(· / p)`, written as a Jacobi symbol. The value at an integer sharing a factor
with `P` is `0`.

The prime-discriminant hypothesis is not part of the definition, so that the expression rewrites by
computation; the API below supplies the facts specific to prime discriminants. -/
def primeDiscriminantChar (P n : ℤ) : ℤ :=
  if P = -4 then ZMod.χ₄ (n : ZMod 4)
  else if P = 8 then ZMod.χ₈ (n : ZMod 8)
  else if P = -8 then ZMod.χ₈' (n : ZMod 8)
  else jacobiSym n P.natAbs

/-- The character of the prime discriminant `-4` is `ZMod.χ₄`. -/
@[simp] theorem primeDiscriminantChar_neg_four (n : ℤ) :
    primeDiscriminantChar (-4) n = ZMod.χ₄ (n : ZMod 4) := by
  simp [primeDiscriminantChar]

/-- The character of the prime discriminant `8` is `ZMod.χ₈`. -/
@[simp] theorem primeDiscriminantChar_eight (n : ℤ) :
    primeDiscriminantChar 8 n = ZMod.χ₈ (n : ZMod 8) := by
  norm_num [primeDiscriminantChar]

/-- The character of the prime discriminant `-8` is `ZMod.χ₈'`. -/
@[simp] theorem primeDiscriminantChar_neg_eight (n : ℤ) :
    primeDiscriminantChar (-8) n = ZMod.χ₈' (n : ZMod 8) := by
  norm_num [primeDiscriminantChar]

/-- Away from the three even prime discriminants the character is a Jacobi symbol. -/
theorem primeDiscriminantChar_of_not_isEvenPrimeDiscriminant {P : ℤ}
    (hP : ¬ IsEvenPrimeDiscriminant P) (n : ℤ) :
    primeDiscriminantChar P n = jacobiSym n P.natAbs := by
  simp only [IsEvenPrimeDiscriminant, not_or] at hP
  simp [primeDiscriminantChar, hP.1, hP.2.1, hP.2.2]

/-- The character of the odd prime discriminant `p*` is the Legendre symbol `(· / p)`. In
particular it depends only on `p`, not on the sign normalization `p* = (-1) ^ ((p - 1) / 2) * p`. -/
@[simp] theorem primeDiscriminantChar_oddPrimeDiscriminant {p : ℕ} (hodd : Odd p) (n : ℤ) :
    primeDiscriminantChar (oddPrimeDiscriminant p) n = jacobiSym n p := by
  rw [primeDiscriminantChar_of_not_isEvenPrimeDiscriminant
    (not_isEvenPrimeDiscriminant_oddPrimeDiscriminant hodd), oddPrimeDiscriminant_natAbs]

/-- The character attached to a prime discriminant is completely multiplicative. -/
@[simp] theorem primeDiscriminantChar_mul (P m n : ℤ) :
    primeDiscriminantChar P (m * n) =
      primeDiscriminantChar P m * primeDiscriminantChar P n := by
  unfold primeDiscriminantChar
  split_ifs <;> push_cast <;> simp [map_mul, jacobiSym.mul_left]

/-- The character attached to a prime discriminant takes the value `1` at `1`. -/
@[simp] theorem primeDiscriminantChar_one (P : ℤ) : primeDiscriminantChar P 1 = 1 := by
  unfold primeDiscriminantChar
  split_ifs <;> simp

/-- The character attached to `P` depends only on the residue class modulo `|P|`. -/
theorem primeDiscriminantChar_congr {P m n : ℤ}
    (h : m % P.natAbs = n % P.natAbs) :
    primeDiscriminantChar P m = primeDiscriminantChar P n := by
  unfold primeDiscriminantChar
  split_ifs with hP4 hP8 hPneg8
  · subst P
    norm_num at h
    congr 1
    rw [← ZMod.intCast_mod m 4, ← ZMod.intCast_mod n 4]
    exact congrArg (fun z : ℤ => (z : ZMod 4)) h
  · subst P
    norm_num at h
    congr 1
    rw [← ZMod.intCast_mod m 8, ← ZMod.intCast_mod n 8]
    exact congrArg (fun z : ℤ => (z : ZMod 8)) h
  · subst P
    norm_num at h
    congr 1
    rw [← ZMod.intCast_mod m 8, ← ZMod.intCast_mod n 8]
    exact congrArg (fun z : ℤ => (z : ZMod 8)) h
  · exact jacobiSym.mod_left' h

/-- An integer coprime to an even prime discriminant is odd. -/
private theorem not_two_dvd_of_isCoprime {P n : ℤ} (hP : IsEvenPrimeDiscriminant P)
    (hcop : IsCoprime n P) : ¬ (2 ∣ n) := by
  intro hdvd
  have h2 : (2 : ℤ) ∣ P := by rcases hP with rfl | rfl | rfl <;> norm_num
  have hu := hcop.isUnit_of_dvd' hdvd h2
  rw [Int.isUnit_iff] at hu
  omega

/-- An integer coprime to an odd prime discriminant is not divisible by the underlying prime. -/
private theorem not_dvd_of_isCoprime {p : ℕ} (hp : p.Prime) {n : ℤ}
    (hcop : IsCoprime n (oddPrimeDiscriminant p)) : ¬ (p : ℤ) ∣ n := by
  intro hdvd
  have hu := hcop.isUnit_of_dvd' hdvd (dvd_oddPrimeDiscriminant_iff.mpr dvd_rfl)
  rw [Int.isUnit_iff] at hu
  exact hp.ne_one (by omega)

/-- The character attached to a prime discriminant takes the values `±1` on the integers
coprime to it. -/
theorem primeDiscriminantChar_eq_one_or_eq_neg_one {P n : ℤ} (hP : IsPrimeDiscriminant P)
    (hcop : IsCoprime n P) :
    primeDiscriminantChar P n = 1 ∨ primeDiscriminantChar P n = -1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
  · have h2 := not_two_dvd_of_isCoprime hev hcop
    rcases hev with rfl | rfl | rfl
    · rw [primeDiscriminantChar_neg_four, ZMod.χ₄_int_eq_if_mod_four, ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [primeDiscriminantChar_eight, ZMod.χ₈_int_eq_if_mod_eight, ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [primeDiscriminantChar_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight, ite_eq_right (by omega)]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [primeDiscriminantChar_oddPrimeDiscriminant hodd, ← jacobiSym.legendreSym.to_jacobiSym]
    refine legendreSym.eq_one_or_neg_one p ?_
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact not_dvd_of_isCoprime hp hcop

/-- The character attached to a prime discriminant vanishes exactly on the integers that are not
coprime to it. -/
@[simp] theorem primeDiscriminantChar_eq_zero_iff {P n : ℤ} (hP : IsPrimeDiscriminant P) :
    primeDiscriminantChar P n = 0 ↔ ¬ IsCoprime n P := by
  constructor
  · intro hz hcop
    rcases primeDiscriminantChar_eq_one_or_eq_neg_one hP hcop with h | h <;> omega
  · intro hcop
    rcases isPrimeDiscriminant_iff.mp hP with hev | ⟨p, hp, hodd, rfl⟩
    · rcases hev with rfl | rfl | rfl
      · have hdvd : (2 : ℤ) ∣ n := by
          by_contra hn
          apply hcop
          simpa using
            ((Int.prime_two.coprime_iff_not_dvd.mpr hn).symm.pow_right (n := 2)).neg_right
        rw [primeDiscriminantChar_neg_four, ZMod.χ₄_int_eq_if_mod_four]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
      · have hdvd : (2 : ℤ) ∣ n := by
          by_contra hn
          apply hcop
          simpa using (Int.prime_two.coprime_iff_not_dvd.mpr hn).symm.pow_right (n := 3)
        rw [primeDiscriminantChar_eight, ZMod.χ₈_int_eq_if_mod_eight]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
      · have hdvd : (2 : ℤ) ∣ n := by
          by_contra hn
          apply hcop
          simpa using
            ((Int.prime_two.coprime_iff_not_dvd.mpr hn).symm.pow_right (n := 3)).neg_right
        rw [primeDiscriminantChar_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight]
        simp only [Int.dvd_iff_emod_eq_zero.mp hdvd, ↓reduceIte]
    · have : Fact p.Prime := ⟨hp⟩
      rw [Int.isCoprime_iff_nat_coprime, oddPrimeDiscriminant_natAbs] at hcop
      rw [primeDiscriminantChar_oddPrimeDiscriminant hodd,
        jacobiSym.eq_zero_iff_not_coprime]
      simpa [Int.gcd_eq_natAbs, Nat.coprime_iff_gcd_eq_one] using hcop

/-! ### Values of the character on the principal form -/

/-- Squares may be reduced modulo `m` before squaring. -/
private theorem sq_emod (a m : ℤ) : a ^ 2 % m = (a % m) ^ 2 % m := by
  rw [pow_two, pow_two, Int.mul_emod]

/-- The squares modulo `8`. -/
private theorem sq_emod_eight (a : ℤ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
      a % 8 = 6 ∨ a % 8 = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> rw [sq_emod a 8, h] <;> norm_num

/-- **The odd half of the genus-character relation.** If an odd prime `p` divides `D` but not `n`,
and `4n = x² - D y²`, then `n` is a nonzero quadratic residue modulo `p`: reducing the hypothesis
modulo `p` kills the `D y²` term and leaves `4n ≡ x²`, so `n` is the square of `x / 2`. -/
theorem jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D n x y : ℤ} (hpD : (p : ℤ) ∣ D) (hpn : ¬ (p : ℤ) ∣ n)
    (h : 4 * n = x ^ 2 - D * y ^ 2) : jacobiSym n p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hdvd : ¬ ((p : ℤ) ∣ 2) := fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast hdvd))
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).not.mpr hdvd
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  refine (legendreSym.eq_one_iff p hn0).mpr ⟨(x : ZMod p) * 2⁻¹, ?_⟩
  have hD0 : (D : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpD
  have h4 : (4 : ZMod p) * (n : ZMod p) = (x : ZMod p) ^ 2 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod p)) h
    push_cast at hcast
    rw [hD0] at hcast
    simpa using hcast
  field_simp
  linear_combination h4

/-- **The even half of the genus-character relation.** Let `P` be an even prime discriminant and
`Q ≡ 1 (mod 4)`. If an odd integer `n` satisfies `4n = x² - P * Q * y²`, then the character of `P`
is trivial at `n`.

Halving `x` — which is even, because `4 ∣ P` — rewrites the hypothesis as
`n = u² - (P / 4) * Q * y²`, and the value of `n` modulo `8` is then forced into the kernel of the
corresponding character. -/
theorem primeDiscriminantChar_eq_one_of_isEvenPrimeDiscriminant {P Q n x y : ℤ}
    (hP : IsEvenPrimeDiscriminant P) (hQ : Q % 4 = 1) (hn : ¬ (2 ∣ n))
    (h : 4 * n = x ^ 2 - P * Q * y ^ 2) : primeDiscriminantChar P n = 1 := by
  obtain ⟨R, hR⟩ : (4 : ℤ) ∣ P := by rcases hP with rfl | rfl | rfl <;> norm_num
  rw [hR] at h
  have hx4 : (4 : ℤ) ∣ x ^ 2 := ⟨n + R * (Q * y ^ 2), by linear_combination -h⟩
  obtain ⟨u, rfl⟩ :=
    Int.prime_two.dvd_of_dvd_pow ((show (2 : ℤ) ∣ 4 by norm_num).trans hx4)
  have hn' : n = u ^ 2 - R * (Q * y ^ 2) :=
    mul_left_cancel₀ (a := (4 : ℤ)) (by norm_num) (by linear_combination h)
  have hQ8 : Q % 8 = 1 ∨ Q % 8 = 5 := by omega
  have key : n % 8 = (u ^ 2 % 8 - R % 8 * ((Q % 8) * (y ^ 2 % 8) % 8) % 8) % 8 := by
    rw [hn', Int.sub_emod, Int.mul_emod R (Q * y ^ 2) 8, Int.mul_emod Q (y ^ 2) 8]
  rcases hP with rfl | rfl | rfl
  · have hR1 : R = -1 := by omega
    subst hR1
    rw [primeDiscriminantChar_neg_four]
    refine ZMod.χ₄_int_one_mod_four ?_
    rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
      rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
  · have hR1 : R = 2 := by omega
    subst hR1
    rw [primeDiscriminantChar_eight, ZMod.χ₈_int_eq_if_mod_eight]
    have hn8 : n % 8 = 1 ∨ n % 8 = 7 := by
      rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
        rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
    rw [ite_eq_right (by omega), ite_eq_left hn8]
  · have hR1 : R = -2 := by omega
    subst hR1
    rw [primeDiscriminantChar_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight]
    have hn8 : n % 8 = 1 ∨ n % 8 = 3 := by
      rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
        rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
    rw [ite_eq_right (by omega), ite_eq_left hn8]

/-- **The genus-character relation for a single prime discriminant.** Let `P` be a prime
discriminant and `Q` an integer, congruent to `1` modulo `4` when `P` is even. An integer `n`
coprime to `P` and satisfying `4n = x² - P * Q * y²` has trivial character at `P`. When `P * Q`
is supplied as an actual discriminant factorization, this equation says that `n` is represented by
the principal form of discriminant `P * Q`. -/
theorem primeDiscriminantChar_eq_one_of_four_mul_eq_sq_sub_mul_sq {P Q n x y : ℤ}
    (hP : IsPrimeDiscriminant P) (hQ : IsEvenPrimeDiscriminant P → Q % 4 = 1)
    (hcop : IsCoprime n P) (h : 4 * n = x ^ 2 - P * Q * y ^ 2) :
    primeDiscriminantChar P n = 1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hP | ⟨p, hp, hodd, rfl⟩
  · exact primeDiscriminantChar_eq_one_of_isEvenPrimeDiscriminant hP (hQ hP)
      (not_two_dvd_of_isCoprime hP hcop) h
  · have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hodd; omega
    have hpd : (p : ℤ) ∣ oddPrimeDiscriminant p * Q :=
      (dvd_oddPrimeDiscriminant_iff.mpr dvd_rfl).mul_right Q
    rw [primeDiscriminantChar_oddPrimeDiscriminant hodd]
    exact jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq hp hp2 hpd
      (not_dvd_of_isCoprime hp hcop) h

/-! ### The genus characters of a fundamental discriminant -/

/-- A product of integers congruent to `1` modulo `4` is congruent to `1` modulo `4`. -/
private theorem prod_emod_four_eq_one {s : Finset ℤ} (hs : ∀ P ∈ s, P % 4 = 1) :
    (∏ P ∈ s, P) % 4 = 1 :=
  Finset.prod_induction _ (fun z => z % 4 = 1)
    (fun a b ha hb => by rw [Int.mul_emod, ha, hb]; norm_num) (by norm_num) hs

/-- **The genus-character relation.** Let `D = ∏ P ∈ s, P` be a factorization of a discriminant
into prime discriminants, at most one of them even, as produced by
`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`. Every integer `n` coprime to `P` and
represented by the principal form of discriminant `D`, `4n = x² - D y²`, has trivial character at
each `P ∈ s`.

The hypothesis that at most one member of `s` is even is what makes the complementary factor
`∏ P' ∈ s.erase P, P'` congruent to `1` modulo `4` when `P` is the even one. -/
theorem primeDiscriminantChar_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {P : ℤ} (hP : P ∈ s) {n x y : ℤ} (hcop : IsCoprime n P)
    (h : 4 * n = x ^ 2 - (∏ P ∈ s, P) * y ^ 2) :
    primeDiscriminantChar P n = 1 := by
  classical
  have hprod : ∏ P' ∈ s, P' = P * ∏ P' ∈ s.erase P, P' := (Finset.mul_prod_erase s _ hP).symm
  rw [hprod] at h
  refine primeDiscriminantChar_eq_one_of_four_mul_eq_sq_sub_mul_sq (hs P hP) ?_
    hcop h
  intro hPeven
  refine prod_emod_four_eq_one fun P' hP' => ?_
  have hmem : P' ∈ s := Finset.mem_of_mem_erase hP'
  rcases isPrimeDiscriminant_iff.mp (hs P' hmem) with hev | ⟨p, _, hodd, rfl⟩
  · exact absurd (heven P hP P' hmem hPeven hev).symm (Finset.ne_of_mem_erase hP')
  · exact oddPrimeDiscriminant_mod_four_eq_one hodd

/-- The genus character indexed by a finite set `s` of prime discriminants: the product of the
characters they carry. The genus characters of a fundamental discriminant `D` are those indexed by
the subsets of a prime-discriminant factorization of `D`. -/
def genusChar (s : Finset ℤ) (n : ℤ) : ℤ := ∏ P ∈ s, primeDiscriminantChar P n

/-- A genus character is the product of its prime-discriminant characters. -/
theorem genusChar_def (s : Finset ℤ) (n : ℤ) :
    genusChar s n = ∏ P ∈ s, primeDiscriminantChar P n := (rfl)

/-- The genus character indexed by the empty set is trivial. -/
@[simp] theorem genusChar_empty (n : ℤ) : genusChar ∅ n = 1 := by simp [genusChar_def]

/-- A singleton genus character is its prime-discriminant character. -/
@[simp] theorem genusChar_singleton (P n : ℤ) :
    genusChar {P} n = primeDiscriminantChar P n := by simp [genusChar_def]

/-- Inserting a fresh prime discriminant multiplies its character into the genus character. -/
@[simp] theorem genusChar_insert {s : Finset ℤ} {P : ℤ} (hP : P ∉ s) (n : ℤ) :
    genusChar (insert P s) n = primeDiscriminantChar P n * genusChar s n := by
  simp [genusChar_def, hP]

/-- A genus character is completely multiplicative. -/
@[simp] theorem genusChar_mul (s : Finset ℤ) (m n : ℤ) :
    genusChar s (m * n) = genusChar s m * genusChar s n := by
  simp [genusChar, primeDiscriminantChar_mul, Finset.prod_mul_distrib]

/-- A genus character takes the value `1` at `1`. -/
@[simp] theorem genusChar_one (s : Finset ℤ) : genusChar s 1 = 1 := by simp [genusChar]

/-- A genus character vanishes exactly when its argument is not coprime to the product of its
prime-discriminant indices. -/
@[simp] theorem genusChar_eq_zero_iff {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) {n : ℤ} :
    genusChar s n = 0 ↔ ¬ IsCoprime n (∏ P ∈ s, P) := by
  rw [genusChar, Finset.prod_eq_zero_iff, IsCoprime.prod_right_iff]
  push Not
  constructor
  · rintro ⟨P, hP, hzero⟩
    exact ⟨P, hP, (primeDiscriminantChar_eq_zero_iff (hs P hP)).mp hzero⟩
  · rintro ⟨P, hP, hnotcop⟩
    exact ⟨P, hP, (primeDiscriminantChar_eq_zero_iff (hs P hP)).mpr hnotcop⟩

/-- A genus character takes the values `±1` on integers coprime to the product of its
prime-discriminant indices. -/
theorem genusChar_eq_one_or_eq_neg_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) {n : ℤ}
    (hcop : IsCoprime n (∏ P ∈ s, P)) : genusChar s n = 1 ∨ genusChar s n = -1 := by
  rw [IsCoprime.prod_right_iff] at hcop
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert P s hP ih =>
      rw [genusChar_insert hP]
      rcases primeDiscriminantChar_eq_one_or_eq_neg_one (hs P (Finset.mem_insert_self P s))
          (hcop P (Finset.mem_insert_self P s)) with hchar | hchar <;>
        rcases ih (fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ))
          (fun Q hQ => hcop Q (Finset.mem_insert_of_mem hQ)) with hgenus | hgenus <;>
        rw [hchar, hgenus] <;> norm_num

/-- **The genus characters are trivial on the values of the principal form.** For a
prime-discriminant factorization `D = ∏ P ∈ s, P` and any subset `t ⊆ s`, the genus character
indexed by `t` is trivial at every integer coprime to the product of the factors in `t` that the
principal form of discriminant `D` represents. This is the arithmetic input for a future proof that
the genus characters descend to the class group. -/
theorem genusChar_eq_one_of_four_mul_eq_sq_sub_mul_sq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hts : t ⊆ s) {n x y : ℤ} (hcop : IsCoprime n (∏ P ∈ t, P))
    (h : 4 * n = x ^ 2 - (∏ P ∈ s, P) * y ^ 2) :
    genusChar t n = 1 :=
  Finset.prod_eq_one fun _ hP =>
    primeDiscriminantChar_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq hs heven (hts hP)
      (hcop.of_prod_right _ hP) h

/-! ### Genus characters on the norms of a quadratic field -/

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The norm form of a quadratic field, written with its fundamental discriminant.** For a
quadratic field `K = ℚ(√d)` with `d` squarefree, every algebraic integer `z` of `K` satisfies
`A² - D * B² = 4 * N(z)` for some integers `A, B`, where `D = fundamentalDiscriminant d`. This is
`NumberField.exists_sq_sub_mul_sq_eq_four_mul_norm` when `d ≡ 1 (mod 4)`, and rescales
`NumberField.exists_sq_sub_mul_sq_eq_norm_of_mod_four_ne_one` by `2` otherwise; it is the uniform
statement the genus-character relation consumes. -/
theorem exists_sq_sub_fundamentalDiscriminant_mul_sq_eq_four_mul_norm
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (z : 𝓞 K) :
    ∃ A B : ℤ, A ^ 2 - fundamentalDiscriminant d * B ^ 2 = 4 * Algebra.norm ℤ z := by
  by_cases hd : d % 4 = 1
  · rw [fundamentalDiscriminant_of_mod_four_eq_one hd]
    exact NumberField.exists_sq_sub_mul_sq_eq_four_mul_norm hmin hgen hsf z
  · rw [fundamentalDiscriminant_of_mod_four_ne_one hd]
    obtain ⟨A, B, hAB⟩ :=
      NumberField.exists_sq_sub_mul_sq_eq_norm_of_mod_four_ne_one hmin hgen hsf hd z
    exact ⟨2 * A, B, by linear_combination 4 * hAB⟩

/-- **The genus characters of a quadratic field are trivial on the norms of its integers.** Let
`K = ℚ(√d)` with `d` squarefree and let `D = fundamentalDiscriminant d` factor as `∏ P ∈ s, P` into
prime discriminants, at most one even. If the norm of an algebraic integer `z` of `K` is coprime to
`P`, then the character `primeDiscriminantChar P` is trivial at it.

This theorem handles element norms. Applying genus characters to ideal-class representatives will
require a further argument comparing representatives through principal ideals. -/
theorem primeDiscriminantChar_norm_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {P : ℤ} (hP : P ∈ s) (z : 𝓞 K)
    (hcop : IsCoprime (Algebra.norm ℤ z) P) :
    primeDiscriminantChar P (Algebra.norm ℤ z) = 1 := by
  obtain ⟨A, B, hAB⟩ :=
    exists_sq_sub_fundamentalDiscriminant_mul_sq_eq_four_mul_norm hmin hgen hsf z
  refine primeDiscriminantChar_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq hs heven hP
    hcop (x := A) (y := B) ?_
  rw [hprod]
  linear_combination -hAB

/-- **Genus characters obstruct norms.** If the genus character of the quadratic field
`K = ℚ(√d)` at a prime discriminant `P` dividing its fundamental discriminant takes the value
`-1` at an integer `n` coprime to `P`, then `n` is not the norm of any algebraic
integer of `K`. This is the form in which genus theory rules out representations. -/
theorem norm_ne_of_primeDiscriminantChar_eq_neg_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {P n : ℤ} (hP : P ∈ s)
    (hcop : IsCoprime n P)
    (hchar : primeDiscriminantChar P n = -1) (z : 𝓞 K) : Algebra.norm ℤ z ≠ n := by
  intro hz
  subst hz
  rw [primeDiscriminantChar_norm_eq_one hs heven hprod hmin hgen hsf hP z hcop] at hchar
  norm_num at hchar

-- A non-vacuity check for the genus-character relation: the integer `3` is coprime to the
-- fundamental discriminant `-20 = (-4) * 5` of `ℚ(√-5)` and has genus character `-1` at the
-- prime discriminant `-4`, so `3` is not represented by the principal form of discriminant `-20`
-- (equivalently, `3` is not the norm of an algebraic integer of `ℚ(√-5)`).
example : ¬ ∃ x y : ℤ, 4 * 3 = x ^ 2 - (-20 : ℤ) * y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hcop : IsCoprime (3 : ℤ) (-4) := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have key := primeDiscriminantChar_eq_one_of_four_mul_eq_sq_sub_mul_sq (P := -4) (Q := 5)
    (n := 3) (x := x) (y := y) isPrimeDiscriminant_neg_four (fun _ => by norm_num) hcop
    (by linear_combination h)
  rw [primeDiscriminantChar_neg_four, ZMod.χ₄_int_eq_if_mod_four] at key
  norm_num at key

end TauCeti.Multiquadratic
