/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant

/-!
# Genus characters of a quadratic discriminant

Genus theory attaches to a fundamental discriminant `D` a family of real quadratic characters, one
for each prime discriminant occurring in a factorization `D = P₁ ⋯ P_t`
(`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`); the products of these over subsets
are the *genus characters* of `D`. The character `primeDiscriminantCharFun P` of a single prime
discriminant is built in
`TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character`. This file defines the
genus characters and proves the arithmetic fact that makes them characters of the class group: **an
integer coprime to `D` and represented by the principal form of discriminant `D` has all its genus
characters equal to `1`.**

The proof splits along the cases of the definition and is elementary. Write `D = P * Q`. If
`P = p*` is odd and `4n = x² - D y²`, then `x² ≡ 4n (mod p)`, so `n` is a nonzero quadratic residue
modulo `p`. If `P` is even, then `Q ≡ 1 (mod 4)` — that congruence is exactly what singles out the
correct even prime discriminant, `24 = (-8) * (-3)` rather than `8 * 3` — and `n` is odd; dividing
`x` by `2` turns the hypothesis into `n = u² - (P / 4) * Q * y²`, and a congruence modulo `8` pins
`n` down to `1 (mod 4)`, to `±1 (mod 8)`, or to `1, 3 (mod 8)` respectively, which is precisely the
triviality of `χ₄`, `χ₈` or `χ₈'` at `n`.

Because `4 * N(z) = A² - D * B²` for every algebraic integer `z` of the quadratic field
`K = ℚ(√d)` with `D = fundamentalDiscriminant d`
(`exists_sq_sub_fundamentalDiscriminant_mul_sq_eq_four_mul_norm`), the relation says that a genus
character of `D` is trivial at the norm of any algebraic integer of `K` coprime to the product of
the prime discriminants indexing it. That is the first step towards reading the genus characters as
characters of the narrow class group of `K`, whose independence is the lower bound `t - 1` in the
genus-theoretic `2`-rank formula. Contrapositively, `norm_ne_of_genusCharFun_eq_neg_one` is the
classical obstruction: an integer with a nontrivial genus character is not a norm.

The genus characters and this relation are classical; see D. A. Cox, *Primes of the Form x² + ny²*,
§3.B, and F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main definitions

* `TauCeti.Multiquadratic.genusCharFun`: the genus character indexed by a finite set of prime
  discriminants, the product of the characters it contains.

## Main results

* `TauCeti.Multiquadratic.primeDiscriminantCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq`: the
  genus-character relation for a single prime discriminant `P` in a factorization `D = P * Q`.
* `TauCeti.Multiquadratic.primeDiscriminantCharFun_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq` and
  `TauCeti.Multiquadratic.genusCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq`: the same relation for
  a prime discriminant, and for a genus character, of a prime-discriminant factorization of `D`.
* `TauCeti.Multiquadratic.genusCharFun_mod_right'`: a genus character is a character modulo the
  absolute value of the product of its indices.
* `TauCeti.Multiquadratic.genusCharFun_norm_eq_one`: a genus character of `D` is trivial at the
  norm of an algebraic integer of `ℚ(√d)` coprime to the product of its indices, and
  `TauCeti.Multiquadratic.norm_ne_of_genusCharFun_eq_neg_one` is the resulting obstruction;
  `TauCeti.Multiquadratic.primeDiscriminantCharFun_norm_eq_one` and
  `TauCeti.Multiquadratic.norm_ne_of_primeDiscriminantCharFun_eq_neg_one` are the single-index
  cases.
-/

public section

open Polynomial

open scoped NumberField

namespace TauCeti.Multiquadratic

/-! ### Values of the character on the principal form -/

/-- The base may be reduced modulo `m` before squaring. -/
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
theorem primeDiscriminantCharFun_eq_one_of_isEvenPrimeDiscriminant_of_four_mul_eq_sq_sub_mul_sq
    {P Q n x y : ℤ} (hP : IsEvenPrimeDiscriminant P) (hQ : Q % 4 = 1) (hn : ¬ (2 ∣ n))
    (h : 4 * n = x ^ 2 - P * Q * y ^ 2) : primeDiscriminantCharFun P n = 1 := by
  obtain ⟨R, hR⟩ : (4 : ℤ) ∣ P := by rcases hP with rfl | rfl | rfl <;> norm_num
  rw [hR] at h
  have hx4 : (4 : ℤ) ∣ x ^ 2 := ⟨n + R * (Q * y ^ 2), by linear_combination -h⟩
  have h24 : (2 : ℤ) ∣ 4 := by norm_num
  obtain ⟨u, rfl⟩ := Int.prime_two.dvd_of_dvd_pow (h24.trans hx4)
  have hn' : n = u ^ 2 - R * (Q * y ^ 2) :=
    mul_left_cancel₀ (a := (4 : ℤ)) (by norm_num) (by linear_combination h)
  have hQ8 : Q % 8 = 1 ∨ Q % 8 = 5 := by omega
  have key : n % 8 = (u ^ 2 % 8 - R % 8 * ((Q % 8) * (y ^ 2 % 8) % 8) % 8) % 8 := by
    rw [hn', Int.sub_emod, Int.mul_emod R (Q * y ^ 2) 8, Int.mul_emod Q (y ^ 2) 8]
  rcases hP with rfl | rfl | rfl
  · have hR1 : R = -1 := by omega
    subst hR1
    rw [primeDiscriminantCharFun_neg_four]
    refine ZMod.χ₄_int_one_mod_four ?_
    rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
      rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
  · have hR1 : R = 2 := by omega
    subst hR1
    rw [primeDiscriminantCharFun_eight, ZMod.χ₈_int_eq_if_mod_eight]
    have hn8 : n % 8 = 1 ∨ n % 8 = 7 := by
      rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
        rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
    rw [ite_eq_right (by omega), ite_eq_left hn8]
  · have hR1 : R = -2 := by omega
    subst hR1
    rw [primeDiscriminantCharFun_neg_eight, ZMod.χ₈'_int_eq_if_mod_eight]
    have hn8 : n % 8 = 1 ∨ n % 8 = 3 := by
      rcases sq_emod_eight u with hu | hu | hu <;> rcases sq_emod_eight y with hy | hy | hy <;>
        rcases hQ8 with hq | hq <;> rw [hu, hy, hq] at key <;> omega
    rw [ite_eq_right (by omega), ite_eq_left hn8]

/-- **The genus-character relation for a single prime discriminant.** Let `P` be a prime
discriminant and `Q` an integer, congruent to `1` modulo `4` when `P` is even. An integer `n`
coprime to `P` and satisfying `4n = x² - P * Q * y²` has trivial character at `P`. When `P * Q`
is supplied as an actual discriminant factorization, this equation says that `n` is represented by
the principal form of discriminant `P * Q`. -/
theorem primeDiscriminantCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq {P Q n x y : ℤ}
    (hP : IsPrimeDiscriminant P) (hQ : IsEvenPrimeDiscriminant P → Q % 4 = 1)
    (hcop : IsCoprime n P) (h : 4 * n = x ^ 2 - P * Q * y ^ 2) :
    primeDiscriminantCharFun P n = 1 := by
  rcases isPrimeDiscriminant_iff.mp hP with hP | ⟨p, hp, hodd, rfl⟩
  · exact primeDiscriminantCharFun_eq_one_of_isEvenPrimeDiscriminant_of_four_mul_eq_sq_sub_mul_sq
      hP (hQ hP) ((isCoprime_evenPrimeDiscriminant_iff_not_two_dvd hP).mp hcop) h
  · have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hodd; omega
    have hpd : (p : ℤ) ∣ oddPrimeDiscriminant p * Q :=
      (dvd_oddPrimeDiscriminant_iff.mpr dvd_rfl).mul_right Q
    rw [primeDiscriminantCharFun_oddPrimeDiscriminant hodd]
    exact jacobiSym_eq_one_of_dvd_of_four_mul_eq_sq_sub_mul_sq hp hp2 hpd
      (oddPrimeDiscriminant_dvd_iff.mpr.mt
        ((prime_oddPrimeDiscriminant hp).coprime_iff_not_dvd.mp hcop.symm)) h

/-! ### The genus characters of a fundamental discriminant -/

/-- A product of integers congruent to `1` modulo `4` is congruent to `1` modulo `4`. -/
private theorem prod_emod_four_eq_one {s : Finset ℤ} (hs : ∀ P ∈ s, P % 4 = 1) :
    (∏ P ∈ s, P) % 4 = 1 :=
  Finset.prod_induction _ (fun z => z % 4 = 1)
    (fun a b ha hb => by rw [Int.mul_emod, ha, hb]; norm_num) (by norm_num) hs

/-- **The genus-character relation.** Let `D = ∏ P ∈ s, P` be a factorization of a discriminant
into prime discriminants, at most one of them even, as produced by
`IsFundamentalDiscriminant.exists_finset_primeDiscriminant`. For each `P ∈ s`, every integer `n`
coprime to `P` and represented by the principal form of discriminant `D`, `4n = x² - D y²`, has
trivial character at `P`.

The hypothesis that at most one member of `s` is even is what makes the complementary factor
`∏ P' ∈ s.erase P, P'` congruent to `1` modulo `4` when `P` is the even one. -/
theorem primeDiscriminantCharFun_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    {P : ℤ} (hP : P ∈ s) {n x y : ℤ} (hcop : IsCoprime n P)
    (h : 4 * n = x ^ 2 - (∏ P ∈ s, P) * y ^ 2) :
    primeDiscriminantCharFun P n = 1 := by
  classical
  have hprod : ∏ P' ∈ s, P' = P * ∏ P' ∈ s.erase P, P' := (Finset.mul_prod_erase s _ hP).symm
  rw [hprod] at h
  refine primeDiscriminantCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq (hs P hP) ?_
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
def genusCharFun (s : Finset ℤ) (n : ℤ) : ℤ := ∏ P ∈ s, primeDiscriminantCharFun P n

/-- A genus character is the product of its prime-discriminant characters. -/
theorem genusCharFun_def (s : Finset ℤ) (n : ℤ) :
    genusCharFun s n = ∏ P ∈ s, primeDiscriminantCharFun P n := (rfl)

/-- The genus character indexed by the empty set is trivial. -/
@[simp] theorem genusCharFun_empty (n : ℤ) : genusCharFun ∅ n = 1 := by simp [genusCharFun_def]

/-- A singleton genus character is its prime-discriminant character. -/
@[simp] theorem genusCharFun_singleton (P n : ℤ) :
    genusCharFun {P} n = primeDiscriminantCharFun P n := by simp [genusCharFun_def]

/-- Inserting a fresh prime discriminant multiplies its character into the genus character. -/
@[simp] theorem genusCharFun_insert {s : Finset ℤ} {P : ℤ} (hP : P ∉ s) (n : ℤ) :
    genusCharFun (insert P s) n = primeDiscriminantCharFun P n * genusCharFun s n := by
  simp [genusCharFun_def, hP]

/-- A genus character is completely multiplicative. -/
@[simp] theorem genusCharFun_mul_right (s : Finset ℤ) (m n : ℤ) :
    genusCharFun s (m * n) = genusCharFun s m * genusCharFun s n := by
  simp [genusCharFun_def, primeDiscriminantCharFun_mul_right, Finset.prod_mul_distrib]

/-- A genus character takes the value `1` at `1`. -/
@[simp] theorem genusCharFun_one (s : Finset ℤ) : genusCharFun s 1 = 1 := by
  simp [genusCharFun_def]

/-- A genus character depends only on the residue class modulo the absolute value of the product
of its prime-discriminant indices: each factor is a character modulo `|P|`
(`primeDiscriminantCharFun_mod_right'`), and `P` divides that product. -/
theorem genusCharFun_mod_right' {s : Finset ℤ} {m n : ℤ}
    (h : m % (∏ P ∈ s, P).natAbs = n % (∏ P ∈ s, P).natAbs) :
    genusCharFun s m = genusCharFun s n := by
  rw [genusCharFun_def, genusCharFun_def]
  refine Finset.prod_congr rfl fun P hP => primeDiscriminantCharFun_mod_right' ?_
  have hdvd : (P.natAbs : ℤ) ∣ ((∏ P ∈ s, P).natAbs : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Int.natAbs_dvd_natAbs.mpr (Finset.dvd_prod_of_mem _ hP))
  rw [← Int.emod_emod_of_dvd m hdvd, ← Int.emod_emod_of_dvd n hdvd, h]

/-- A genus character vanishes exactly when its argument is not coprime to the product of its
prime-discriminant indices. -/
@[simp] theorem genusCharFun_eq_zero_iff {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) {n : ℤ} :
    genusCharFun s n = 0 ↔ ¬ IsCoprime n (∏ P ∈ s, P) := by
  rw [genusCharFun_def, Finset.prod_eq_zero_iff, IsCoprime.prod_right_iff]
  push Not
  constructor
  · rintro ⟨P, hP, hzero⟩
    exact ⟨P, hP, (primeDiscriminantCharFun_eq_zero_iff (hs P hP)).mp hzero⟩
  · rintro ⟨P, hP, hnotcop⟩
    exact ⟨P, hP, (primeDiscriminantCharFun_eq_zero_iff (hs P hP)).mpr hnotcop⟩

/-- A genus character takes the values `±1` on integers coprime to the product of its
prime-discriminant indices. -/
theorem genusCharFun_eq_one_or_eq_neg_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) {n : ℤ}
    (hcop : IsCoprime n (∏ P ∈ s, P)) : genusCharFun s n = 1 ∨ genusCharFun s n = -1 := by
  rw [IsCoprime.prod_right_iff] at hcop
  rw [genusCharFun_def]
  exact Finset.prod_induction _ (fun z => z = 1 ∨ z = -1)
    (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num)
    (Or.inl rfl)
    fun P hP => primeDiscriminantCharFun_eq_one_or_eq_neg_one (hs P hP) (hcop P hP)

/-- **The genus characters are trivial on the values of the principal form.** For a
prime-discriminant factorization `D = ∏ P ∈ s, P` and any subset `t ⊆ s`, the genus character
indexed by `t` is trivial at every integer coprime to the product of the factors in `t` that the
principal form of discriminant `D` represents. This is the arithmetic input for a future proof that
the genus characters descend to the class group. -/
theorem genusCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hts : t ⊆ s) {n x y : ℤ} (hcop : IsCoprime n (∏ P ∈ t, P))
    (h : 4 * n = x ^ 2 - (∏ P ∈ s, P) * y ^ 2) :
    genusCharFun t n = 1 :=
  Finset.prod_eq_one fun _ hP =>
    primeDiscriminantCharFun_eq_one_of_mem_of_four_mul_eq_sq_sub_mul_sq hs heven (hts hP)
      (hcop.of_prod_right _ hP) h

/-! ### Genus characters on the norms of a quadratic field -/

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The genus characters of a quadratic field are trivial on the norms of its integers.** Let
`K = ℚ(√d)` with `d` squarefree and let `D = fundamentalDiscriminant d` factor as `∏ P ∈ s, P` into
prime discriminants, at most one even. For a subset `t ⊆ s`, if the norm of an algebraic integer
`z` of `K` is coprime to `∏ P ∈ t, P`, then the genus character indexed by `t` is trivial at it.

This theorem handles element norms. Applying genus characters to ideal-class representatives will
require a further argument comparing representatives through principal ideals. -/
theorem genusCharFun_norm_eq_one {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) (z : 𝓞 K)
    (hcop : IsCoprime (Algebra.norm ℤ z) (∏ P ∈ t, P)) :
    genusCharFun t (Algebra.norm ℤ z) = 1 := by
  obtain ⟨A, B, hAB⟩ :=
    exists_sq_sub_fundamentalDiscriminant_mul_sq_eq_four_mul_norm hmin hgen hsf z
  refine genusCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq hs heven hts hcop (x := A) (y := B) ?_
  rw [hprod]
  linear_combination -hAB

/-- The single-index case of `genusCharFun_norm_eq_one`: the character at a prime discriminant
`P ∈ s` is trivial at the norms of the algebraic integers of `ℚ(√d)` that are coprime to `P`. -/
theorem primeDiscriminantCharFun_norm_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {P : ℤ} (hP : P ∈ s) (z : 𝓞 K)
    (hcop : IsCoprime (Algebra.norm ℤ z) P) :
    primeDiscriminantCharFun P (Algebra.norm ℤ z) = 1 := by
  rw [← genusCharFun_singleton]
  exact genusCharFun_norm_eq_one hs heven hprod hmin hgen hsf
    (Finset.singleton_subset_iff.mpr hP) z (by simpa using hcop)

/-- **Genus characters obstruct norms.** If a genus character of the quadratic field `K = ℚ(√d)`,
indexed by a subset `t` of a prime-discriminant factorization of its fundamental discriminant,
takes the value `-1` at an integer `n`, then `n` is not the norm of any algebraic integer of `K`.
This is the form in which genus theory rules out representations. -/
theorem norm_ne_of_genusCharFun_eq_neg_one {s t : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) {n : ℤ}
    (hchar : genusCharFun t n = -1) (z : 𝓞 K) : Algebra.norm ℤ z ≠ n := by
  intro hz
  subst hz
  have hcop : IsCoprime (Algebra.norm ℤ z) (∏ P ∈ t, P) := by
    by_contra hc
    rw [(genusCharFun_eq_zero_iff fun P hP => hs P (hts hP)).mpr hc] at hchar
    norm_num at hchar
  rw [genusCharFun_norm_eq_one hs heven hprod hmin hgen hsf hts z hcop] at hchar
  norm_num at hchar

/-- The single-index case of `norm_ne_of_genusCharFun_eq_neg_one`: an integer at which the
character of a prime discriminant `P ∈ s` takes the value `-1` is not the norm of an algebraic
integer of `ℚ(√d)`. -/
theorem norm_ne_of_primeDiscriminantCharFun_eq_neg_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {P n : ℤ} (hP : P ∈ s)
    (hchar : primeDiscriminantCharFun P n = -1) (z : 𝓞 K) : Algebra.norm ℤ z ≠ n := by
  refine norm_ne_of_genusCharFun_eq_neg_one hs heven hprod hmin hgen hsf
    (Finset.singleton_subset_iff.mpr hP) ?_ z
  rwa [genusCharFun_singleton]

-- A non-vacuity check for the genus-character relation: the integer `3` is coprime to the
-- fundamental discriminant `-20 = (-4) * 5` of `ℚ(√-5)` and has genus character `-1` at the
-- prime discriminant `-4`, so `3` is not represented by the principal form of discriminant `-20`
-- (equivalently, `3` is not the norm of an algebraic integer of `ℚ(√-5)`).
example : ¬ ∃ x y : ℤ, 4 * 3 = x ^ 2 - (-20 : ℤ) * y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hcop : IsCoprime (3 : ℤ) (-4) := by rw [Int.isCoprime_iff_gcd_eq_one]; decide
  have key := primeDiscriminantCharFun_eq_one_of_four_mul_eq_sq_sub_mul_sq (P := -4) (Q := 5)
    (n := 3) (x := x) (y := y) isPrimeDiscriminant_neg_four (fun _ => by norm_num) hcop
    (by linear_combination h)
  rw [primeDiscriminantCharFun_neg_four, ZMod.χ₄_int_eq_if_mod_four] at key
  norm_num at key

end TauCeti.Multiquadratic
