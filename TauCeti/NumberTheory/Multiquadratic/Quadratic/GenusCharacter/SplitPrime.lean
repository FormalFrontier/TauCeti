/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.Quadratic.Splitting

/-!
# Genus characters at a split prime

Let `K = ℚ(√d)` with `d` squarefree, and let `D = ∏ P ∈ s, P` be a factorization of its
discriminant into prime discriminants. Evaluating the genus characters of `s` at an odd prime `q`
is the same as evaluating the Legendre symbols of the `P ∈ s` at `q`, because each
prime-discriminant character is such a symbol
(`primeDiscriminantCharFun_eq_legendreSym`). Multiplying the symbols back together identifies the
full genus character with the splitting symbol of `K`:

`genusCharFun s q = legendreSym q d`.

Two consequences follow. First, the quadratic splitting law reads: `q` splits in `K` exactly when
its genus character is trivial. Second — the point of the file — a split prime carries the
prescribed character values into the narrow class group: a prime `𝔮` of `𝓞 K` above a split `q`
has absolute norm `q`, so its narrow ideal class `[𝔮] ∈ Cl⁺(K)` satisfies

`χ_P([𝔮]) = primeDiscriminantCharFun P q` for every `P ∈ s`,

and the same values are taken by the `ZMod 2`-linear family on `Cl⁺(K)/Cl⁺(K)²`. This is the
mechanism by which a sign pattern prescribed at a rational prime is realized by a narrow ideal
class.

The classical account is in D. A. Cox, *Primes of the Form `x² + ny²`*, §3.B, and F. Lemmermeyer,
*Reciprocity Laws*, §2.2. The splitting law itself, the genus characters, and their descent to the
narrow class group are the preceding Tau Ceti modules; nothing is vendored here.

## Main results

* `genusCharFun_natCast_eq_legendreSym`: `genusCharFun s q = legendreSym q d` at an odd prime `q`.
* `ncard_primesOver_eq_finrank_iff_genusCharFun_eq_one`: `q` splits in `K` exactly when its genus
  character is trivial.
* `exists_forall_genusCharFunNarrowClassGroupHom_eq`: a narrow ideal class realizing the
  prime-discriminant character values of a split prime.
* `exists_forall_genusCharFunElementaryTwoQuotientFamilyLinearMap_eq`: the same values in the
  linear family on `Cl⁺(K)/Cl⁺(K)²`.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The Legendre symbol of a product is the product of the Legendre symbols. -/
private theorem prod_legendreSym {q : ℕ} [Fact q.Prime] (s : Finset ℤ) :
    ∏ P ∈ s, legendreSym q P = legendreSym q (∏ P ∈ s, P) := by
  classical
  induction s using Finset.induction with
  | empty => simp [legendreSym.at_one]
  | insert P s hP ih => rw [Finset.prod_insert hP, Finset.prod_insert hP, legendreSym.mul, ih]

/-- **A genus character evaluates at an odd prime as a Legendre symbol.** For a set `s` of prime
discriminants, `genusCharFun s q = legendreSym q (∏ P ∈ s, P)` at every odd prime `q`, since each
prime-discriminant character is the Legendre symbol of its prime discriminant. -/
theorem genusCharFun_natCast_eq_legendreSym_prod {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    genusCharFun s (q : ℤ) = legendreSym q (∏ P ∈ s, P) := by
  rw [genusCharFun_def, ← prod_legendreSym]
  exact Finset.prod_congr rfl fun P hP => primeDiscriminantCharFun_eq_legendreSym (hs P hP) hq

/-- An odd prime is coprime to `2` in `ℤ`. -/
private theorem isCoprime_natCast_two {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    IsCoprime ((q : ℤ)) 2 :=
  (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr fun h => by
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h))

/-- **The genus character of a quadratic discriminant is its splitting symbol.** For
`K = ℚ(√d)` with discriminant `D = ∏ P ∈ s, P`, the genus character indexed by the whole
factorization agrees at an odd prime `q` with `legendreSym q d`: the fundamental discriminant
differs from `d` by the square of `1` or `2`, which the symbol does not see. -/
theorem genusCharFun_natCast_eq_legendreSym {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    genusCharFun s (q : ℤ) = legendreSym q d := by
  obtain ⟨c, hc, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
  have hc0 : ((c : ℤ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rcases hc with rfl | rfl
    · exact fun h => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp (by exact_mod_cast h))
    · exact fun h =>
        hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast h))
  rw [genusCharFun_natCast_eq_legendreSym_prod hs hq, hprod, ← hcd, legendreSym.mul,
    legendreSym.sq_one' q hc0, one_mul]

/-- **The quadratic splitting law in genus-character form.** An odd prime `q` not dividing the
squarefree radicand `d` splits in `K = ℚ(√d)` exactly when the genus character of the whole
prime-discriminant factorization of `disc K` is trivial at `q`. -/
theorem ncard_primesOver_eq_finrank_iff_genusCharFun_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hqd : ¬ (q : ℤ) ∣ d) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K ↔
      genusCharFun s (q : ℤ) = 1 := by
  rw [NumberField.ncard_primesOver_quadratic_iff hmin hgen hq hqd,
    genusCharFun_natCast_eq_legendreSym hs hprod hq]

/-- **The narrow class of a split prime realizes the prescribed character values.**
Let `D = ∏ P ∈ s, P` be a prime-discriminant factorization of the discriminant of `K = ℚ(√d)`
and let `q` be an odd prime not dividing `d` with trivial genus character. Then `q` splits in
`K`, and the narrow ideal class of a prime of `𝓞 K` above `q` has, at each `P ∈ s`, exactly the
value `primeDiscriminantCharFun P q`. -/
theorem exists_forall_genusCharFunNarrowClassGroupHom_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hqd : ¬ (q : ℤ) ∣ d)
    (hgc : genusCharFun s (q : ℤ) = 1) :
    ∃ A : NumberField.NarrowClassGroup K, ∀ (P : ℤ) (hP : P ∈ s),
      ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
          (Finset.singleton_subset_iff.mpr hP) A : ℤˣ) : ℤ) =
        primeDiscriminantCharFun P (q : ℤ) := by
  -- The genus character is the splitting symbol, so `q` splits and is an ideal norm.
  obtain ⟨𝔮, _, hnorm⟩ :=
    NumberField.exists_isPrime_absNorm_eq_of_legendreSym_eq_one hmin hgen hq hqd
      ((genusCharFun_natCast_eq_legendreSym hs hprod hq) ▸ hgc)
  have h𝔮0 : 𝔮 ∈ (Ideal (𝓞 K))⁰ := by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors, hnorm]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  -- `q` is coprime to the modulus, being an odd prime that does not divide the discriminant.
  have hcopD : IsCoprime ((q : ℤ)) (∏ P ∈ s, P) := by
    refine (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr ?_
    rw [hprod, dvd_fundamentalDiscriminant_iff (isCoprime_natCast_two hq)]
    exact hqd
  refine ⟨NumberField.NarrowClassGroup.mk0 ⟨𝔮, h𝔮0⟩, fun P hP => ?_⟩
  have hcop : IsCoprime ((Ideal.absNorm 𝔮 : ℤ)) (∏ P' ∈ ({P} : Finset ℤ), P') := by
    rw [Finset.prod_singleton, hnorm]
    exact IsCoprime.prod_right_iff.mp hcopD P hP
  let I : genusCharFunCoprimeIdealSubmonoid (K := K) {P} :=
    ⟨⟨𝔮, h𝔮0⟩, (mem_genusCharFunCoprimeIdealSubmonoid_iff _).mpr hcop⟩
  -- Evaluate the descended character on this coprime representative of the class.
  rw [show (⟨𝔮, h𝔮0⟩ : (Ideal (𝓞 K))⁰) = I.1 from rfl, genusCharFunNarrowClassGroupHom_mk0,
    genusCharFunCoprimeIdealHom_apply]
  rw [show ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = 𝔮 from rfl, hnorm, genusCharFun_singleton]

/-- **The linear family on `Cl⁺(K)/Cl⁺(K)²` realizes the character values of a split prime.**
The elementary-`2` form of `exists_forall_genusCharFunNarrowClassGroupHom_eq`: the vector of
prime-discriminant characters of a split prime `q` lies in the image of the linear family of
singleton genus characters. -/
theorem exists_forall_genusCharFunElementaryTwoQuotientFamilyLinearMap_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hqd : ¬ (q : ℤ) ∣ d)
    (hgc : genusCharFun s (q : ℤ) = 1) :
    ∃ x : NumberField.NarrowClassGroup.ElementaryTwoQuotient K, ∀ P : ↥s,
      ((Additive.toMul (genusCharFunElementaryTwoQuotientFamilyLinearMap
          hs heven hprod hmin hgen hsf x P) : ℤˣ) : ℤ) =
        primeDiscriminantCharFun (P : ℤ) (q : ℤ) := by
  obtain ⟨A, hA⟩ := exists_forall_genusCharFunNarrowClassGroupHom_eq
    hs heven hprod hmin hgen hsf hq hqd hgc
  refine ⟨TauCeti.elementaryTwoQuotientMk A, fun P => ?_⟩
  rw [genusCharFunElementaryTwoQuotientFamilyLinearMap_apply,
    genusCharFunElementaryTwoQuotientLinearMap_mk]
  exact hA P P.2

end TauCeti.Multiquadratic
