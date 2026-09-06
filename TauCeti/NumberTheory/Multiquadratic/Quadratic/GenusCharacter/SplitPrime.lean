/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.Quadratic.Splitting
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Ramification

/-!
# Genus characters at a split prime

Let `K = ℚ(√d)` with `d` squarefree, and let `D = ∏ P ∈ s, P` be a factorization of its
discriminant into prime discriminants. At an odd prime `q` the genus character of the whole
factorization is the splitting symbol of `K`,

`genusCharFun s q = legendreSym q d`

(`genusCharFun_natCast_eq_legendreSym`). Two consequences follow. First, the quadratic splitting
law reads: `q` splits in `K` exactly when its genus character is trivial. Second — the point of
the file — a split prime carries the prescribed character values into the narrow class group: a
prime `𝔮` of `𝓞 K` above a split `q` has absolute norm `q`, so its narrow ideal class
`[𝔮] ∈ Cl⁺(K)` satisfies

`χ_P([𝔮]) = primeDiscriminantCharFun P q` for every `P ∈ s`,

and the same values are taken by the `ZMod 2`-linear family on `Cl⁺(K)/Cl⁺(K)²`. This is the
mechanism by which a sign pattern prescribed at a rational prime is realized by a narrow ideal
class.

The classical account is in D. A. Cox, *Primes of the Form `x² + ny²`*, §3.B, and F. Lemmermeyer,
*Reciprocity Laws*, §2.2. The splitting law itself, the genus characters, and their descent to the
narrow class group are the preceding Tau Ceti modules; nothing is vendored here.

## Main results

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

/-- **The quadratic splitting law in genus-character form.** An odd prime `q` splits in
`K = ℚ(√d)` for squarefree `d` exactly when the genus character of the whole
prime-discriminant factorization of `disc K` is trivial at `q`. -/
theorem ncard_primesOver_eq_finrank_iff_genusCharFun_eq_one {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K ↔
      genusCharFun s (q : ℤ) = 1 := by
  by_cases hqd : ¬ (q : ℤ) ∣ d
  · rw [NumberField.ncard_primesOver_quadratic_iff hmin hgen hq hqd,
      genusCharFun_natCast_eq_legendreSym hs hprod hq]
  · have hodd : Odd (q : ℤ) := by
      exact_mod_cast (Fact.out : q.Prime).odd_of_ne_two hq
    have hdvd : (q : ℤ) ∣ fundamentalDiscriminant d := by
      rw [dvd_fundamentalDiscriminant_iff (Int.isCoprime_two_right.mpr hodd)]
      exact not_not.mp hqd
    have hram : q ∈ NumberField.ramifiedPrimes K :=
      (mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant hmin hgen hsf Fact.out).mpr hdvd
    have hfinrank : Module.finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
    have hcard := NumberField.ncard_primesOver_eq_one_of_mem_ramifiedPrimes hfinrank hram
    have hleg : legendreSym q d = 0 :=
      (legendreSym.eq_zero_iff q d).mpr
        ((ZMod.intCast_zmod_eq_zero_iff_dvd d q).mpr (not_not.mp hqd))
    rw [hcard, hfinrank, genusCharFun_natCast_eq_legendreSym hs hprod hq, hleg]
    norm_num

/-- **The narrow class of a split prime realizes the prescribed character values.**
Let `D = ∏ P ∈ s, P` be a prime-discriminant factorization of the discriminant of `K = ℚ(√d)`
and let `q` be an odd prime with trivial genus character. Then `q` splits in `K`, and the narrow
ideal class of a prime of `𝓞 K` above `q` has, at each `P ∈ s`, exactly the value
`primeDiscriminantCharFun P q`. -/
theorem exists_forall_genusCharFunNarrowClassGroupHom_eq {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (hgc : genusCharFun s (q : ℤ) = 1) :
    ∃ A : NumberField.NarrowClassGroup K, ∀ (P : ℤ) (hP : P ∈ s),
      ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
          (Finset.singleton_subset_iff.mpr hP) A : ℤˣ) : ℤ) =
        primeDiscriminantCharFun P (q : ℤ) := by
  -- The genus character is the splitting symbol, so `q` splits and is an ideal norm.
  have hleg : legendreSym q d = 1 := (genusCharFun_natCast_eq_legendreSym hs hprod hq) ▸ hgc
  obtain ⟨𝔮, _, _, hnorm⟩ :=
    NumberField.exists_isPrime_and_absNorm_eq_of_legendreSym_eq_one hmin hgen hq hleg
  have h𝔮0 : 𝔮 ∈ (Ideal (𝓞 K))⁰ := by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors, hnorm]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  -- `q` is coprime to the modulus, being an odd prime that does not divide the discriminant.
  have hqd : ¬ (q : ℤ) ∣ d := by
    intro hdvd
    rw [(legendreSym.eq_zero_iff q d).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd d q).mpr hdvd)]
      at hleg
    exact zero_ne_one hleg
  have hodd : Odd ((q : ℤ)) := by
    exact_mod_cast (Fact.out : q.Prime).odd_of_ne_two hq
  have hcopD : IsCoprime ((q : ℤ)) (∏ P ∈ s, P) := by
    refine (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr ?_
    rw [hprod, dvd_fundamentalDiscriminant_iff (Int.isCoprime_two_right.mpr hodd)]
    exact hqd
  refine ⟨NumberField.NarrowClassGroup.mk0 ⟨𝔮, h𝔮0⟩, fun P hP => ?_⟩
  have hcop : IsCoprime ((Ideal.absNorm 𝔮 : ℤ)) (∏ P' ∈ ({P} : Finset ℤ), P') := by
    rw [Finset.prod_singleton, hnorm]
    exact IsCoprime.prod_right_iff.mp hcopD P hP
  -- Evaluate the descended character on an arbitrary coprime ideal, then feed `𝔮` in: the
  -- coprime-ideal submonoid is a subtype of `(Ideal (𝓞 K))⁰`, so `𝔮` enters as the two nested
  -- projections of the element built from `hcop`.
  have key : ∀ I : genusCharFunCoprimeIdealSubmonoid (K := K) {P},
      ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
          (Finset.singleton_subset_iff.mpr hP)
          (NumberField.NarrowClassGroup.mk0 I.1) : ℤˣ) : ℤ) =
        primeDiscriminantCharFun P
          (Ideal.absNorm ((I.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℤ) := fun I => by
    rw [genusCharFunNarrowClassGroupHom_mk0, genusCharFunCoprimeIdealHom_apply,
      genusCharFun_singleton]
  rw [← hnorm]
  exact key ⟨⟨𝔮, h𝔮0⟩, (mem_genusCharFunCoprimeIdealSubmonoid_iff _).mpr hcop⟩

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
    (hsf : Squarefree d) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (hgc : genusCharFun s (q : ℤ) = 1) :
    ∃ x : NumberField.NarrowClassGroup.ElementaryTwoQuotient K, ∀ P : ↥s,
      ((Additive.toMul (genusCharFunElementaryTwoQuotientFamilyLinearMap
          hs heven hprod hmin hgen hsf x P) : ℤˣ) : ℤ) =
        primeDiscriminantCharFun (P : ℤ) (q : ℤ) := by
  obtain ⟨A, hA⟩ := exists_forall_genusCharFunNarrowClassGroupHom_eq
    hs heven hprod hmin hgen hsf hq hgc
  refine ⟨TauCeti.elementaryTwoQuotientMk A, fun P => ?_⟩
  rw [genusCharFunElementaryTwoQuotientFamilyLinearMap_apply,
    genusCharFunElementaryTwoQuotientLinearMap_mk]
  exact hA P P.2

end TauCeti.Multiquadratic
