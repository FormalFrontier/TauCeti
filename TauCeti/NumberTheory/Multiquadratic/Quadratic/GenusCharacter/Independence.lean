/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.SplitPrime
import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Dirichlet

/-!
# Independence of the genus characters of a quadratic field

Let `K = ℚ(√d)` with `d` squarefree, and let `D = P₁ ⋯ P_t` be the prime-discriminant
factorization of its fundamental discriminant. The genus characters `χ_{P_i}` are characters of the
narrow class group `Cl⁺(K)` (`genusCharFunNarrowClassGroupHom`), and their product over all `i` is
trivial on every class. This file proves that this is the **only** relation among them: every
assignment of signs `ε_i = ±1` with `∏ ε_i = 1` is the vector of values `(χ_{P_i}(A))_i` at some
narrow class `A`. In other words the map `Cl⁺(K) → {±1}^t` they define hits the whole
product-one hyperplane, which has `2^(t-1)` elements.

This is the lower bound half of the genus-theoretic `2`-rank formula for the narrow class group,
`rank₂ Cl⁺(K) ≥ t - 1`; the matching upper bound is
`TauCeti.Multiquadratic.narrowTwoRank_le_ncard_ramifiedPrimes_sub_one`. See D. A. Cox, *Primes of
the Form x² + ny²*, §3.B and §6.A, and F. Lemmermeyer, *Reciprocity Laws: From Euler to
Eisenstein*, §2.2.

## Main results

* `TauCeti.Multiquadratic.exists_forall_genusCharFunNarrowClassGroupHom_singleton_eq`: every sign
  pattern of product `1` on the prime discriminants of `D` is the value vector of the singleton
  genus characters at some narrow class.
* `TauCeti.Multiquadratic.exists_forall_genusCharFunNarrowClassGroupHom_subset_eq`: the same class
  has the prescribed product of signs as the value of every subset-indexed genus character.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Every sign pattern of product one is attained by a narrow class.** Let `K = ℚ(√d)` with `d`
squarefree, let `∏ P ∈ s, P = fundamentalDiscriminant d` be the prime-discriminant factorization,
and let `ε` assign a sign to each `P ∈ s` with `∏ P ∈ s, ε P = 1`. Then some narrow class `A` has
`χ_P(A) = ε P` for every `P ∈ s`. -/
theorem exists_forall_genusCharFunNarrowClassGroupHom_singleton_eq
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (ε : ℤ → ℤˣ) (hε : ∏ P ∈ s, ε P = 1) :
    ∃ A : NarrowClassGroup K, ∀ P (hP : P ∈ s),
      genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr hP) A = ε P := by
  obtain ⟨q, -, hq, hq2, hqε⟩ :=
    exists_prime_gt_forall_primeDiscriminantCharFun_eq hs heven ε 0
  have : Fact q.Prime := ⟨hq⟩
  have hgc : genusCharFun s (q : ℤ) = 1 := by
    rw [genusCharFun_def, Finset.prod_congr rfl fun P hP => hqε P hP, ← Units.coe_prod, hε,
      Units.val_one]
  obtain ⟨A, hA⟩ :=
    exists_forall_genusCharFunNarrowClassGroupHom_eq hs heven hprod hmin hgen hsf hq2 hgc
  refine ⟨A, fun P hP => Units.ext ?_⟩
  rw [hA P hP, hqε P hP]

/-- **Every sign pattern of product one is attained, on all subset characters at once.** Under the
hypotheses of `exists_forall_genusCharFunNarrowClassGroupHom_singleton_eq`, some narrow class `A`
has `χ_t(A) = ∏ P ∈ t, ε P` for every subset `t ⊆ s` simultaneously. -/
theorem exists_forall_genusCharFunNarrowClassGroupHom_subset_eq
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (ε : ℤ → ℤˣ) (hε : ∏ P ∈ s, ε P = 1) :
    ∃ A : NarrowClassGroup K, ∀ t (hts : t ⊆ s),
      genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts A = ∏ P ∈ t, ε P := by
  obtain ⟨A, hA⟩ :=
    exists_forall_genusCharFunNarrowClassGroupHom_singleton_eq hs heven hprod hmin hgen hsf ε hε
  refine ⟨A, fun t hts => ?_⟩
  rw [genusCharFunNarrowClassGroupHom_eq_prod_singleton hs heven hprod hmin hgen hsf hts,
    MonoidHom.finsetProd_apply, ← Finset.prod_coe_sort t]
  exact Finset.prod_congr rfl fun P _ => hA P (hts P.2)

end TauCeti.Multiquadratic
