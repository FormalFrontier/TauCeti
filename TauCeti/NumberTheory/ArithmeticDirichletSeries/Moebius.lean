/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
-- Non-public: the alternating sum over a powerset,
-- `Finset.sum_powerset_neg_one_pow_card_of_nonempty`, is used only inside the proof of the
-- divisor-sum identity, so downstream importers do not pay for it.
import Mathlib.Data.Nat.Choose.Sum

/-!
# The ideal Möbius function and Möbius inversion

The Möbius function of a nonzero ideal `A` of the ring of integers of a number field `K` is
`(-1) ^ k` when `A` is a product of `k` distinct prime ideals and `0` otherwise. This file packages
it as a `TauCeti.IdealArithmeticFunction K`, computes it on prime powers, and proves that it is the
inverse of the everywhere-one function for the ideal Dirichlet convolution. That inverse relation is
the ideal Möbius inversion formula, stated here as an equivalence between the two directions.

## Main definitions

* `TauCeti.IdealArithmeticFunction.moebius` is the ideal Möbius function, the complex-valued
  restriction of Mathlib's `UniqueFactorizationMonoid.moebius` to the nonzero ideals of `𝓞 K`.

## Main results

* `TauCeti.Ideal.sum_moebius_divisorsAntidiagonal_of_ne_one`: the Möbius function sums to zero over
  the factorizations of a nonzero ideal other than the unit ideal. This is the combinatorial heart
  of the file.
* `TauCeti.IdealArithmeticFunction.convolution_moebius_one` and
  `TauCeti.IdealArithmeticFunction.convolution_one_moebius`: the ideal Möbius function is a
  two-sided inverse of the everywhere-one function for ideal convolution.
* `TauCeti.IdealArithmeticFunction.convolution_one_eq_iff`: **ideal Möbius inversion**, the
  equivalence between `convolution f 1 = g` and `f = convolution g moebius`.
* `TauCeti.IdealArithmeticFunction.moebius_apply_prime`,
  `TauCeti.IdealArithmeticFunction.moebius_apply_prime_pow`, and
  `TauCeti.IdealArithmeticFunction.moebius_mul_of_isRelPrime`: the prime-power values and
  multiplicativity on coprime ideals.
* `TauCeti.IdealArithmeticFunction.not_exists_multiplicativeIdealWeight_eq_moebius` and
  `TauCeti.IdealArithmeticFunction.not_exists_unitaryIdealWeight_eq_moebius`: the **rejection
  tests**. The ideal Möbius function underlies neither ideal-weight carrier, because those carriers
  are completely multiplicative while `μ (𝔭 ^ 2) = 0`.

## Implementation notes

Mathlib's `UniqueFactorizationMonoid.moebius` already supplies the definition, the squarefree and
prime values, and multiplicativity on relatively prime elements for an arbitrary unique
factorization monoid, so `TauCeti.IdealArithmeticFunction.moebius` is its complex-valued
restriction rather than a fresh definition. What Mathlib does not supply — and what this file
proves — is the divisor-sum identity, since the divisor sum needs a finite index set, and for
ideals that is `TauCeti.Ideal.divisorsAntidiagonal`.

The divisor sum is proved over `ℤ` and then cast, so that it can consume Mathlib's
`Finset.sum_powerset_neg_one_pow_card_of_nonempty` directly. The proof reindexes the squarefree
factorizations of `A` by the subsets of the finite set of prime ideals dividing `A`: a squarefree
divisor is the product of the subset of primes it is divisible by, and the Möbius function of that
divisor is `(-1)` to the size of the subset. The alternating sum over a nonempty powerset vanishes.

The ideal Möbius function is *not* completely multiplicative, so it is not a
`TauCeti.MultiplicativeIdealWeight`; the two rejection theorems record this rather than leaving it
to the reader, following
`TauCeti.MultiplicativeIdealWeight.not_exists_toIdealArithmeticFunction_eq_one`.

## Roadmap role

This is Layer **2.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, built on the Layer
**2.1** convolution of `TauCeti/NumberTheory/ArithmeticDirichletSeries/Convolution.lean`. Its
consumers are the von Mangoldt transform of Layer 2.3 and the local factors of Layer 3.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open NumberField IsDedekindDomain
open UniqueFactorizationMonoid (normalizedFactors prod_normalizedFactors
  normalizedFactors_eq_zero_iff dvd_iff_normalizedFactors_le_normalizedFactors
  normalizedFactors_prod_eq_self_of_subset prod_ne_zero_of_subset_normalizedFactors
  factors_eq_normalizedFactors squarefree_iff_nodup_normalizedFactors)
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

/-! ### The ideal Möbius function -/

/-- The **ideal Möbius function** of a number field `K`: the value at a nonzero ideal `A` is
`(-1) ^ k` when `A` is a product of `k` distinct prime ideals, and `0` when `A` is divisible by the
square of a prime ideal.

It is the complex-valued restriction of Mathlib's `UniqueFactorizationMonoid.moebius` for the unique
factorization monoid `Ideal (𝓞 K)`. -/
noncomputable def moebius : IdealArithmeticFunction K :=
  fun A ↦ (UniqueFactorizationMonoid.moebius (A : Ideal (𝓞 K)) : ℂ)

theorem moebius_apply (A : (Ideal (𝓞 K))⁰) :
    (moebius : IdealArithmeticFunction K) A =
      (UniqueFactorizationMonoid.moebius (A : Ideal (𝓞 K)) : ℂ) := (rfl)

@[simp]
theorem moebius_one : (moebius : IdealArithmeticFunction K) 1 = 1 := by
  rw [moebius_apply, Submonoid.coe_one, UniqueFactorizationMonoid.moebius_one, Int.cast_one]

/-- The Möbius function vanishes at an ideal divisible by the square of a prime. -/
@[simp]
theorem moebius_of_not_squarefree {A : (Ideal (𝓞 K))⁰} (hA : ¬ Squarefree (A : Ideal (𝓞 K))) :
    (moebius : IdealArithmeticFunction K) A = 0 := by
  simp [moebius_apply, UniqueFactorizationMonoid.moebius_of_not_squarefree hA]

/-- At a squarefree ideal the Möbius function is `(-1)` to the number of prime factors. -/
theorem moebius_apply_of_squarefree {A : (Ideal (𝓞 K))⁰} (hA : Squarefree (A : Ideal (𝓞 K))) :
    (moebius : IdealArithmeticFunction K) A =
      (-1) ^ Multiset.card (normalizedFactors (A : Ideal (𝓞 K))) := by
  rw [moebius_apply, hA.moebius_eq, factors_eq_normalizedFactors]
  push_cast
  ring

/-- The Möbius function of a prime ideal is `-1`. -/
theorem moebius_apply_prime {A : (Ideal (𝓞 K))⁰} (hA : Prime (A : Ideal (𝓞 K))) :
    (moebius : IdealArithmeticFunction K) A = -1 := by
  rw [moebius_apply, hA.irreducible.moebius_eq]
  norm_num

/-- The Möbius function vanishes at a power with exponent at least two of any ideal that is not the
unit ideal, since that power is then divisible by a square. -/
theorem moebius_apply_pow_of_not_isUnit {A : (Ideal (𝓞 K))⁰} (hA : ¬ IsUnit (A : Ideal (𝓞 K)))
    {n : ℕ} (hn : 2 ≤ n) : (moebius : IdealArithmeticFunction K) (A ^ n) = 0 := by
  refine moebius_of_not_squarefree fun hsq ↦ hA ?_
  refine hsq (A : Ideal (𝓞 K)) ?_
  rw [SubmonoidClass.coe_pow, ← sq]
  exact pow_dvd_pow _ hn

/-- The Möbius function vanishes at a prime power with exponent at least two. -/
theorem moebius_apply_prime_pow {A : (Ideal (𝓞 K))⁰} (hA : Prime (A : Ideal (𝓞 K))) {n : ℕ}
    (hn : 2 ≤ n) : (moebius : IdealArithmeticFunction K) (A ^ n) = 0 :=
  moebius_apply_pow_of_not_isUnit hA.not_isUnit hn

/-- The Möbius function is multiplicative on coprime ideals. Together with
`TauCeti.IdealArithmeticFunction.moebius_apply_prime_pow` this is the precise sense in which it is
multiplicative: it is *not* completely multiplicative. -/
theorem moebius_mul_of_isRelPrime {A B : (Ideal (𝓞 K))⁰}
    (h : IsRelPrime (A : Ideal (𝓞 K)) (B : Ideal (𝓞 K))) :
    (moebius : IdealArithmeticFunction K) (A * B) = moebius A * moebius B := by
  rw [moebius_apply, moebius_apply, moebius_apply, Submonoid.coe_mul, h.moebius_mul]
  push_cast
  ring

end IdealArithmeticFunction

/-! ### The divisor sum of the Möbius function -/

namespace Ideal

/-- **The Möbius function sums to zero over the factorizations of a nonzero ideal that is not the
unit ideal.**

The squarefree first entries of the antidiagonal are exactly the products of subsets of the finite
set `P` of prime ideals dividing `A`, and the Möbius function of such a product is `(-1)` to the
size of the subset; the alternating sum over the powerset of a nonempty `P` vanishes. The entries
that are not squarefree contribute nothing. -/
theorem sum_moebius_divisorsAntidiagonal_of_ne_one {A : (Ideal (𝓞 K))⁰} (hA : A ≠ 1) :
    ∑ p ∈ divisorsAntidiagonal A,
      UniqueFactorizationMonoid.moebius ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = 0 := by
  classical
  have hA0 : (A : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero A
  set P : Finset (Ideal (𝓞 K)) := (normalizedFactors (A : Ideal (𝓞 K))).toFinset with hPdef
  -- `A` is not the unit ideal, so it has at least one prime factor.
  have hPne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, hPdef, Ne, Multiset.toFinset_eq_empty,
      normalizedFactors_eq_zero_iff hA0, _root_.Ideal.isUnit_iff]
    exact fun h ↦ hA (Subtype.ext (by simpa [_root_.Ideal.one_eq_top] using h))
  -- Drop the factorizations whose first entry is not squarefree.
  rw [← Finset.sum_filter_of_ne
    (p := fun p : (Ideal (𝓞 K))⁰ × (Ideal (𝓞 K))⁰ ↦ Squarefree ((p.1 : Ideal (𝓞 K))))
    (fun p _ hp ↦ by
      by_contra hcon
      exact hp (UniqueFactorizationMonoid.moebius_of_not_squarefree hcon))]
  -- Reindex the surviving factorizations by the subsets of `P`.
  have hreindex : ∑ p ∈ {p ∈ divisorsAntidiagonal A | Squarefree ((p.1 : Ideal (𝓞 K)))},
      UniqueFactorizationMonoid.moebius ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
      ∑ S ∈ P.powerset, (-1 : ℤ) ^ S.card := by
    refine Finset.sum_nbij (fun p ↦ (normalizedFactors ((p.1 : Ideal (𝓞 K)))).toFinset) ?_ ?_ ?_ ?_
    · -- The primes dividing a divisor of `A` divide `A`.
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp0 : ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero p.1
      refine Finset.mem_powerset.mpr ?_
      rw [hPdef]
      exact Multiset.toFinset_subset.mpr (Multiset.subset_of_le
        ((dvd_iff_normalizedFactors_le_normalizedFactors hp0 hA0).mp
          (fst_dvd_of_mem_divisorsAntidiagonal hp.1)))
    · -- A squarefree ideal is determined by the set of primes dividing it, and the first entry of a
      -- factorization determines the second.
      intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have hp0 : ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero p.1
      have hq0 : ((q.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero q.1
      have hpq' : (normalizedFactors ((p.1 : Ideal (𝓞 K)))).toFinset =
          (normalizedFactors ((q.1 : Ideal (𝓞 K)))).toFinset := hpq
      have hfac : normalizedFactors ((p.1 : Ideal (𝓞 K))) =
          normalizedFactors ((q.1 : Ideal (𝓞 K))) := by
        rw [← ((squarefree_iff_nodup_normalizedFactors hp0).mp hp.2).dedup,
          ← ((squarefree_iff_nodup_normalizedFactors hq0).mp hq.2).dedup,
          ← Multiset.toFinset_val, ← Multiset.toFinset_val, hpq']
      have hassoc : Associated ((p.1 : Ideal (𝓞 K))) ((q.1 : Ideal (𝓞 K))) := by
        have h := (prod_normalizedFactors hp0).symm
        rw [hfac] at h
        exact h.trans (prod_normalizedFactors hq0)
      have h1 : p.1 = q.1 := Subtype.ext (associated_iff_eq.mp hassoc)
      have h2 : p.2 = q.2 := by
        refine mul_left_cancel (a := p.1) ?_
        rw [mem_divisorsAntidiagonal.mp hp.1, ← mem_divisorsAntidiagonal.mp hq.1, h1]
      exact Prod.ext h1 h2
    · -- Every subset of `P` arises: its product is a squarefree divisor of `A`.
      intro S hS
      rw [Finset.mem_coe, Finset.mem_powerset] at hS
      have hsub : (S.val : Multiset (Ideal (𝓞 K))) ⊆ normalizedFactors (A : Ideal (𝓞 K)) :=
        fun _ hx ↦ Multiset.mem_toFinset.mp (hS (Finset.mem_val.mp hx))
      have hB0 : S.val.prod ≠ 0 := prod_ne_zero_of_subset_normalizedFactors hsub
      have hBfac : normalizedFactors S.val.prod = S.val :=
        normalizedFactors_prod_eq_self_of_subset hsub
      obtain ⟨C, hC⟩ : S.val.prod ∣ (A : Ideal (𝓞 K)) :=
        (Multiset.prod_dvd_prod_of_le ((Multiset.le_iff_subset S.nodup).mpr hsub)).trans
          (prod_normalizedFactors hA0).dvd
      have hC0 : C ≠ 0 := by
        rintro rfl
        exact hA0 (by rw [hC, mul_zero])
      refine ⟨(⟨S.val.prod, mem_nonZeroDivisors_of_ne_zero hB0⟩,
        ⟨C, mem_nonZeroDivisors_of_ne_zero hC0⟩), ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨mem_divisorsAntidiagonal.mpr (Subtype.ext (by simpa using hC.symm)), ?_⟩
        exact (squarefree_iff_nodup_normalizedFactors hB0).mpr (by rw [hBfac]; exact S.nodup)
      · have hval : (normalizedFactors S.val.prod).toFinset = S := by
          rw [hBfac, Finset.val_toFinset]
        exact hval
    · -- The Möbius function of a squarefree ideal is `(-1)` to the number of primes dividing it.
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp0 : ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero p.1
      rw [hp.2.moebius_eq, factors_eq_normalizedFactors,
        Multiset.toFinset_card_of_nodup ((squarefree_iff_nodup_normalizedFactors hp0).mp hp.2)]
  rw [hreindex]
  exact Finset.sum_powerset_neg_one_pow_card_of_nonempty hPne

end Ideal

namespace IdealArithmeticFunction

/-! ### Möbius inversion -/

/-- The ideal Möbius function is a left inverse of the everywhere-one function for ideal
convolution. -/
@[simp]
theorem convolution_moebius_one :
    convolution (moebius : IdealArithmeticFunction K) 1 = delta := by
  ext A
  rcases eq_or_ne A 1 with rfl | hA
  · simp
  rw [delta_of_ne_one hA, convolution_apply]
  calc ∑ p ∈ Ideal.divisorsAntidiagonal A,
        (moebius : IdealArithmeticFunction K) p.1 * (1 : IdealArithmeticFunction K) p.2
      = ((∑ p ∈ Ideal.divisorsAntidiagonal A,
          UniqueFactorizationMonoid.moebius ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℤ) : ℂ) := by
        rw [Int.cast_sum]
        exact Finset.sum_congr rfl fun p _ ↦ by rw [Pi.one_apply, mul_one, moebius_apply]
    _ = 0 := by
        rw [Ideal.sum_moebius_divisorsAntidiagonal_of_ne_one hA, Int.cast_zero]

/-- The ideal Möbius function is a right inverse of the everywhere-one function for ideal
convolution. -/
@[simp]
theorem convolution_one_moebius :
    convolution (1 : IdealArithmeticFunction K) moebius = delta := by
  rw [convolution_comm, convolution_moebius_one]

/-- **Ideal Möbius inversion.** Summing an ideal arithmetic function over the divisors of an ideal
is inverted by convolving with the ideal Möbius function. -/
theorem convolution_one_eq_iff {f g : IdealArithmeticFunction K} :
    convolution f 1 = g ↔ f = convolution g moebius := by
  constructor
  · rintro rfl
    rw [convolution_assoc, convolution_one_moebius, convolution_delta]
  · rintro rfl
    rw [convolution_assoc, convolution_moebius_one, convolution_delta]

/-- Regrouping by absolute norm sends the ideal Möbius inversion identity to the corresponding
identity for Mathlib's Dirichlet convolution of arithmetic functions. -/
theorem normCoeff_moebius_mul_normCoeff_one :
    normCoeff K (moebius : IdealArithmeticFunction K) * normCoeff K 1 = 1 := by
  rw [← normCoeff_convolution, convolution_moebius_one, normCoeff_delta]

/-! ### The Möbius function is not an ideal weight -/

/-- **Rejection test.** The ideal Möbius function underlies no multiplicative ideal weight: such a
weight is completely multiplicative, so it takes the value `1` at the square of a prime at which it
takes the value `-1`, whereas the Möbius function vanishes there. -/
theorem not_exists_multiplicativeIdealWeight_eq_moebius :
    ¬ ∃ χ : MultiplicativeIdealWeight K,
      χ.toIdealArithmeticFunction = (moebius : IdealArithmeticFunction K) := by
  rintro ⟨χ, hχ⟩
  obtain ⟨P, hPbot, hPmax⟩ :=
    Ring.exists_maximal_of_not_isField (NumberField.RingOfIntegers.not_isField K)
  set 𝔭 : (Ideal (𝓞 K))⁰ := ⟨P, mem_nonZeroDivisors_of_ne_zero hPbot⟩
  have hprime : Prime ((𝔭 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) :=
    _root_.Ideal.prime_of_isPrime hPbot hPmax.isPrime
  have h1 : χ P = -1 := by
    have := congrFun hχ 𝔭
    rwa [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, moebius_apply_prime hprime]
      at this
  have h2 : χ (P ^ 2) = 0 := by
    have := congrFun hχ (𝔭 ^ 2)
    rwa [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
      moebius_apply_prime_pow hprime le_rfl, SubmonoidClass.coe_pow] at this
  rw [map_pow, h1] at h2
  norm_num at h2

/-- **Rejection test.** The ideal Möbius function underlies no unitary ideal weight either, since a
unitary weight is in particular a multiplicative one. -/
theorem not_exists_unitaryIdealWeight_eq_moebius :
    ¬ ∃ χ : UnitaryIdealWeight K,
      χ.toIdealArithmeticFunction = (moebius : IdealArithmeticFunction K) := by
  rintro ⟨χ, hχ⟩
  refine not_exists_multiplicativeIdealWeight_eq_moebius ⟨χ.1, ?_⟩
  ext I
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, ← hχ,
    UnitaryIdealWeight.toIdealArithmeticFunction_apply]

end IdealArithmeticFunction

end TauCeti
