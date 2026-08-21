/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.RamifiedPrime.Product
public import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The ramified primes of an imaginary quadratic field span exactly `2 ^ (t - 1)` classes

Let `K = ℚ(√d)` be an imaginary quadratic field, presented by `θ : 𝓞 K` with
`minpoly ℤ θ = X ^ 2 - d` for a squarefree `d < -1`, and let `t` be the number of rational primes
ramifying in `K`. The classes `[𝔭_p]` of the primes above the ramified primes are `2`-torsion
(`NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes`) and satisfy the relation
`∏_{p ∣ d} [𝔭_p] = 1` (`prod_classGroupMk0_eq_one`), which bounds the subgroup they generate by
`2 ^ (t - 1)` elements (`natCard_closure_image_classGroupMk0_le`). This file supplies the matching
lower bound, so that subgroup has **exactly** `2 ^ (t - 1)` elements, and reads off the
genus-theoretic lower bound `2-rank Cl(K) ≥ t - 1`.

The content is that there is no relation beyond the known one. A relation is a subset `S` of the
ramified primes with `∏_{p ∈ S} 𝔭_p` principal; taking absolute norms, a generator `z` of that
product has `|N(z)| = ∏_{p ∈ S} p`, and since `d < 0` the norm form of `K` is positive definite,
so `N(z) = ∏_{p ∈ S} p` on the nose. Writing `n = |d|`, the norm form is `(A² + n B²)/4` in
general and `A² + n B²` when `d ≢ 1 (mod 4)` (`NumberField.exists_sq_sub_mul_sq_eq_four_mul_norm`
and `NumberField.exists_sq_sub_mul_sq_eq_norm_of_mod_four_ne_one`). The product `m = ∏_{p ∈ S} p`
is a squarefree divisor of the discriminant, hence of `n` when `d ≡ 1 (mod 4)` (where `disc K = d`
is odd) and of `2n` otherwise (where `disc K = 4d`). Positive definiteness then leaves very little
room: if the `B`-coordinate vanishes, `m` is a square and so `m = 1`; if it does not, then
`m ≥ n/4` resp. `m ≥ n`, and the few surviving ratios `n/m` are excluded one by one. The upshot is
`m = 1` or `m = n`, that is, `S = ∅` or `S` is the set of prime factors of `d`.

Counting is then immediate: fix a prime factor `q` of `d`. If two subsets of the ramified primes
avoiding `q` have the same product of classes, their symmetric difference is a relation, and it
too avoids `q`; so it is not the set of prime factors of `d`, which contains `q`, leaving only the
empty relation — that is, the two subsets are equal. Distinct such subsets therefore have distinct
products of classes.

The radicand `d = -1` is genuinely excluded, not merely for convenience: there `t = 1` and the
single ramified prime `2` has the *principal* prime `(1 + i)` above it, so the relation used here
(which lives on the prime factors of `d`) is empty while the classes still collapse. The bound
`2-rank ≥ t - 1 = 0` is vacuous in that case anyway.

For the ordinary class group of a *real* quadratic field the analogous statement is false — `ℚ(√3)`
has `t = 2` and class number `1` — which is why genus theory states the `t - 1` formula for the
narrow class group there; only the imaginary case, where narrow and ordinary agree, is treated
here.

The classical source is D. A. Cox, *Primes of the Form x² + ny²*, Chapter 3, and F. Lemmermeyer,
*Reciprocity Laws*, Chapter 6, where this is the lower-bound half of the ambiguous class number
formula.

## Main results

In the namespace `TauCeti.Multiquadratic`:

* `prod_eq_one_or_prod_eq_natAbs_of_isPrincipal_prod`: a principal product of ramified primes has
  `∏_{p ∈ s} p` equal to `1` or to `|d|`.
* `eq_empty_or_eq_primeFactors_of_prod_classGroupMk0_eq_one`: the class-group form — a trivial
  product of ramified-prime classes is indexed by `∅` or by the prime factors of `d`.
* `two_pow_le_natCard_closure_image_classGroupMk0` and `natCard_closure_image_classGroupMk0_eq`:
  the classes of the ramified primes generate a subgroup of order exactly `2 ^ (t - 1)`.
* `card_sub_one_le_twoRank` and `ncard_ramifiedPrimes_sub_one_le_twoRank`: hence
  `2-rank Cl(𝓞 K) ≥ t - 1`.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors
open NumberField (ramifiedPrimes)

namespace TauCeti.Multiquadratic

/-- A squarefree integer that is a square is `1`. -/
private theorem eq_one_of_squarefree_of_eq_sq {m c : ℤ} (hmsf : Squarefree m) (h : m = c ^ 2) :
    m = 1 := by
  have hu : IsUnit c := hmsf c ⟨1, by rw [h]; ring⟩
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp [h]

/-- The `d ≡ 1 (mod 4)` branch of the ramified-prime independence computation: a positive
squarefree divisor `m` of `n > 1` with `4m` represented by the form `A² + n B²` is `1` or `n`. -/
private theorem eq_one_or_eq_of_four_mul_eq_sq_add {n m A B : ℤ} (hn : 1 < n) (hnodd : ¬ (2 ∣ n))
    (hm : 0 < m) (hmsf : Squarefree m) (hdvd : m ∣ n) (h : A ^ 2 + n * B ^ 2 = 4 * m) :
    m = 1 ∨ m = n := by
  rcases eq_or_ne B 0 with rfl | hB
  · left
    have h4 : A ^ 2 = 4 * m := by linarith [h, sq_nonneg A]
    have h2 : (2 : ℤ) ∣ A := Int.prime_two.dvd_of_dvd_pow ⟨2 * m, by rw [h4]; ring⟩
    obtain ⟨c, rfl⟩ := h2
    have hc : (4 : ℤ) * c ^ 2 = 4 * m := by linear_combination h4
    have hmc : m = c ^ 2 := by linarith
    exact eq_one_of_squarefree_of_eq_sq hmsf hmc
  · have hB1 : 1 ≤ B ^ 2 := by
      rcases lt_or_gt_of_ne hB with h' | h' <;> nlinarith
    obtain ⟨k, hk⟩ := hdvd
    have hnpos : (0 : ℤ) < n := by omega
    have hkpos : 0 < k := by
      rcases le_or_gt k 0 with h' | h'
      · nlinarith [mul_nonneg hm.le (neg_nonneg.mpr h')]
      · exact h'
    have hk4 : k ≤ 4 := by nlinarith [mul_le_mul_of_nonneg_left hB1 hnpos.le, sq_nonneg A]
    have hkodd : ¬ (2 ∣ k) := fun hdk => hnodd (hk ▸ hdk.mul_left m)
    have hk13 : k = 1 ∨ k = 3 := by omega
    rcases hk13 with rfl | rfl
    · right; omega
    · left
      have hB2 : B ^ 2 = 1 := le_antisymm (by nlinarith [sq_nonneg A]) hB1
      rw [hk, hB2] at h
      have hmA : m = A ^ 2 := by linarith
      exact eq_one_of_squarefree_of_eq_sq hmsf hmA

/-- The `d ≢ 1 (mod 4)` branch of the ramified-prime independence computation: a positive
squarefree divisor `m` of `2n` with `n > 1` squarefree and `m` represented by the form
`A² + n B²` is `1` or `n`. -/
private theorem eq_one_or_eq_of_eq_sq_add {n m A B : ℤ} (hn : 1 < n) (hnsf : Squarefree n)
    (hm : 0 < m) (hmsf : Squarefree m) (hdvd : m ∣ 2 * n) (h : A ^ 2 + n * B ^ 2 = m) :
    m = 1 ∨ m = n := by
  rcases eq_or_ne B 0 with rfl | hB
  · have hmA : m = A ^ 2 := by linarith
    exact Or.inl (eq_one_of_squarefree_of_eq_sq hmsf hmA)
  · have hB1 : 1 ≤ B ^ 2 := by
      rcases lt_or_gt_of_ne hB with h' | h' <;> nlinarith
    have hnpos : (0 : ℤ) < n := by omega
    have hmn : n ≤ m := by nlinarith [mul_le_mul_of_nonneg_left hB1 hnpos.le, sq_nonneg A]
    obtain ⟨k, hk⟩ := hdvd
    have hkpos : 0 < k := by
      rcases le_or_gt k 0 with h' | h'
      · nlinarith [mul_nonneg hm.le (neg_nonneg.mpr h')]
      · exact h'
    have hk2 : k ≤ 2 := by nlinarith
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · exfalso
      have hm2n : m = 2 * n := by omega
      have hB2le : B ^ 2 ≤ 2 := by nlinarith [sq_nonneg A]
      have hBle : B ≤ 1 := by nlinarith
      have hBge : -1 ≤ B := by nlinarith
      have hB2 : B ^ 2 = 1 := by
        have hBpm : B = -1 ∨ B = 1 := by omega
        rcases hBpm with rfl | rfl <;> norm_num
      rw [hB2, hm2n] at h
      have hnA : n = A ^ 2 := by linarith
      have := eq_one_of_squarefree_of_eq_sq hnsf hnA
      omega
    · right; omega

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The absolute norm of a product of ramified primes is the product of the rational primes below
them: each factor has residue degree one. -/
private theorem absNorm_prod_eq_prod (hfin : Module.finrank ℚ K = 2) {s : Finset ℕ}
    (P : ℕ → Ideal (𝓞 K)) (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K)
    (hprime : ∀ p ∈ s, (P p).IsPrime)
    (hover : ∀ p ∈ s, (P p).LiesOver (Ideal.span {(p : ℤ)})) :
    Ideal.absNorm (∏ p ∈ s, P p) = ∏ p ∈ s, p := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have := hprime p hp
  have := hover p hp
  exact NumberField.absNorm_eq_of_mem_ramifiedPrimes hfin (hram p hp) (P p)

/-- The product of a finite set of primes is squarefree. -/
private theorem squarefree_prod_primes {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (f := fun p => p) ?_
    fun p hp => (hprime p hp).squarefree
  intro p hp q hq hne
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hne)

/-- **The only principal products of ramified primes are the two obvious ones.** Let `K = ℚ(√d)`
be an imaginary quadratic field with `d < -1` squarefree, and let `s` be a finite set of ramified
rational primes with `P p` the prime of `𝓞 K` above `p ∈ s`. If `∏_{p ∈ s} 𝔭_p` is principal, then
`∏_{p ∈ s} p` is `1` (forcing `s = ∅`) or `|d|` (the known relation
`span_singleton_eq_prod_primeFactors`, which comes from `θ` itself).

This is the arithmetic heart of the genus-theoretic `2`-rank formula: the classes of the ramified
primes satisfy no relation beyond the one already known. The proof takes absolute norms — a
generator `z` of the product has `|N(z)| = ∏_{p ∈ s} p` — and then reads off the possibilities
from the norm form of `K`, which is positive definite because `d < 0`. Whether the `2` in the
discriminant is available as a ramified prime is exactly the `d mod 4` split: for `d ≡ 1 (mod 4)`
the norm form is `(A² + |d|B²)/4` and `∏_{p ∈ s} p` divides `|d|`, while otherwise the form is
`A² + |d|B²` and the product divides `2|d|`. -/
theorem prod_eq_one_or_prod_eq_natAbs_of_isPrincipal_prod
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) {s : Finset ℕ} (P : ℕ → Ideal (𝓞 K))
    (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K) (hprime : ∀ p ∈ s, (P p).IsPrime)
    (hover : ∀ p ∈ s, (P p).LiesOver (Ideal.span {(p : ℤ)}))
    (hprin : Submodule.IsPrincipal (∏ p ∈ s, P p)) :
    ∏ p ∈ s, p = 1 ∨ ∏ p ∈ s, p = d.natAbs := by
  classical
  have hfin : Module.finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  have hpprime : ∀ p ∈ s, p.Prime := fun p hp =>
    NumberField.prime_of_mem_ramifiedPrimes (hram p hp)
  have hn1 : (1 : ℤ) < -d := by omega
  have hnabs : (d.natAbs : ℤ) = -d := by omega
  have hnsf : Squarefree (-d) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]; exact hsf
  have hmpos : (0 : ℤ) < ((∏ p ∈ s, p : ℕ) : ℤ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (hpprime p hp).pos
  have hmsf : Squarefree ((∏ p ∈ s, p : ℕ) : ℤ) :=
    Int.squarefree_natCast.mpr (squarefree_prod_primes hpprime)
  -- A generator of the product has absolute norm `∏_{p ∈ s} p`.
  obtain ⟨z, hz⟩ := Submodule.IsPrincipal.principal (S := ∏ p ∈ s, P p) (self := hprin)
  rw [Ideal.submodule_span_eq] at hz
  have hnormz : (Algebra.norm ℤ z).natAbs = ∏ p ∈ s, p := by
    rw [← Ideal.absNorm_span_singleton z, ← hz, absNorm_prod_eq_prod hfin P hram hprime hover]
  -- The norm form is positive definite, so that norm is the product on the nose.
  obtain ⟨A₀, B₀, hAB₀⟩ := NumberField.exists_sq_sub_mul_sq_eq_four_mul_norm hmin hgen hsf z
  have hnonneg : 0 ≤ Algebra.norm ℤ z := by
    nlinarith [sq_nonneg A₀, mul_nonneg (by omega : (0 : ℤ) ≤ -d) (sq_nonneg B₀)]
  have hnormeq : Algebra.norm ℤ z = ((∏ p ∈ s, p : ℕ) : ℤ) := by
    rw [← hnormz, Int.natAbs_of_nonneg hnonneg]
  have hdvddiscr : ∀ p ∈ s, (p : ℤ) ∣ NumberField.discr K := fun p hp =>
    (NumberField.mem_ramifiedPrimes_iff_dvd_discr (hpprime p hp)).mp (hram p hp)
  have hconv : ((∏ p ∈ s, p : ℕ) : ℤ) = 1 ∨ ((∏ p ∈ s, p : ℕ) : ℤ) = -d →
      ∏ p ∈ s, p = 1 ∨ ∏ p ∈ s, p = d.natAbs := by
    rintro (h | h)
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by rw [← hnabs] at h; exact_mod_cast h)
  refine hconv ?_
  by_cases hd4 : d % 4 = 1
  · -- `disc K = d`: every ramified prime divides the odd number `d`.
    have hdisc : NumberField.discr K = d :=
      NumberField.discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4
    have hsub : s ⊆ d.natAbs.primeFactors := fun p hp => by
      have h := hdvddiscr p hp
      rw [hdisc] at h
      exact Nat.mem_primeFactors.mpr
        ⟨hpprime p hp, by simpa using Int.natAbs_dvd_natAbs.mpr h, by omega⟩
    have hmdvd : ((∏ p ∈ s, p : ℕ) : ℤ) ∣ -d := by
      rw [← hnabs]
      exact_mod_cast (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub).trans
        (Nat.prod_primeFactors_dvd _)
    exact eq_one_or_eq_of_four_mul_eq_sq_add (A := A₀) (B := B₀) hn1 (by omega) hmpos hmsf hmdvd
      (by linear_combination hAB₀ + 4 * hnormeq)
  · -- `disc K = 4d`: a ramified prime divides `2|d|`, and the norm form has no denominator.
    have hdisc : NumberField.discr K = 4 * d :=
      NumberField.discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4
    have hsub : s ⊆ (2 * d.natAbs).primeFactors := fun p hp => by
      have h := hdvddiscr p hp
      rw [hdisc] at h
      have h4 : p ∣ 4 * d.natAbs := by
        simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr h
      refine Nat.mem_primeFactors.mpr ⟨hpprime p hp, ?_, by omega⟩
      rcases ((hpprime p hp).dvd_mul).mp h4 with h' | h'
      · have hfour : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [hfour] at h'
        have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (hpprime p hp) Nat.prime_two).mp
          ((hpprime p hp).dvd_of_dvd_pow h')
        rw [hp2]
        exact ⟨d.natAbs, rfl⟩
      · exact h'.mul_left 2
    have hmdvd : ((∏ p ∈ s, p : ℕ) : ℤ) ∣ 2 * -d := by
      have hcast : ((2 * d.natAbs : ℕ) : ℤ) = 2 * -d := by push_cast [hnabs]; ring
      rw [← hcast]
      exact_mod_cast (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub).trans
        (Nat.prod_primeFactors_dvd _)
    obtain ⟨A, B, hAB⟩ :=
      NumberField.exists_sq_sub_mul_sq_eq_norm_of_mod_four_ne_one hmin hgen hsf hd4 z
    exact eq_one_or_eq_of_eq_sq_add (A := A) (B := B) hn1 hnsf hmpos hmsf hmdvd
      (by linear_combination hAB + hnormeq)

variable (Q : ℕ → (Ideal (𝓞 K))⁰)

/-- **The classes of the ramified primes satisfy only the known relation.** For `K = ℚ(√d)` with
`d < -1` squarefree and `s` a finite set of ramified rational primes, a trivial product
`∏_{p ∈ s} [𝔭_p] = 1` of their classes forces `s` to be empty or to be the whole set of prime
factors of `d` — the relation of `prod_classGroupMk0_eq_one`. -/
theorem eq_empty_or_eq_primeFactors_of_prod_classGroupMk0_eq_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) {s : Finset ℕ}
    (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K)
    (hprime : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
    (h : ∏ p ∈ s, ClassGroup.mk0 (Q p) = 1) :
    s = ∅ ∨ s = d.natAbs.primeFactors := by
  have hprin : Submodule.IsPrincipal (∏ p ∈ s, (Q p : Ideal (𝓞 K))) := by
    rwa [← map_prod, ClassGroup.mk0_eq_one_iff (∏ p ∈ s, Q p).2, Submonoid.coe_finsetProd] at h
  rcases prod_eq_one_or_prod_eq_natAbs_of_isPrincipal_prod hmin hgen hsf hd
      (fun p => (Q p : Ideal (𝓞 K))) hram hprime hover hprin with h1 | h1
  · left
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hple : p ≤ 1 := Nat.le_of_dvd one_pos (h1 ▸ Finset.dvd_prod_of_mem (fun p => p) hp)
    exact (NumberField.prime_of_mem_ramifiedPrimes (hram p hp)).one_lt.not_ge hple
  · right
    rw [← h1, Nat.primeFactors_prod
      fun p hp => NumberField.prime_of_mem_ramifiedPrimes (hram p hp)]

/-- **The ramified primes of an imaginary quadratic field span at least `2 ^ (t - 1)` classes.**
Complementing `natCard_closure_image_classGroupMk0_le`: with `s` a finite set of ramified primes
containing every prime factor of `d < -1`, the sub-products `∏_{p ∈ S} [𝔭_p]` over subsets `S` of
`s` avoiding one chosen prime factor `q` of `d` are pairwise distinct: if two of them agree, the
symmetric difference of the two index sets is a relation avoiding `q`, so it is not the set of
prime factors of `d`, and `eq_empty_or_eq_primeFactors_of_prod_classGroupMk0_eq_one` leaves only
the empty relation, forcing the two index sets to be equal. -/
theorem two_pow_le_natCard_closure_image_classGroupMk0
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) {s : Finset ℕ}
    (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K)
    (hprime : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
    (hs : d.natAbs.primeFactors ⊆ s) :
    2 ^ (s.card - 1) ≤
      Nat.card (Subgroup.closure ((fun p ↦ ClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) := by
  classical
  have hfin : Module.finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  have hsq : ∀ p ∈ s, ClassGroup.mk0 (Q p) ^ 2 = 1 := fun p hp => by
    have := hprime p hp
    have := hover p hp
    exact NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes hfin (hram p hp)
      (Q p : Ideal (𝓞 K))
  have hd1 : 1 < d.natAbs := by omega
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hd1
  have hqs : q ∈ s := hs hq
  -- Distinct subsets of `s.erase q` give distinct sub-products.
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, ClassGroup.mk0 (Q p))
      ↑(s.erase q).powerset := by
    intro S hS T hT hST
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS hT
    simp only at hST
    -- The classes of the symmetric difference multiply to `1`.
    have heq : ∏ p ∈ S \ T, ClassGroup.mk0 (Q p) = ∏ p ∈ T \ S, ClassGroup.mk0 (Q p) := by
      have hS' := Finset.prod_inter_mul_prod_sdiff S T fun p => ClassGroup.mk0 (Q p)
      have hT' := Finset.prod_inter_mul_prod_sdiff T S fun p => ClassGroup.mk0 (Q p)
      rw [Finset.inter_comm T S] at hT'
      exact mul_left_cancel (hS'.trans (hST.trans hT'.symm))
    have hUV : ∏ p ∈ S \ T ∪ T \ S, ClassGroup.mk0 (Q p) = 1 := by
      rw [Finset.prod_union disjoint_sdiff_sdiff, ← heq, ← sq, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun p hp =>
        hsq p (Finset.mem_of_mem_erase (hS (Finset.mem_sdiff.mp hp).1))
    have hsubs : S \ T ∪ T \ S ⊆ s := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact Finset.mem_of_mem_erase (hS (Finset.mem_sdiff.mp h).1)
      · exact Finset.mem_of_mem_erase (hT (Finset.mem_sdiff.mp h).1)
    have hqnot : q ∉ S \ T ∪ T \ S := by
      intro hp
      rcases Finset.mem_union.mp hp with h | h
      · exact Finset.notMem_erase q s (hS (Finset.mem_sdiff.mp h).1)
      · exact Finset.notMem_erase q s (hT (Finset.mem_sdiff.mp h).1)
    rcases eq_empty_or_eq_primeFactors_of_prod_classGroupMk0_eq_one Q hmin hgen hsf hd
        (fun p hp => hram p (hsubs hp)) (fun p hp => hprime p (hsubs hp))
        (fun p hp => hover p (hsubs hp)) hUV with hempty | hpf
    · exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hempty).1)
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.union_eq_empty.mp hempty).2)
    · exact absurd (by rw [hpf]; exact hq) hqnot
  have himg : (fun S : Finset ℕ => ∏ p ∈ S, ClassGroup.mk0 (Q p)) '' ↑(s.erase q).powerset ⊆
      (↑(Subgroup.closure ((fun p ↦ ClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) :
        Set (ClassGroup (𝓞 K))) := by
    rintro x ⟨S, hS, rfl⟩
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS
    exact Subgroup.prod_mem _ fun p hp =>
      Subgroup.subset_closure ⟨p, Finset.mem_of_mem_erase (hS hp), rfl⟩
  calc 2 ^ (s.card - 1) = ((s.erase q).powerset : Finset (Finset ℕ)).card := by
        rw [Finset.card_powerset, Finset.card_erase_of_mem hqs]
    _ = ((s.erase q).powerset : Set (Finset ℕ)).ncard := (Set.ncard_coe_finset _).symm
    _ = ((fun S : Finset ℕ => ∏ p ∈ S, ClassGroup.mk0 (Q p)) ''
          ↑(s.erase q).powerset).ncard := (Set.InjOn.ncard_image hinj).symm
    _ ≤ (↑(Subgroup.closure ((fun p ↦ ClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) :
          Set (ClassGroup (𝓞 K))).ncard := Set.ncard_le_ncard himg (Set.toFinite _)
    _ = Nat.card (Subgroup.closure ((fun p ↦ ClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) :=
        (Nat.card_coe_set_eq _).symm

/-- **The ramified primes of an imaginary quadratic field span exactly `2 ^ (t - 1)` classes.**
For `K = ℚ(√d)` with `d < -1` squarefree and `s` a finite set of ramified rational primes
containing every prime factor of `d`, the subgroup of `Cl(𝓞 K)` generated by the classes of the
primes above the members of `s` has exactly `2 ^ (#s - 1)` elements: the upper bound is
`natCard_closure_image_classGroupMk0_le`, and the lower bound is
`two_pow_le_natCard_closure_image_classGroupMk0`. -/
theorem natCard_closure_image_classGroupMk0_eq
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) {s : Finset ℕ}
    (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K)
    (hprime : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
    (hs : d.natAbs.primeFactors ⊆ s) :
    Nat.card (Subgroup.closure ((fun p ↦ ClassGroup.mk0 (Q p)) '' (↑s : Set ℕ))) =
      2 ^ (s.card - 1) :=
  le_antisymm
    (natCard_closure_image_classGroupMk0_le Q hmin hgen hsf hram hprime hover hs (by omega))
    (two_pow_le_natCard_closure_image_classGroupMk0 Q hmin hgen hsf hd hram hprime hover hs)

/-- **The genus-theoretic lower bound on the 2-rank.** For `K = ℚ(√d)` with `d < -1` squarefree
and `s` a finite set of ramified rational primes containing every prime factor of `d`, the 2-rank
of `Cl(𝓞 K)` is at least `#s - 1`: the classes of the ramified primes span a subgroup of exponent
two and order `2 ^ (#s - 1)`. -/
theorem card_sub_one_le_twoRank
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) {s : Finset ℕ}
    (hram : ∀ p ∈ s, p ∈ ramifiedPrimes K)
    (hprime : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime)
    (hover : ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}))
    (hs : d.natAbs.primeFactors ⊆ s) :
    s.card - 1 ≤ TauCeti.ClassGroup.twoRank (𝓞 K) := by
  have hfin : Module.finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  have hsq : ∀ p ∈ s, ClassGroup.mk0 (Q p) ^ 2 = 1 := fun p hp => by
    have := hprime p hp
    have := hover p hp
    exact NumberField.classGroupMk0_sq_eq_one_of_mem_ramifiedPrimes hfin (hram p hp)
      (Q p : Ideal (𝓞 K))
  rw [TauCeti.ClassGroup.twoRank_def, ← TauCeti.twoRank_def]
  refine TauCeti.le_twoRank_of_card_eq_two_pow (ClassGroup (𝓞 K)) (fun x hx => ?_)
    (natCard_closure_image_classGroupMk0_eq Q hmin hgen hsf hd hram hprime hover hs)
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hsq p hp
  | one => exact one_pow 2
  | mul a b _ _ ha hb => rw [mul_pow, ha, hb, one_mul]
  | inv a _ ha => rw [inv_pow, ha, inv_one]

/-- **The genus-theoretic lower bound `2-rank ≥ t - 1`.** For an imaginary quadratic field
`K = ℚ(√d)` with `d < -1` squarefree, the 2-rank of the class group is at least `t - 1`, where
`t = #{ramified primes}`. Together with the matching upper bound this is the 2-rank formula of
genus theory in the imaginary case; the field-theoretic counterpart, `[K_gen : K] = 2 ^ (t - 1)`,
is `finrank_candidateGenusField_over_candidateGenusFieldBase_eq_two_pow_ncard_ramifiedPrimes`. -/
theorem ncard_ramifiedPrimes_sub_one_le_twoRank
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hd : d < -1) :
    (ramifiedPrimes K).ncard - 1 ≤ TauCeti.ClassGroup.twoRank (𝓞 K) := by
  classical
  have hfinite := NumberField.finite_ramifiedPrimes (K := K)
  have hram : ∀ p ∈ hfinite.toFinset, p ∈ ramifiedPrimes K := fun p hp =>
    hfinite.mem_toFinset.mp hp
  obtain ⟨Q, hprime, hover⟩ := NumberField.exists_primeIdealFamily (K := K) hfinite.toFinset
    fun p hp => NumberField.prime_of_mem_ramifiedPrimes (hram p hp)
  have hs : d.natAbs.primeFactors ⊆ hfinite.toFinset := fun p hp =>
    hfinite.mem_toFinset.mpr (mem_ramifiedPrimes_of_mem_primeFactors hmin hgen hsf hp)
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact card_sub_one_le_twoRank Q hmin hgen hsf hd hram hprime hover hs

end TauCeti.Multiquadratic
