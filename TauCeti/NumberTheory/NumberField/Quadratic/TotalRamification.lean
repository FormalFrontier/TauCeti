/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes

/-!
# A ramified prime of a quadratic field is totally ramified

Let `K` be a number field of degree `2` over `ℚ` and let `p` be a rational prime that ramifies
in `K`. This file proves the classical description of that ramification: there is exactly one
prime `𝔭` of `𝓞 K` above `p`, it has ramification index `2` and inertia degree `1`, and

`p 𝓞 K = 𝔭 ^ 2`.

The argument is the fundamental identity `∑_{𝔭 ∣ p} e(𝔭) f(𝔭) = [K : ℚ]`
(`Ideal.sum_ramification_inertia_eq_finrank`) with the right-hand side equal to `2`: every
summand is at least `1`, so a single summand with `e ≥ 2` exhausts the sum, forcing `e = 2`,
`f = 1` and no further primes above `p`. Turning the resulting `e = 2` into the ideal identity
`p 𝓞 K = 𝔭 ^ 2` is the Dedekind factorization
`IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`: all the normalized factors of
`p 𝓞 K` lie over `p`, hence equal `𝔭`, and `𝔭` occurs with multiplicity `e = 2`.

Together with the splitting law of `TauCeti.NumberTheory.NumberField.Quadratic.Splitting` — which
describes the *unramified* primes of a quadratic field, and is stated only away from the primes
dividing the radicand — this completes the list of splitting types of a rational prime in a
quadratic field. It is the ramified case that genus theory needs: the `2`-rank formula for
`ℚ(√d)` rests on comparing the ramification of `p` in `ℚ(√d)` with its ramification in the genus
field, and `e(𝔭 ∣ p) = 2` is what makes the genus field unramified over `ℚ(√d)` at `p`.

## Main results

In the namespace `TauCeti.NumberField`, all for `Module.finrank ℚ K = 2`:

* `primesOver_eq_singleton_of_mem_ramifiedPrimes` and
  `ncard_primesOver_eq_one_of_mem_ramifiedPrimes`: a ramified prime has a unique prime above it.
* `ramificationIdx_eq_two_of_mem_ramifiedPrimes` and `inertiaDeg_eq_one_of_mem_ramifiedPrimes`:
  that prime has `e = 2` and `f = 1`.
* `map_span_eq_sq_of_mem_ramifiedPrimes`: `p 𝓞 K = 𝔭 ^ 2`.
* `mem_ramifiedPrimes_iff_ramificationIdx_eq_two`: conversely, `e = 2` characterises the ramified
  primes among the rational primes.
-/

public section

open Ideal Module UniqueFactorizationMonoid
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

/-- The rational prime `p`, as the ideal `span {(p : ℤ)}` of `ℤ`, is maximal. -/
private theorem isMaximal_span_natCast (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprime : (span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp hp)
  exact hprime.isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hpne)

/-- The rational prime `p`, as an ideal of `ℤ`, is nonzero. -/
private theorem span_natCast_ne_bot (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simpa [Ideal.span_singleton_eq_bot] using hpne

/-- **The fundamental identity for a quadratic field.** Over a rational prime `p`, the ramification
indices and inertia degrees of the primes of `𝓞 K` satisfy `∑ e(𝔭) f(𝔭) = 2`. -/
private theorem sum_ramificationIdx_mul_inertiaDeg_eq_two (hK : finrank ℚ K = 2)
    [(span {(p : ℤ)} : Ideal ℤ).IsMaximal] :
    ∑ q : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, NumberField.RingOfIntegers.rank K, hK]

/-- **The engine of the file.** If some prime `𝔭` of `𝓞 K` above a rational prime `p` has
ramification index different from `1`, then in the quadratic field `K` it is the only prime above
`p`, and its ramification index and inertia degree are `2` and `1`. -/
private theorem totallyRamified_aux (hK : finrank ℚ K = 2) (hp : p.Prime)
    {𝔭 : Ideal (𝓞 K)} [𝔭.IsPrime] [𝔭.LiesOver (span {(p : ℤ)})]
    (hram : 𝔭.ramificationIdx ℤ ≠ 1) :
    𝔭.ramificationIdx ℤ = 2 ∧ 𝔭.inertiaDeg ℤ = 1 ∧
      (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} := by
  classical
  have := isMaximal_span_natCast hp
  set x : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨𝔭, ‹_›, ‹_›⟩ with hx
  have hx1 : (x : Ideal (𝓞 K)) = 𝔭 := by rw [hx]
  -- `e(𝔭) ≥ 2`, since it is positive and not `1`.
  have he : 2 ≤ 𝔭.ramificationIdx ℤ :=
    (Nat.two_le_iff _).mpr ⟨(Ideal.ramificationIdx_pos 𝔭 ℤ).ne', hram⟩
  have hf0 : 1 ≤ 𝔭.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔭 ℤ
  -- Every summand of the fundamental identity is at least `1`.
  have hone : ∀ q : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hlo⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos q ℤ).ne' (Ideal.inertiaDeg_pos q ℤ).ne')
  -- The summand at `𝔭` is at least `2`, since `e(𝔭) ≥ 2` and `f(𝔭) ≥ 1`.
  have htwo : 2 ≤ 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ :=
    le_trans (by omega) (Nat.mul_le_mul he hf0)
  have hsum := sum_ramificationIdx_mul_inertiaDeg_eq_two (K := K) (p := p) hK
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx1] at hsum
  -- The summand at `𝔭` already accounts for the whole sum, so the remaining ones vanish.
  have hrest : ∑ q ∈ Finset.univ.erase x, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 0 := by omega
  have hxval : 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ = 2 := by omega
  -- With `e(𝔭) ≥ 2` this pins down `f(𝔭) = 1` and then `e(𝔭) = 2`.
  have hfone : 𝔭.inertiaDeg ℤ = 1 := by
    have hle : 2 * 𝔭.inertiaDeg ℤ ≤ 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ :=
      Nat.mul_le_mul he le_rfl
    omega
  have heone : 𝔭.ramificationIdx ℤ = 2 := by rw [hfone, mul_one] at hxval; exact hxval
  -- A vanishing sum of positive terms has no terms, so `𝔭` is the only prime above `p`.
  have huniq : ∀ q : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), q = x := by
    intro q
    by_contra hne
    have hmemq : q ∈ Finset.univ.erase x := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ q⟩
    exact absurd ((Finset.sum_eq_zero_iff.mp hrest) q hmemq)
      (Nat.one_le_iff_ne_zero.mp (hone q))
  refine ⟨heone, hfone, ?_⟩
  ext q
  refine ⟨fun hq => ?_, ?_⟩
  · have := congrArg Subtype.val (huniq ⟨q, hq.1, hq.2⟩)
    rw [hx1] at this
    exact this
  · rintro rfl
    exact ⟨‹_›, ‹_›⟩

/-- A ramified rational prime admits a prime of `𝓞 K` above it with ramification index `≠ 1`. -/
private theorem exists_ramificationIdx_ne_one (hmem : p ∈ ramifiedPrimes K) :
    ∃ 𝔮 : Ideal (𝓞 K), ∃ _ : 𝔮.IsPrime, 𝔮.LiesOver (span {(p : ℤ)}) ∧
      𝔮.ramificationIdx ℤ ≠ 1 := by
  by_contra hcon
  refine (mem_ramifiedPrimes_iff.mp hmem).2 ?_
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro 𝔮 h𝔮 hlo
  by_contra hne
  exact hcon ⟨𝔮, h𝔮, hlo, hne⟩

variable (hK : finrank ℚ K = 2) (hp : p.Prime) (hmem : p ∈ ramifiedPrimes K)
  (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [𝔭.LiesOver (span {(p : ℤ)})]

include hK hp hmem

/-- The ramified case of the quadratic splitting law, for the prime `𝔭` named by the caller. -/
private theorem totallyRamified_of_mem_ramifiedPrimes :
    𝔭.ramificationIdx ℤ = 2 ∧ 𝔭.inertiaDeg ℤ = 1 ∧
      (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} := by
  obtain ⟨𝔮, h𝔮, hlo, hne⟩ := exists_ramificationIdx_ne_one hmem
  have := h𝔮
  have := hlo
  obtain ⟨he, hf, hset⟩ := totallyRamified_aux hK hp hne
  have h𝔭mem : 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨‹_›, ‹_›⟩
  rw [hset] at h𝔭mem
  rw [Set.mem_singleton_iff] at h𝔭mem
  rw [h𝔭mem]
  exact ⟨he, hf, hset⟩

/-- **A ramified prime of a quadratic field has a unique prime above it.** If `p` ramifies in a
number field `K` of degree `2`, the primes of `𝓞 K` above `p` are the single prime `𝔭`. -/
theorem primesOver_eq_singleton_of_mem_ramifiedPrimes :
    (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} :=
  (totallyRamified_of_mem_ramifiedPrimes hK hp hmem 𝔭).2.2

/-- **A ramified prime of a quadratic field has exactly one prime above it.** The count form of
`primesOver_eq_singleton_of_mem_ramifiedPrimes`: in the notation of the fundamental identity,
`g = 1`. -/
theorem ncard_primesOver_eq_one_of_mem_ramifiedPrimes :
    ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = 1 := by
  obtain ⟨𝔮, h𝔮, hlo, hne⟩ := exists_ramificationIdx_ne_one hmem
  have := h𝔮
  have := hlo
  rw [(totallyRamified_aux hK hp hne).2.2, Set.ncard_singleton]

/-- **A ramified prime of a quadratic field is totally ramified.** The prime `𝔭` above a ramified
rational prime `p` has ramification index `e(𝔭 ∣ p) = 2`. -/
theorem ramificationIdx_eq_two_of_mem_ramifiedPrimes : 𝔭.ramificationIdx ℤ = 2 :=
  (totallyRamified_of_mem_ramifiedPrimes hK hp hmem 𝔭).1

/-- **The residue field does not grow at a ramified prime of a quadratic field.** The prime `𝔭`
above a ramified rational prime `p` has inertia degree `f(𝔭 ∣ p) = 1`. -/
theorem inertiaDeg_eq_one_of_mem_ramifiedPrimes : 𝔭.inertiaDeg ℤ = 1 :=
  (totallyRamified_of_mem_ramifiedPrimes hK hp hmem 𝔭).2.1

/-- **`p 𝓞 K = 𝔭 ^ 2` at a ramified prime of a quadratic field.** The ideal generated by a ramified
rational prime `p` in the ring of integers of a quadratic field is the square of the unique prime
above it. -/
theorem map_span_eq_sq_of_mem_ramifiedPrimes :
    (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = 𝔭 ^ 2 := by
  classical
  set I : Ideal (𝓞 K) := (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K))
  have hP0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := span_natCast_ne_bot hp
  have hI0 : I ≠ ⊥ :=
    fun h => hP0 ((Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))).mp h)
  -- Every normalized factor of `p 𝓞 K` is a prime lying over `p`, hence equals `𝔭`.
  have hfac : ∀ q ∈ normalizedFactors I, q = 𝔭 := by
    intro q hq
    have hqprime : q.IsPrime := isPrime_of_prime (prime_of_normalized_factor q hq)
    have hle : I ≤ q := le_of_dvd (dvd_of_mem_normalizedFactors hq)
    have hcomap : q.under ℤ = span {(p : ℤ)} :=
      ((isMaximal_span_natCast hp).eq_of_le (Ideal.IsPrime.under ℤ q).ne_top
        (Ideal.map_le_iff_le_comap.mp hle)).symm
    have : q.LiesOver (span {(p : ℤ)}) := ⟨hcomap.symm⟩
    have hqmem : q ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨hqprime, ‹_›⟩
    rw [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hp hmem 𝔭, Set.mem_singleton_iff] at hqmem
    exact hqmem
  -- `𝔭` occurs in that factorization with multiplicity `e(𝔭 ∣ p) = 2`.
  have hcount : (normalizedFactors I).count 𝔭 = 2 := by
    rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (span {(p : ℤ)} : Ideal ℤ) 𝔭 hI0]
    exact ramificationIdx_eq_two_of_mem_ramifiedPrimes hK hp hmem 𝔭
  have hcard : Multiset.card (normalizedFactors I) = 2 := by
    rw [← hcount]
    exact (Multiset.count_eq_card.mpr fun q hq => (hfac q hq).symm).symm
  have hrep : normalizedFactors I = Multiset.replicate 2 𝔭 := by
    rw [← hcard]
    exact Multiset.eq_replicate_card.mpr hfac
  calc I = (normalizedFactors I).prod := (associated_iff_eq.mp (prod_normalizedFactors hI0)).symm
    _ = 𝔭 ^ 2 := by rw [hrep, Multiset.prod_replicate]

omit hmem

/-- **Ramification index `2` characterises the ramified primes of a quadratic field.** For a
rational prime `p` and a prime `𝔭` of `𝓞 K` above it, `p` ramifies in the quadratic field `K` iff
`e(𝔭 ∣ p) = 2`. -/
theorem mem_ramifiedPrimes_iff_ramificationIdx_eq_two :
    p ∈ ramifiedPrimes K ↔ 𝔭.ramificationIdx ℤ = 2 := by
  refine ⟨fun hmem => ramificationIdx_eq_two_of_mem_ramifiedPrimes hK hp hmem 𝔭, fun he => ?_⟩
  refine mem_ramifiedPrimes_iff.mpr ⟨hp, fun hunr => ?_⟩
  have := Algebra.IsUnramifiedIn.ramificationIdx_eq_one (R := ℤ) hunr (𝔓 := 𝔭) ‹_›
  omega

end TauCeti.NumberField
