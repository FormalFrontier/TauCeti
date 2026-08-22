/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import Mathlib.Algebra.Algebra.Equiv

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
`p 𝓞 K = 𝔭 ^ 2` is the Dedekind factorization `Ideal.map_algebraMap_eq_finsetProd_pow`, whose
product runs over the single prime `𝔭`.

This file covers every ramified prime of a quadratic field. The splitting law of
`TauCeti.NumberTheory.NumberField.Quadratic.Splitting` covers the odd primes `p ∤ d` not dividing
the radicand; the unramified prime `2` (that is, `d ≡ 1 mod 4`, where `2` is split or inert) is
described by neither file and remains open. It is the ramified case that genus theory needs: the
`2`-rank formula for `ℚ(√d)` rests on comparing the ramification of `p` in `ℚ(√d)` with its
ramification in the genus field, and `e(𝔭 ∣ p) = 2` is what makes the genus field unramified over
`ℚ(√d)` at `p`.

## Main results

All of the following assume `Module.finrank ℚ K = 2`. They live in the namespace `NumberField`,
except for the two `TauCeti.NumberField` results whose names are written out in full:

* `primesOver_eq_singleton_of_mem_ramifiedPrimes` and
  `ncard_primesOver_eq_one_of_mem_ramifiedPrimes`: a ramified prime has a unique prime above it.
* `ramificationIdx_eq_two_of_mem_ramifiedPrimes` and `inertiaDeg_eq_one_of_mem_ramifiedPrimes`:
  that prime has `e = 2` and `f = 1`.
* `absNorm_eq_of_mem_ramifiedPrimes`: its absolute norm is `p`.
* `TauCeti.NumberField.eq_of_absNorm_eq_of_mem_ramifiedPrimes`: every ideal of absolute norm `p`
  is that unique prime.
* `map_span_eq_sq_of_mem_ramifiedPrimes`: `p 𝓞 K = 𝔭 ^ 2`.
* `TauCeti.NumberField.eq_map_span_of_absNorm_eq_sq_of_mem_ramifiedPrimes`: every ideal of
  absolute norm `p ^ 2` is the ideal `p 𝓞 K`; hence
  `TauCeti.NumberField.isPrincipal_of_absNorm_eq_sq_of_mem_ramifiedPrimes`: it is principal.
* `map_eq_self_of_mem_ramifiedPrimes`: any ring automorphism of `𝓞 K` fixes `𝔭`.
* `mem_ramifiedPrimes_iff_ramificationIdx_eq_two`: conversely, `e = 2` characterises the ramified
  primes among the rational primes.
-/

public section

open Ideal Module
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

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
  have := Fact.mk hp
  set x : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨𝔭, ‹_›, ‹_›⟩ with hx
  have hx1 : (x : Ideal (𝓞 K)) = 𝔭 := by rw [hx]
  -- `e(𝔭) ≥ 2`, since it is positive and not `1`.
  have he : 2 ≤ 𝔭.ramificationIdx ℤ :=
    (Nat.two_le_iff _).mpr ⟨(Ideal.ramificationIdx_pos 𝔭 ℤ).ne', hram⟩
  have hf0 : 1 ≤ 𝔭.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔭 ℤ
  -- The summand at `𝔭` is at least `2`, since `e(𝔭) ≥ 2` and `f(𝔭) ≥ 1`.
  have htwo : 2 ≤ 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ :=
    le_trans (by omega) (Nat.mul_le_mul he hf0)
  have hsum := sum_ramificationIdx_mul_inertiaDeg_eq_two (K := K) (p := p) hK
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hx1] at hsum
  -- The summand at `𝔭` already accounts for the whole sum, so the remaining ones vanish.
  have hrest : ∑ q ∈ Finset.univ.erase x, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 0 := by omega
  have hxval : 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ = 2 := by omega
  -- `e ∣ 2` and `2` is prime, so `e = 2`; then `f = 1`.
  have heone : 𝔭.ramificationIdx ℤ = 2 :=
    ((Nat.prime_two.eq_one_or_self_of_dvd _ ⟨_, hxval.symm⟩).resolve_left (by omega))
  have hfone : 𝔭.inertiaDeg ℤ = 1 := by rw [heone] at hxval; omega
  -- A vanishing sum of terms that are each at least `1` has no terms, so `𝔭` is the only prime.
  have huniq : ∀ q : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), q = x := fun q => by
    by_contra hne
    exact absurd ((Finset.sum_eq_zero_iff.mp hrest) q
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ q⟩))
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  exact ⟨heone, hfone, hx1 ▸ Set.eq_singleton_iff_unique_mem.mpr
    ⟨x.2, fun q hq => congrArg Subtype.val (huniq ⟨q, hq.1, hq.2⟩)⟩⟩

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

include hK hmem

/-- The ramified case of the quadratic splitting law, for the prime `𝔭` named by the caller. -/
private theorem totallyRamified_of_mem_ramifiedPrimes :
    𝔭.ramificationIdx ℤ = 2 ∧ 𝔭.inertiaDeg ℤ = 1 ∧
      (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} := by
  obtain ⟨𝔮, h𝔮, hlo, hne⟩ := exists_ramificationIdx_ne_one hmem
  have := h𝔮
  have := hlo
  obtain ⟨he, hf, hset⟩ := totallyRamified_aux hK (prime_of_mem_ramifiedPrimes hmem) hne
  have h𝔭mem : 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨‹_›, ‹_›⟩
  rw [hset] at h𝔭mem
  rw [Set.mem_singleton_iff] at h𝔭mem
  rw [h𝔭mem]
  exact ⟨he, hf, hset⟩

/-- **A ramified prime of a quadratic field has a unique prime above it.** If `p` ramifies in a
number field `K` of degree `2`, the primes of `𝓞 K` above `p` are the single prime `𝔭`. -/
theorem primesOver_eq_singleton_of_mem_ramifiedPrimes :
    (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} :=
  (totallyRamified_of_mem_ramifiedPrimes hK hmem 𝔭).2.2

/-- **A ramified prime of a quadratic field has exactly one prime above it.** The count form of
`primesOver_eq_singleton_of_mem_ramifiedPrimes`: in the notation of the fundamental identity,
`g = 1`. -/
theorem ncard_primesOver_eq_one_of_mem_ramifiedPrimes :
    ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = 1 := by
  have := Fact.mk (prime_of_mem_ramifiedPrimes hmem)
  obtain ⟨𝔮, _, _⟩ := (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
  rw [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔮, Set.ncard_singleton]

/-- **A ramified prime of a quadratic field is totally ramified.** The prime `𝔭` above a ramified
rational prime `p` has ramification index `e(𝔭 ∣ p) = 2`. -/
theorem ramificationIdx_eq_two_of_mem_ramifiedPrimes : 𝔭.ramificationIdx ℤ = 2 :=
  (totallyRamified_of_mem_ramifiedPrimes hK hmem 𝔭).1

/-- **The residue field does not grow at a ramified prime of a quadratic field.** The prime `𝔭`
above a ramified rational prime `p` has inertia degree `f(𝔭 ∣ p) = 1`. -/
theorem inertiaDeg_eq_one_of_mem_ramifiedPrimes : 𝔭.inertiaDeg ℤ = 1 :=
  (totallyRamified_of_mem_ramifiedPrimes hK hmem 𝔭).2.1

/-- **The absolute norm of a ramified prime of a quadratic field is the rational prime below it.**
Since the residue degree is `1` (`inertiaDeg_eq_one_of_mem_ramifiedPrimes`), the residue field of
`𝔭` is `ℤ/p`, so `N(𝔭) = p`. -/
theorem absNorm_eq_of_mem_ramifiedPrimes : Ideal.absNorm 𝔭 = p := by
  have hpprime := prime_of_mem_ramifiedPrimes hmem
  have hne : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using Int.natCast_ne_zero.mpr hpprime.ne_zero
  have : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    ((Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hpprime.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hpprime)).isMaximal hne
  have : 𝔭.IsMaximal :=
    (inferInstance : 𝔭.IsPrime).isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hne 𝔭)
  rw [Ideal.absNorm_eq_pow_inertiaDeg' 𝔭 hpprime,
    Ideal.inertiaDeg'_eq_inertiaDeg, inertiaDeg_eq_one_of_mem_ramifiedPrimes hK hmem 𝔭, pow_one]

/-- **`p 𝓞 K = 𝔭 ^ 2` at a ramified prime of a quadratic field.** The ideal generated by a ramified
rational prime `p` in the ring of integers of a quadratic field is the square of the unique prime
above it. -/
theorem map_span_eq_sq_of_mem_ramifiedPrimes :
    (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = 𝔭 ^ 2 := by
  have hprime := prime_of_mem_ramifiedPrimes hmem
  have := Fact.mk hprime
  -- `p 𝓞 K` is the product of the primes above `p` to their ramification indices; here that
  -- product runs over the single prime `𝔭`, with exponent `e(𝔭 ∣ p) = 2`.
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (by simp [hprime.ne_zero]),
    Set.toFinset_congr (primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭)]
  simp [ramificationIdx_eq_two_of_mem_ramifiedPrimes hK hmem 𝔭]

/-- **A ring automorphism fixes a ramified prime.** In a degree-two number field, any ring
automorphism `σ` of `𝓞 K` fixes the unique prime `𝔭` above a ramified rational prime `p`: `σ 𝔭` is
again a prime of `𝓞 K` lying over `p`, and a ramified prime has only one prime above it. -/
theorem map_eq_self_of_mem_ramifiedPrimes (σ : 𝓞 K ≃+* 𝓞 K) :
    Ideal.map σ 𝔭 = 𝔭 := by
  have hlo : (Ideal.map σ 𝔭).LiesOver (span {(p : ℤ)}) :=
    Ideal.LiesOver.of_eq_map_equiv (span {(p : ℤ)}) σ.toIntAlgEquiv rfl
  have hmemset : Ideal.map σ 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) :=
    ⟨inferInstance, hlo⟩
  rwa [primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭, Set.mem_singleton_iff] at hmemset

omit hmem
include hp

/-- **Ramification index `2` characterises the ramified primes of a quadratic field.** For a
rational prime `p` and a prime `𝔭` of `𝓞 K` above it, `p` ramifies in the quadratic field `K` iff
`e(𝔭 ∣ p) = 2`. -/
theorem mem_ramifiedPrimes_iff_ramificationIdx_eq_two :
    p ∈ ramifiedPrimes K ↔ 𝔭.ramificationIdx ℤ = 2 := by
  refine ⟨fun hmem => ramificationIdx_eq_two_of_mem_ramifiedPrimes hK hmem 𝔭, fun he => ?_⟩
  refine mem_ramifiedPrimes_iff.mpr ⟨hp, fun hunr => ?_⟩
  have := Algebra.IsUnramifiedIn.ramificationIdx_eq_one (R := ℤ) hunr (𝔓 := 𝔭) ‹_›
  omega

end NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

/-- **An ideal of prime norm is the unique prime above a ramified rational prime.** If `p`
ramifies in a quadratic number field, every ideal of absolute norm `p` equals the caller's chosen
prime `𝔭` above `p`. -/
theorem eq_of_absNorm_eq_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    (hmem : p ∈ _root_.NumberField.ramifiedPrimes K) (𝔭 I : Ideal (𝓞 K)) [𝔭.IsPrime]
    [𝔭.LiesOver (span {(p : ℤ)})] (hI : I.absNorm = p) : I = 𝔭 := by
  have hpprime := _root_.NumberField.prime_of_mem_ramifiedPrimes hmem
  have hirr : Irreducible I.absNorm := by rw [hI]; exact hpprime
  let _ : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm hirr
  have hprimeNorm : I.absNorm.Prime := by rw [hI]; exact hpprime
  let _ : I.LiesOver (span {(p : ℤ)}) := ⟨by
    simpa [hI, Ideal.under_def] using Ideal.span_singleton_absNorm (I := I) hprimeNorm⟩
  have hmemI : I ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨inferInstance, inferInstance⟩
  have hset : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {𝔭} :=
    _root_.NumberField.primesOver_eq_singleton_of_mem_ramifiedPrimes hK hmem 𝔭
  have : I ∈ ({𝔭} : Set (Ideal (𝓞 K))) := hset ▸ hmemI
  simpa using this

/-- **An ideal whose absolute norm is the square of a ramified rational prime is the ideal that
prime generates.** In a quadratic number field, such an ideal is the square of the unique prime
`𝔭` above `p`, and `𝔭 ^ 2 = p 𝓞 K`. -/
theorem eq_map_span_of_absNorm_eq_sq_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    (hmem : p ∈ _root_.NumberField.ramifiedPrimes K) (I : Ideal (𝓞 K))
    (hI : I.absNorm = p ^ 2) :
    I = (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) := by
  have hp : p.Prime := _root_.NumberField.prime_of_mem_ramifiedPrimes hmem
  have hpdvd : p ∣ I.absNorm := by rw [hI]; exact dvd_pow_self p two_ne_zero
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hpdvd
  let _ : P.IsPrime := hPmax.isPrime
  let _ : P.LiesOver (span {(p : ℤ)}) := ⟨hPunder.symm⟩
  obtain ⟨J, hIJ⟩ := hPdvd
  have hPnorm : P.absNorm = p := _root_.NumberField.absNorm_eq_of_mem_ramifiedPrimes hK hmem P
  have hJnorm : J.absNorm = p := by
    have hnorm := congrArg Ideal.absNorm hIJ
    rw [map_mul, hI, hPnorm, sq] at hnorm
    exact (Nat.eq_of_mul_eq_mul_left hp.pos hnorm).symm
  have hJP : J = P := eq_of_absNorm_eq_of_mem_ramifiedPrimes hK hmem P J hJnorm
  rw [hIJ, hJP, ← pow_two]
  exact (_root_.NumberField.map_span_eq_sq_of_mem_ramifiedPrimes hK hmem P).symm

/-- **An ideal whose absolute norm is the square of a ramified rational prime is principal.** By
`eq_map_span_of_absNorm_eq_sq_of_mem_ramifiedPrimes` it is the ideal `p 𝓞 K`, generated by `p`. -/
theorem isPrincipal_of_absNorm_eq_sq_of_mem_ramifiedPrimes (hK : finrank ℚ K = 2)
    (hmem : p ∈ _root_.NumberField.ramifiedPrimes K) (I : Ideal (𝓞 K))
    (hI : I.absNorm = p ^ 2) : Submodule.IsPrincipal I := by
  rw [eq_map_span_of_absNorm_eq_sq_of_mem_ramifiedPrimes hK hmem I hI, Ideal.map_span,
    Set.image_singleton]
  exact ⟨algebraMap ℤ (𝓞 K) p, rfl⟩

end TauCeti.NumberField
