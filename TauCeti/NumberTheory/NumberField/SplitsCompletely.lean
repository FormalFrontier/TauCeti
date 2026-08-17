/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.RamificationInertia.Galois
public import TauCeti.NumberTheory.RamificationInertia.Splitting

/-!
# A counting criterion for a prime to split completely in a number field

For a finite Galois number field `K / ℚ`, a rational prime `p` splits completely — meaning
there are exactly `[K : ℚ]` primes of `𝓞 K` above `p` — if and only if `p` is unramified with
residue degree one, i.e. both the ramification index `e` and the inertia degree `f` (which are
common to all primes above `p`, the extension being Galois) equal `1`.

One direction needs no Galois hypothesis at all: a full complement of primes already forces
`e = f = 1` at each of them, directly from the fundamental identity, and hence identifies each
residue field with the prime field.

This is the count form of the fundamental identity `(#primes) · e · f = [L : K]`: with the
product fixed at `[L : K]`, the number of primes is maximal exactly when `e = f = 1`. The
rational-prime corollary is the Galois-number-field criterion underlying the multiquadratic
prime-splitting law (Layer 1 of the multiquadratic roadmap), where complete splitting is read
off from residues.

## Main results

* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff`: the rational-prime specialization.
* `TauCeti.NumberField.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank`:
  complete splitting makes each residue field the prime field.
* `TauCeti.NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`: the orbit–stabilizer
  form — `p` splits completely iff the decomposition group of a prime above it is trivial.

## Provenance

Two of Mathlib's fundamental identities are used, according to whether a Galois hypothesis is
available. The splitting criterion itself rests on the Galois identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`). The consequences drawn without
a Galois hypothesis — that complete splitting forces `e = f = 1`, and hence that the residue field
at `Q` is the prime field — rest instead on the general identity for finite flat extensions of
domains (`Ideal.sum_ramification_inertia_eq_finrank`), applied through
the general theorem in `TauCeti.RamificationInertia.Splitting`.
The criterion is assembled here for the Tau Ceti library.
-/

public section

open NumberField Ideal Module MulAction
open scoped Pointwise

namespace TauCeti.NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

private theorem ncard_primesOver_eq_finrank_iff_of_isGalois {A : Type*} [CommRing A]
    [IsDedekindDomain A] [Algebra A (𝓞 L)] [Module.Finite A (𝓞 L)]
    [IsTorsionFree A (𝓞 L)] [IsGaloisGroup Gal(L/K) A (𝓞 L)] (P : Ideal A) [P.IsMaximal] :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔
      P.ramificationIdxIn (𝓞 L) = 1 ∧ P.inertiaDegIn (𝓞 L) = 1 := by
  have h := TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup
    (B := 𝓞 L) Gal(L/K) P
  rw [IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at h
  exact h

/-- In a Galois number field, a rational prime `p` splits completely (there are `[K : ℚ]` primes
of `𝓞 K` above `p`) iff its ramification index and inertia degree are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [Fact p.Prime] : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧ (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hpne
  have : (span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  have : (span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal ‹_› hp0
  have h := ncard_primesOver_eq_finrank_iff_of_isGalois ℚ K (A := ℤ) (span {(p : ℤ)})
  exact h

/-- **Splitting completely ⟺ decomposition group trivial.** For a Galois number field `L` and a
prime `Q` of `𝓞 L` above the rational prime `p`, the prime `p` splits completely (there are
`[L : ℚ]` primes above it) iff the decomposition group of `Q` — its stabilizer under `Gal(L/ℚ)` —
is trivial. -/
theorem ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot (L : Type*) [Field L]
    [NumberField L] [IsGalois ℚ L] {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] : (primesOver (span {(p : ℤ)}) (𝓞 L)).ncard = finrank ℚ L ↔
      stabilizer (L ≃ₐ[ℚ] L) Q = ⊥ := by
  -- The orbit of `Q` under `Gal(L/ℚ)` is all of the primes above `p`, so orbit–stabilizer gives
  -- `#{primes above p} · |stabilizer Q| = |Gal(L/ℚ)| = [L : ℚ]`.
  have horbit : orbit (L ≃ₐ[ℚ] L) Q = (span {(p : ℤ)}).primesOver (𝓞 L) :=
    Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 L) (L ≃ₐ[ℚ] L) (span {(p : ℤ)}) Q
  have hkey : (primesOver (span {(p : ℤ)}) (𝓞 L)).ncard *
      Nat.card (stabilizer (L ≃ₐ[ℚ] L) Q) = finrank ℚ L := by
    rw [← Nat.card_coe_set_eq, ← horbit, ← Nat.card_prod,
      Nat.card_congr (orbitProdStabilizerEquivGroup (L ≃ₐ[ℚ] L) Q),
      IsGalois.card_aut_eq_finrank]
  have hpos : 0 < finrank ℚ L := finrank_pos
  constructor
  · intro hn
    rw [hn] at hkey
    have hst1 : Nat.card (stabilizer (L ≃ₐ[ℚ] L) Q) = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hkey)
    exact Subgroup.card_eq_one.mp hst1
  · intro hst
    rw [hst] at hkey
    simpa using hkey

/-- **Complete splitting makes the residue field at `Q` the prime field.** If `p` splits
completely then `algebraMap (ℤ ⧸ (p)) (𝓞 K ⧸ Q)` is bijective. No Galois hypothesis is needed. -/
theorem bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank {K : Type*} [Field K]
    [NumberField K]
    {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})]
    (hsplit : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K) :
    Function.Bijective (algebraMap (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q)) := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hpne).mpr (Nat.prime_iff_prime_int.mp Fact.out))
      (by simpa [Ideal.span_singleton_eq_bot] using hpne)
  exact RamificationInertia.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank
    (span {(p : ℤ)}) Q (by rwa [NumberField.RingOfIntegers.rank])

end TauCeti.NumberField
