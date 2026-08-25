/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Factorization
public import TauCeti.RingTheory.DedekindDomain.SInteger.Spectrum

/-!
# Multiplicities transfer to the `S`-integers

For `v ∉ S`, extension of ideals along `R → 𝒪_S` preserves the multiplicity at `v`: the
multiplicity of the extension at the prime `integerPrimeOverOfNotMem` above `v` is the multiplicity
of the original at `v`.

## Main results

* `IsDedekindDomain.integer_count_coeIdeal_map`: for an integral ideal.
* `IsDedekindDomain.integer_count_spanSingleton`: for a principal fractional ideal, obtained from
  the integral case by clearing a denominator.

These are the multiplicative analogue of the valuation-transfer lemmas
`valuation_integerPrimeOverOfNotMem` and `valuation_integerHeightOneSpectrumEquiv` in
`SInteger/Spectrum.lean`, and they are what the `S`-class-group computation in
`SInteger/ClassGroup.lean` runs on. They live in their own module rather than in `Spectrum.lean`
because they need `FractionalIdeal.count`, and `Spectrum.lean` does not otherwise depend on the
factorization layer — a consumer of the valuation transfer alone should not pay for it.

Both are adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's §Provenance pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this
repository's convention for adapted material, the upstream authorship is credited here rather than
in the copyright header. Stoll's unprefixed names are given the `integer` prefix that
`TauCeti/RingTheory/DedekindDomain/SInteger/` already uses.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- The multiplicity of the extension of an ideal at the prime above `v ∉ S` is the multiplicity
at `v`. -/
@[simp]
lemma integer_count_coeIdeal_map {v : HeightOneSpectrum R} (hv : v ∉ S) {J : Ideal R} :
    count K (integerPrimeOverOfNotMem K S hv)
        ((Ideal.map (algebraMap R (S.integer K)) J : Ideal (S.integer K)) :
          FractionalIdeal (S.integer K)⁰ K) =
      count K v (J : FractionalIdeal R⁰ K) := by
  rcases eq_or_ne J ⊥ with rfl | hJ
  · rw [Ideal.map_bot]
    simp only [coeIdeal_bot, count_zero]
  have hmJ := Ideal.map_ne_bot_of_ne_bot (S := S.integer K) hJ
  rw [count_coe K _ hmJ, count_coe K v hJ, Nat.cast_inj]
  -- the two multiplicities dominate the same `k`, and `le_count_associates_iff_le_pow` turns each
  -- side into
  -- containment of a prime power, which `integer_map_le_map_pow_iff` transfers
  refine eq_of_forall_le_iff fun k ↦ ?_
  rw [(integerPrimeOverOfNotMem K S hv).le_count_associates_iff_le_pow hmJ k,
    integer_map_le_map_pow_iff K S hv, ← v.le_count_associates_iff_le_pow hJ k]

/-- The multiplicity of a principal fractional ideal at the prime above `v ∉ S` is the
multiplicity at `v`. -/
@[simp]
lemma integer_count_spanSingleton {v : HeightOneSpectrum R} (hv : v ∉ S) {x : K} :
    count K (integerPrimeOverOfNotMem K S hv) (spanSingleton (S.integer K)⁰ x) =
      count K v (spanSingleton R⁰ x) := by
  -- The integral case already knows this, so it is enough to write `x = a / b` with `a b : R` and
  -- clear the denominator: `spanSingleton` of an element of `R` *is* a coerced ideal.
  have hcoe : ∀ r : R, spanSingleton (S.integer K)⁰ (algebraMap R K r) =
      ((Ideal.map (algebraMap R (S.integer K)) (Ideal.span {r}) : Ideal (S.integer K)) :
        FractionalIdeal (S.integer K)⁰ K) := by
    intro r
    rw [Ideal.map_span, Set.image_singleton, coeIdeal_span_singleton,
      ← IsScalarTower.algebraMap_apply R (S.integer K) K]
  have key : ∀ r : R, count K (integerPrimeOverOfNotMem K S hv)
      (spanSingleton (S.integer K)⁰ (algebraMap R K r)) =
        count K v (spanSingleton R⁰ (algebraMap R K r)) := by
    intro r
    rw [hcoe r, integer_count_coeIdeal_map K S hv, coeIdeal_span_singleton]
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [spanSingleton_zero, count_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hb)
  have ha0 : algebraMap R K a ≠ 0 := by
    rintro h; exact hx (by rw [h, zero_div])
  -- clearing the denominator turns each side into a difference of two integral counts, and `key`
  -- settles those; `FractionalIdeal.count_spanSingleton_div` is stated once, in
  -- `TauCeti/RingTheory/DedekindDomain/Factorization.lean`, and used here at both rings.
  rw [count_spanSingleton_div K _ ha0 hb0, count_spanSingleton_div K v ha0 hb0, key a, key b]

end IsDedekindDomain

end
