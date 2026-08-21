/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Complements on the multiplicity of a height one prime

Three facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.le_count_associates_iff_le_pow`: the multiplicity of `v` in
  a nonzero `J` is at least `k` exactly when `v ^ k` contains `J`. The multiplicity here is
  `Associates.count`, not `FractionalIdeal.count` — hence the `associates` token, matching
  Mathlib's `Ideal.count_associates_factors_eq` for the same expression. Mathlib reads that
  multiplicity as divisibility of `Associates`; a consumer comparing two multiplicities across a
  ring extension wants a containment of *ideals*, and shows the two ideals contain the same prime
  powers.
* `FractionalIdeal.count_div`: the multiplicity of `I / J` is the difference of the multiplicities
  of `I` and `J`. Mathlib's `count` API has `count_mul`, `count_inv`, `count_pow` and `count_zpow`
  but no division form, so every consumer that clears a denominator repeats the same rewrites.
* `FractionalIdeal.count_spanSingleton_div`: the same on principal fractional ideals. This is the
  one the `S`-integer class-group computation in
  `TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean` uses, at both `R` and `𝒪_S` — which
  is why the ring is a variable rather than fixed — advancing
  `TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 (Mordell–Weil), whose weak-Mordell–Weil
  argument needs the `S`-class group to be finite. `count_div` is its general form and has no
  consumer in this repository yet.

All three are general facts about an arbitrary Dedekind domain, mentioning no particular ring
extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**The two `count` lemmas are new here** — they have no counterpart in that source.
-/
public section

namespace IsDedekindDomain.HeightOneSpectrum

/-- The multiplicity of `v` in a nonzero ideal `J` is at least `k` exactly when `v ^ k` contains
`J`. -/
theorem le_count_associates_iff_le_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

end IsDedekindDomain.HeightOneSpectrum

namespace FractionalIdeal

open IsDedekindDomain

open scoped nonZeroDivisors

/-- **The multiplicity of a quotient is the difference of the multiplicities.** Mathlib's `count`
API has `count_mul`, `count_inv`, `count_pow` and `count_zpow` but no division form, so every
consumer that clears a denominator repeats the same rewrites. -/
theorem count_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (w : HeightOneSpectrum A) {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0)
    (hJ : J ≠ 0) : count K w (I / J) = count K w I - count K w J := by
  rw [div_eq_mul_inv, count_mul K w hI (inv_ne_zero hJ), count_inv]
  ring

/-- The multiplicity of `x / y` is the difference of the multiplicities of `x` and `y`: `count_div`
read on principal fractional ideals, which is the form the `S`-integer class-group computation
uses. -/
theorem count_spanSingleton_div {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] (w : HeightOneSpectrum A) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) :
    count K w (spanSingleton A⁰ (x / y)) =
      count K w (spanSingleton A⁰ x) - count K w (spanSingleton A⁰ y) := by
  rw [← spanSingleton_div_spanSingleton, count_div K w (spanSingleton_ne_zero_iff.mpr hx)
    (spanSingleton_ne_zero_iff.mpr hy)]

end FractionalIdeal

end
