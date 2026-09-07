/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Complements on Dedekind-domain factorization

Facts about `Associates.count` and `FractionalIdeal.count` that Mathlib does not carry, together
with unit-level factorization of invertible fractional ideals.

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
  argument needs the `S`-class group to be finite. It is also the step that carries
  `count_toPrincipalIdeal_eq_neg_log_valuation` below. `count_div` is its general form and has no
  consumer in this repository yet.
* `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`: the multiplicity at `v` of the
  principal fractional ideal of a nonzero rational function `u : Kˣ` is
  `-WithZero.log (v.valuation K u)`. This is the passage between the two ways this library measures
  a principal ideal at a height one prime — Mathlib's `count` and the adic valuation.
* `IsDedekindDomain.HeightOneSpectrum.unitOfPrime`: a height-one prime regarded as an invertible
  fractional ideal.
* `FractionalIdeal.hasFiniteMulSupport_zpow_count`: a family of powers indexed by the height one
  primes, with the multiplicities of a fixed fractional ideal as exponents, has finite
  multiplicative support. The bases are an arbitrary family in an arbitrary `DivInvMonoid`, since
  nothing but the vanishing of almost all exponents is at stake; the unit-level factorization below
  is the case of the primes themselves.
* `FractionalIdeal.finprod_unitOfPrime_zpow_count`: unique factorization of an invertible
  fractional ideal, transported along `Units.coeHom`.

All these declarations are general facts about an arbitrary Dedekind domain, mentioning no
particular ring extension.

`le_count_associates_iff_le_pow` is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean:381` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's convention
for adapted material, the upstream authorship is credited here rather than in the copyright header.
**`count_div` and `count_spanSingleton_div` are new here** — they have no counterpart in that
source. `count_toPrincipalIdeal_eq_neg_log_valuation` is this repository's own, relocated here
from `TauCeti/AlgebraicGeometry/WeilDivisor/Dedekind/Basic.lean`: nothing in its statement or
proof mentions a Weil divisor, and stating it under `TauCeti.AlgebraicGeometry` put it out of
reach of the `RingTheory` consumers that need it, which is exactly the boundary
`TauCeti/RingTheory/ClassGroup/HeightOneSpectrum.lean` records in its module docstring.

The unit-level prime factorization `FractionalIdeal.finprod_unitOfPrime_zpow_count` is adapted
from Michael Stoll's `EllipticCurves/Mathlib/FractionalIdeal.lean` at commit `66889eada51a` of the
`MichaelStollBayreuth/EllipticCurves` repository (Apache 2.0).
-/
public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A height-one prime, regarded as an invertible fractional ideal. -/
noncomputable def unitOfPrime (v : HeightOneSpectrum R) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The fractional ideal underlying `v.unitOfPrime K` is `v.asIdeal`. -/
@[simp]
theorem coe_unitOfPrime (v : HeightOneSpectrum R) (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] :
    (v.unitOfPrime K : FractionalIdeal R⁰ K) = v.asIdeal := by
  rw [unitOfPrime]
  exact Units.val_mk0 _

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

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **A prime-indexed family of powers with the multiplicities of a fractional ideal as exponents
has finite multiplicative support.** Only finitely many primes occur in a fractional ideal, so
only finitely many exponents are nonzero, whatever `DivInvMonoid` the bases live in. -/
lemma hasFiniteMulSupport_zpow_count {G : Type*} [DivInvMonoid G] (I : FractionalIdeal R⁰ K)
    (f : HeightOneSpectrum R → G) :
    (Function.mulSupport fun v : HeightOneSpectrum R ↦ f v ^ count K v I).Finite := by
  refine (Filter.eventually_cofinite.mp (finite_factors I)).subset fun v hv hc ↦ ?_
  exact hv (by simp only [hc, zpow_zero])

/-- Only finitely many factors in the unit-level prime factorization are nontrivial. -/
lemma hasFiniteMulSupport_unitOfPrime_zpow (I : (FractionalIdeal R⁰ K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum R ↦
      v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K)).Finite :=
  hasFiniteMulSupport_zpow_count (I : FractionalIdeal R⁰ K) (fun v ↦ v.unitOfPrime K)

/-- Unique factorization of an invertible fractional ideal as a product of prime powers. -/
lemma finprod_unitOfPrime_zpow_count (I : (FractionalIdeal R⁰ K)ˣ) :
    I = ∏ᶠ v : HeightOneSpectrum R,
      v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K) := by
  -- State the map equation separately: rewriting would also affect the coercion inside `count`.
  have hmap : ((∏ᶠ v : HeightOneSpectrum R,
        v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K)) :
        (FractionalIdeal R⁰ K)ˣ) =
      ∏ᶠ v : HeightOneSpectrum R,
        ((v.unitOfPrime K ^ count K v (I : FractionalIdeal R⁰ K) :
          (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) :=
    MonoidHom.map_finprod (Units.coeHom (FractionalIdeal R⁰ K))
      (hasFiniteMulSupport_unitOfPrime_zpow I)
  refine Units.ext ?_
  rw [hmap]
  simp only [Units.val_zpow_eq_zpow_val, HeightOneSpectrum.coe_unitOfPrime]
  exact (finprod_heightOneSpectrum_factorization' (K := K)
    (I := (I : FractionalIdeal R⁰ K)) (Units.ne_zero I)).symm

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

section PrincipalIdeal

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

private lemma count_spanSingleton_eq_neg_log_intValuation (v : HeightOneSpectrum A) (r : A)
    (hr : r ≠ 0) :
    count K v (spanSingleton A⁰ (algebraMap A K r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal A) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← coeIdeal_span_singleton (S := A⁰) (P := K) r, count_coe K v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

/-- **The multiplicity of a principal fractional ideal is the sign-flipped logarithm of the
valuation.** Stated at the multiplicative-units level `u : Kˣ`, matching Mathlib's
`toPrincipalIdeal A K : Kˣ →* _`. -/
theorem count_toPrincipalIdeal_eq_neg_log_valuation (v : HeightOneSpectrum A) (u : Kˣ) :
    count K v (toPrincipalIdeal A K u : FractionalIdeal A⁰ K) =
      -WithZero.log (v.valuation K (u : K)) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq A⁰ (u : K)
  have hn : n ≠ 0 := by
    intro hn
    apply u.ne_zero
    rw [← hnd, hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hd : (d : A) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hval : v.valuation K (u : K) = v.intValuation n / v.intValuation (d : A) :=
    hnd ▸ v.valuation_of_mk'
  rw [hval, coe_toPrincipalIdeal, ← hnd, IsFractionRing.mk'_eq_div,
    count_spanSingleton_div K v ((not_congr IsFractionRing.to_map_eq_zero_iff).mpr hn)
      ((not_congr IsFractionRing.to_map_eq_zero_iff).mpr hd),
    count_spanSingleton_eq_neg_log_intValuation K v n hn,
    count_spanSingleton_eq_neg_log_intValuation K v (d : A) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : A) hd)]
  ring

end PrincipalIdeal

end FractionalIdeal

end
