/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.DedekindDomain.Ideal

/-!
# Adic valuations transport along an isomorphism of Dedekind domains

An isomorphism `e : R ≃+* R'` of Dedekind domains induces an isomorphism
`σ = IsFractionRing.ringEquivOfRingEquiv e : K ≃+* K'` of their fraction fields, and carries a
height one prime `v` of `R` to the height one prime of `R'` with underlying ideal
`Ideal.map e v.asIdeal`. This file proves that `σ` intertwines the two adic valuations: for a
height one prime `w` of `R'` with
`w.asIdeal = Ideal.map e v.asIdeal`,

```text
w.valuation K' (σ f) = v.valuation K f
```

for every `f : K`. Equivalently, `ord` at `w` of `σ f` is `ord` at `v` of `f`, which is the
algebraic content of the Galois descent `div (σ f) = σ_* (div f)` for divisors on a curve.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.intValuation_ringEquiv` and
  `IsDedekindDomain.HeightOneSpectrum.valuation_ringEquivOfRingEquiv`: the integer-valued and the
  fraction-field adic valuations transport.

The ideal-level input this rests on — that `Ideal.map e` preserves divisibility and
factorisation multiplicities, and that Mathlib's `equivOfRingEquiv` is `Ideal.map e` on
underlying ideals — is not valuation theory and lives in
`TauCeti/RingTheory/DedekindDomain/Ideal.lean`.

## Implementation notes

The hypothesis on the two primes is stated as the equation `w.asIdeal = Ideal.map e v.asIdeal`
rather than as `w = equivOfRingEquiv e v`, so that a call site holding some independently
constructed `w` — a place of a curve, say — does not first have to identify it with the transport.
`asIdeal_equivOfRingEquiv` discharges the hypothesis whenever `w` *is* that transport, so nothing
is lost in the other direction.

`valuation_ringEquivOfRingEquiv_algebraMap` is `private`: it is the `algebraMap` special case
used to reduce the general statement to a quotient of two elements of `R`, and the reusable
restriction result is `intValuation_ringEquiv`.

## Provenance

Adapted from [AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit
`513e83879e2f`, `projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`: the proofs of
`intValuation_map_ringEquiv`, `valuation_map_ringEquiv_algebraMap` and `valuation_map_ringEquiv`
are that file's, with the vocabulary adapted to this repository's interfaces. The ideal-level
lemmas adapted from the same source are attributed in
`TauCeti/RingTheory/DedekindDomain/Ideal.lean`.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, II.3 (the Galois action on divisors).
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

section DedekindDomain

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/-- **The integer adic valuation transports along a ring isomorphism.** If the height one prime `w`
of `R'` is the image of the height one prime `v` of `R` under `e`, then the `w`-adic valuation of
`e r` is the `v`-adic valuation of `r`. -/
theorem intValuation_ringEquiv (e : R ≃+* R') {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · have her : e r ≠ 0 := by simp [hr]
    have hspan : Ideal.span {e r} = Ideal.map e (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [w.intValuation_if_neg her, v.intValuation_if_neg hr, hvw, hspan,
      Ideal.count_factors_map_of_ringEquiv e ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime)
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hr)]

variable {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K']

/-- The fraction-field adic valuation transports on the image of `R`, which is the building block
for `valuation_ringEquivOfRingEquiv`. -/
private theorem valuation_ringEquivOfRingEquiv_algebraMap (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (r : R) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e (algebraMap R K r)) =
      v.valuation K (algebraMap R K r) := by
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap e r, valuation_of_algebraMap,
    valuation_of_algebraMap]
  exact intValuation_ringEquiv e hvw r

/-- **The adic valuation of the fraction field transports along a ring isomorphism.** With
`σ = IsFractionRing.ringEquivOfRingEquiv e` the induced isomorphism of fraction fields, and `w` the
image of `v` under `e`, the `w`-adic valuation of `σ f` is the `v`-adic valuation of `f`. This is
the algebraic engine of divisor Galois descent. -/
theorem valuation_ringEquivOfRingEquiv (e : R ≃+* R') {v : HeightOneSpectrum R}
    {w : HeightOneSpectrum R'} (hvw : w.asIdeal = Ideal.map e v.asIdeal) (f : K) :
    w.valuation K' (IsFractionRing.ringEquivOfRingEquiv e f) = v.valuation K f := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, Valuation.map_div, Valuation.map_div,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw a,
    valuation_ringEquivOfRingEquiv_algebraMap e hvw b]

end DedekindDomain

end IsDedekindDomain.HeightOneSpectrum
