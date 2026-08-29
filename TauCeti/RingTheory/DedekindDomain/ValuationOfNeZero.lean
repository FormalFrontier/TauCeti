/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# The `Multiplicative ℤ`-valued adic valuation of a unit

Mathlib attaches to a height one prime `v` of a Dedekind domain `R` a homomorphism
`v.valuationOfNeZero : Kˣ →* Multiplicative ℤ`, the `v`-adic valuation of a unit of the fraction
field read without the adjoined zero, and relates it to `v.valuation K` in one direction only:
`valuationOfNeZero_eq` coerces it into `ℤᵐ⁰`. This file supplies the two complements that make it
usable as a rewriting rule.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff`: the `Multiplicative ℤ`-valued
  valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`: its `m = 1` case, that a unit
  has trivial `v`-adic `valuationOfNeZero` exactly when its `v`-adic valuation is `1`.

## Implementation notes

These live in their own module rather than beside their first consumer. `valuationOfNeZero` is
declared in `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`, so any host must import that;
but the *generic* completion and `S`-integer APIs that need these two lemmas must not, in
consequence, also inherit this repository's Selmer-group development. Keeping the pair here lets
`TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean` use them without depending on
`TauCeti/RingTheory/DedekindDomain/SelmerGroup.lean`, which is downstream of it.

## Provenance

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, at the `EllipticCurves` roadmap's pin
`66889eada51a`, Apache 2.0, by Michael Stoll) reaches for a
`HeightOneSpectrum.valuationOfNeZero_eq_iff`; no such lemma exists at our Mathlib pin, so it is
supplied here. Following this repository's convention for adapted material, the upstream
authorship is credited here rather than in the copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
Mathlib carries only the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_iff (v : HeightOneSpectrum R) (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`, the case
`m = 1` of `valuationOfNeZero_eq_iff`.

Not `@[simp]`: it is the `m = 1` instance of `valuationOfNeZero_eq_iff`, which carries the
annotation instead. With both marked, `simpNF` rejects this one — "simp can prove this" — because
the general form subsumes it. Every consumer names it explicitly, so nothing depends on the
attribute. -/
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  simp

end IsDedekindDomain.HeightOneSpectrum

end
