/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# Complements on the `v`-adic valuation of a unit

Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` is the `v`-adic valuation
restricted to `Kˣ`, valued in `Multiplicative ℤ` rather than `ℤₘ₀`, and Mathlib relates it to
`valuation` only through the coercion `valuationOfNeZero_eq`. This file adds the triviality
criterion in the uncoerced form.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`: a unit has trivial `v`-adic
  `valuationOfNeZero` exactly when its `v`-adic `valuation` is `1`.

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SelmerGroup.lean` at
the `EllipticCurves` roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll) reaches for a
`HeightOneSpectrum.valuationOfNeZero_eq_iff` in this role; no such lemma exists at our Mathlib
pin, so this supplies it. Following this repository's convention for adapted material, the
upstream authorship is credited here rather than in the copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`. Mathlib
carries this only in the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]

end IsDedekindDomain.HeightOneSpectrum

end
