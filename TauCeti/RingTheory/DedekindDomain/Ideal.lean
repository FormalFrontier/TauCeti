/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on the height one spectrum of a Dedekind domain

A single fact about distinct height-one primes of a Dedekind domain, complementing
`Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`: distinct height-one primes are
incomparable, so each contains an element the other does not. This is what separates the
valuations at two primes, and it is consumed by
`TauCeti/RingTheory/DedekindDomain/SInteger/Basic.lean`.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Distinct height one primes are incomparable: a height one prime is not contained in any
other one, since both are maximal. -/
lemma exists_mem_notMem {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

end IsDedekindDomain.HeightOneSpectrum

end
