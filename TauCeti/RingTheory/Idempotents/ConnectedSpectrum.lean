/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen

/-!
# Connected prime spectra and idempotents

The prime spectrum of a nontrivial commutative ring is connected exactly when the ring has no
idempotents other than zero and one.  Mathlib identifies idempotents with clopen subsets of the
prime spectrum; this file records the resulting connectedness criterion in the form used by
coordinate rings of geometrically connected affine schemes.

## Main declaration

* `TauCeti.connectedSpace_primeSpectrum_iff`: `Spec R` is connected if and only if every
  idempotent of `R` is zero or one.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- **The prime spectrum of a nontrivial commutative ring is connected exactly when its only
idempotents are zero and one.** -/
theorem connectedSpace_primeSpectrum_iff :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [connectedSpace_iff_clopen]
  constructor
  · rintro ⟨_, hconnected⟩ e he
    rcases hconnected (PrimeSpectrum.basicOpen e)
        ((PrimeSpectrum.isClopen_iff).2 ⟨e, he, rfl⟩) with hempty | huniv
    · left
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.zero
      rw [PrimeSpectrum.basicOpen_zero]
      exact TopologicalSpace.Opens.ext hempty
    · right
      apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he IsIdempotentElem.one
      rw [PrimeSpectrum.basicOpen_one]
      exact TopologicalSpace.Opens.ext huniv
  · intro hidempotent
    refine ⟨inferInstance, ?_⟩
    intro s hs
    obtain ⟨e, he, rfl⟩ := (PrimeSpectrum.isClopen_iff).1 hs
    rcases hidempotent e he with rfl | rfl
    · simp
    · simp

end TauCeti
