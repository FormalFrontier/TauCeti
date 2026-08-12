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

## Main declarations

* `TauCeti.eq_zero_or_eq_one_of_isIdempotentElem`: an idempotent is zero or one when `Spec R`
  is connected.
* `TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one`: `Spec R` is connected
  if and only if every idempotent of `R` is zero or one.
* `TauCeti.connectedSpace_primeSpectrum_of_injective`: connectedness descends along an
  injective ring homomorphism.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- An idempotent in a commutative ring with connected prime spectrum is zero or one. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem [ConnectedSpace (PrimeSpectrum R)]
    {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have hconnected := (connectedSpace_iff_clopen.mp
    (inferInstance : ConnectedSpace (PrimeSpectrum R))).2
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

variable [Nontrivial R]

/-- **The prime spectrum of a nontrivial commutative ring is connected exactly when its only
idempotents are zero and one.** -/
theorem connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro h
    let := h
    exact fun _ he ↦ eq_zero_or_eq_one_of_isIdempotentElem he
  · intro hidempotent
    rw [connectedSpace_iff_clopen]
    refine ⟨inferInstance, ?_⟩
    intro s hs
    obtain ⟨e, he, rfl⟩ := (PrimeSpectrum.isClopen_iff).1 hs
    rcases hidempotent e he with rfl | rfl
    · simp
    · simp

variable {S : Type*} [CommRing S]

omit [Nontrivial R] in
/-- Connectedness of prime spectra descends along injective ring homomorphisms. -/
theorem connectedSpace_primeSpectrum_of_injective [ConnectedSpace (PrimeSpectrum S)]
    (f : R →+* S) (hf : Function.Injective f) : ConnectedSpace (PrimeSpectrum R) := by
  let : Nontrivial S := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial R := f.domain_nontrivial
  rw [connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one]
  intro e he
  rcases eq_zero_or_eq_one_of_isIdempotentElem (he.map f) with hzero | hone
  · exact Or.inl (hf (hzero.trans f.map_zero.symm))
  · exact Or.inr (hf (hone.trans f.map_one.symm))

end TauCeti
