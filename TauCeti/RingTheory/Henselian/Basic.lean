/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Adically complete local rings are Henselian local rings

Mathlib has both halves of the comparison between `HenselianRing R I`, which lifts a simple root
over `R ⧸ I`, and `HenselianLocalRing R`, which lifts a simple root over the residue field, except
for the step that produces the local class from the ideal-theoretic one at `I = 𝔪`. So
`IsAdicComplete.henselianRing` never reaches `HenselianLocalRing`, and the Henselian API is
unavailable for a complete local ring such as the integers of a complete discretely valued field.

The step is short: the two differ only in their simplicity hypothesis, `IsUnit (f' a₀)` against
`IsUnit (Ideal.Quotient.mk 𝔪 (f' a₀))`, and over a local ring a unit maps to a unit.

## Main results

* `TauCeti.IsAdicComplete.henselianLocalRing`: a local ring that is complete for the adic topology
  of its maximal ideal is a Henselian local ring.
-/

public section

namespace TauCeti

open IsLocalRing

/-- A local ring that is complete for the adic topology of its maximal ideal is a Henselian local
ring. This is Mathlib's `IsAdicComplete.henselianRing` at `I = 𝔪`, whose simplicity hypothesis is
weaker: it asks the derivative to be a unit in the residue field rather than in the ring, and over
a local ring the image of a unit is a unit. -/
instance IsAdicComplete.henselianLocalRing (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _)

end TauCeti
