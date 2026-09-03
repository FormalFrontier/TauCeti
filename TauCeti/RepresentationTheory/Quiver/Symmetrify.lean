/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Finite.Defs

/-!
# Symmetrified quivers

This file supplies general infrastructure for Mathlib's `Quiver.Symmetrify` construction.

## References

This file supplies a prerequisite for Layer 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u

/-- Typeclass search does not unfold the `Symmetrify` type synonym to reuse `Finite Q`. -/
instance instFiniteSymmetrify (Q : Type u) [Finite Q] : Finite (Symmetrify Q) :=
  inferInstanceAs (Finite Q)

end TauCeti
