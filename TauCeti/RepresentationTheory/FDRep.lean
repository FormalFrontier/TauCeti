/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Finite-dimensional representations

This file supplies general-purpose facts about Mathlib's category `FDRep`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

/-- Forgetting finite-dimensionality keeps the finite-generation instance on the carrier. -/
instance moduleFinite_forgetFDRep {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A)

/-- Forgetting finite-dimensionality does not change the dimension of the carrier. -/
@[simp]
theorem finrank_forgetFDRep {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

end TauCeti
