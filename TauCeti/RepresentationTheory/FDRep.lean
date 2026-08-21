/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Finite-dimensional representations

This file records how the forgetful functor `FDRep R G ⥤ Rep R G` preserves module-finiteness and
finrank. These facts let results proved for representation carriers transfer back to `FDRep`, in
particular in `TauCeti.RepresentationTheory.Induction.FiniteDimensional`. In the same spirit it
records that rebundling the representation an object carries returns that object, which is the
identification a construction phrased as `FDRep.of ρ` needs in order to be read as a statement
about the object it started from.

## Main statements

* `FDRep.moduleFinite_forget₂_obj`: the forgotten carrier is module-finite.
* `FDRep.finrank_forget₂_obj`: forgetting does not change finrank.
* `FDRep.of_ρ_eq_self`: rebundling the representation carried by an object returns that object.
-/

public section

namespace FDRep

open CategoryTheory

universe u v

/-- Forgetting finite-dimensionality keeps the finite-generation instance on the carrier. -/
instance moduleFinite_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) : Module.Finite R ((forget₂ (FDRep R G) (Rep R G)).obj A) :=
  inferInstanceAs (Module.Finite R A)

/-- Forgetting finite-dimensionality does not change the dimension of the carrier. -/
@[simp]
theorem finrank_forget₂_obj {R : Type u} {G : Type v} [CommRing R] [Monoid G]
    (A : FDRep R G) :
    Module.finrank R ((forget₂ (FDRep R G) (Rep R G)).obj A) = Module.finrank R A :=
  rfl

/-- Rebundling the representation carried by an object of `FDRep R G` returns that object. -/
@[simp]
theorem of_ρ_eq_self {R : Type u} {G : Type v} [CommRing R] [Monoid G] (A : FDRep R G) :
    FDRep.of A.ρ = A := (rfl)

end FDRep
