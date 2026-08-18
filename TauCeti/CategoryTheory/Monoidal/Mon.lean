/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monoid objects

This file provides general-purpose facts about monoid objects, including the functor-of-points
form of monomorphism cancellation.

## Main declarations

* `TauCeti.isCommMonObj_of_grp_iso`: commutativity of a group object is preserved by isomorphism.
* `TauCeti.monoidHom_injective_of_mono`: a monic morphism of monoid objects is injective on points
  at every object.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

/-- Commutativity of a group object is preserved under isomorphism. -/
theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

/-- A monic morphism of monoid objects is injective on points at every object.

The map on points is postcomposition with the morphism, so its injectivity is the
functor-of-points form of the defining cancellation property of a monomorphism. -/
theorem monoidHom_injective_of_mono {C : Type u} [Category C] [CartesianMonoidalCategory C]
    {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N) [IsMonHom f] [Mono f] (T : C) :
    Function.Injective (IsMonHom.monoidHom f T) :=
  fun _ _ hpq => (cancel_mono f).1 hpq

end TauCeti
