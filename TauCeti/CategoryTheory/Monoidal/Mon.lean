/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Commutative monoid objects

This file provides general-purpose facts about commutative monoid objects.

## Main declarations

* `TauCeti.isCommMonObj_of_grp_iso`: commutativity of a group object is preserved by isomorphism.
* `TauCeti.isCommMonObj_mapGrp_obj`: a braided functor preserves commutativity of group objects.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti

universe v₁ v₂ u₁ u₂

/-- A braided functor preserves commutativity of group objects. -/
instance isCommMonObj_mapGrp_obj
    {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] (G : Grp C) [IsCommMonObj G.X] :
    IsCommMonObj (F.mapGrp.obj G).X := by
  change IsCommMonObj (F.obj G.X)
  infer_instance

/-- Commutativity of a group object is preserved under isomorphism. -/
theorem isCommMonObj_of_grp_iso
    {C : Type u₁} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

end TauCeti
