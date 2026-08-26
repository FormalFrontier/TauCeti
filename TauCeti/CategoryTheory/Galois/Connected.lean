/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Galois.Basic

/-!
# Connected objects are invariant under equivalence

`CategoryTheory.PreGaloisCategory.IsConnected` is defined by conditions on initial objects,
monomorphisms and isomorphisms alone, and an equivalence of categories preserves and reflects all
three. This file records the resulting transport statements: connectedness is invariant under
isomorphism inside a category, and an equivalence `F : C ⥤ D` makes `F.obj A` connected exactly
when `A` is.

None of this needs the Galois axioms. Mathlib states connectedness for an object of an arbitrary
category and only later restricts to `PreGaloisCategory`, and that arbitrary generality is what is
used here; in particular the statements apply to a category that is merely *equivalent* to a
Galois category, which is how a connectedness criterion is transported to a concrete category
whose objects are not finite sets.

## Main declarations

* `TauCeti.isConnected_of_iso`: an object isomorphic to a connected object is connected.
* `TauCeti.isConnected_map`: an equivalence carries connected objects to connected objects.
* `TauCeti.isConnected_map_iff`: connectedness of `F.obj A` is equivalent to connectedness of `A`.
-/

public section
noncomputable section

universe v₁ v₂ u₁ u₂

namespace TauCeti

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An object isomorphic to a connected object is connected. -/
theorem isConnected_of_iso {A B : C} (e : A ≅ B) [PreGaloisCategory.IsConnected A] :
    PreGaloisCategory.IsConnected B where
  notInitial h := PreGaloisCategory.IsConnected.notInitial (h.ofIso e.symm)
  noTrivialComponent Y i hm hni := by
    have _ : Mono i := hm
    have _ : Mono (i ≫ e.inv) := mono_comp _ _
    have h : IsIso (i ≫ e.inv) :=
      PreGaloisCategory.IsConnected.noTrivialComponent Y (i ≫ e.inv) hni
    have hi : i = (i ≫ e.inv) ≫ e.hom := by simp
    rw [hi]
    infer_instance

variable (F : C ⥤ D) [F.IsEquivalence]

-- The two isomorphisms below are the components of the unit and counit of `F.asEquivalence`,
-- restated with `𝟭` and `⋙` already evaluated. Without that, unification has to see through the
-- identity and composite functors to match `IsInitial`, `IsConnected` and `Iso` arguments against
-- the objects they are about, and fails.

/-- The unit isomorphism of an equivalence, at an object. -/
private def unitIsoApp (A : C) : A ≅ F.inv.obj (F.obj A) :=
  F.asEquivalence.unitIso.app A

/-- The counit isomorphism of an equivalence, at an object. -/
private def counitIsoApp (B : D) : F.obj (F.inv.obj B) ≅ B :=
  F.asEquivalence.counitIso.app B

/-- An equivalence of categories carries connected objects to connected objects. -/
theorem isConnected_map (A : C) [PreGaloisCategory.IsConnected A] :
    PreGaloisCategory.IsConnected (F.obj A) where
  notInitial h := PreGaloisCategory.IsConnected.notInitial (h.isInitialOfObj F A)
  noTrivialComponent Y i hm hni := by
    have _ : Mono i := hm
    have _ : Mono (F.inv.map i) := F.inv.map_mono i
    have _ : PreGaloisCategory.IsConnected (F.inv.obj (F.obj A)) :=
      isConnected_of_iso (unitIsoApp F A)
    have hni' : IsInitial (F.inv.obj Y) → False := fun h =>
      hni (IsInitial.ofIso (h.isInitialObj F (F.inv.obj Y)) (counitIsoApp F Y))
    have _ : IsIso (F.inv.map i) :=
      PreGaloisCategory.IsConnected.noTrivialComponent _ _ hni'
    exact isIso_of_reflects_iso i F.inv

/-- **Connectedness transports along an equivalence of categories**: for an equivalence
`F : C ⥤ D`, an object `A` of `C` is connected exactly when `F.obj A` is. -/
@[simp]
theorem isConnected_map_iff (A : C) :
    PreGaloisCategory.IsConnected (F.obj A) ↔ PreGaloisCategory.IsConnected A := by
  refine ⟨fun h => ?_, fun _ => isConnected_map F A⟩
  have _ : PreGaloisCategory.IsConnected (F.inv.obj (F.obj A)) := isConnected_map F.inv (F.obj A)
  exact isConnected_of_iso (unitIsoApp F A).symm

end TauCeti

end
