/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid

/-!
# Functors on a groupoid with a weakly initial object

Let `C` be a groupoid and `x₀ : C` an object which admits a morphism to every object. Restricting
functors `F G : C ⥤ D` to `x₀` produces objects of `D` with actions of the vertex group
`End x₀`. This file proves that an isomorphism `F.obj x₀ ≅ G.obj x₀` commuting with these
actions extends to a natural isomorphism `F ≅ G`, and the extension has the given isomorphism
as its component at `x₀`.

The construction is the usual transport of structure. Choosing a morphism `γ x : x₀ ⟶ x` for
every object, the component at `x` is `F.map (γ x)⁻¹ ≫ e ≫ G.map (γ x)`; naturality at
`f : x ⟶ y` holds because the discrepancy `γ x ≫ f ≫ (γ y)⁻¹` between the two chosen morphisms
is an endomorphism of `x₀`, so equivariance applies to it. Nothing depends on the choice, since
the resulting natural transformation is determined by its component at `x₀`, and that component
is `e` whatever `γ x₀` is.

The hypothesis is exactly connectedness of the groupoid when `C` is nonempty, but is stated as
the family of nonemptiness assertions `∀ x, Nonempty (x₀ ⟶ x)` rather than through
`CategoryTheory.IsConnected`: the intended source of that data is a path-connected topological
space, whose fundamental groupoid comes with paths from a chosen basepoint, and the equivalence
of the two formulations is not needed.

## Main declarations

* `TauCeti.Groupoid.natIsoOfEnd`: an equivariant isomorphism of the values at a weakly initial
  object of a groupoid extends to a natural isomorphism.
* `TauCeti.Groupoid.natIsoOfEnd_app_self`: the extension restricts to the given isomorphism.
-/

public section
noncomputable section

universe t w v u

open CategoryTheory

namespace TauCeti.Groupoid

variable {C : Type u} [CategoryTheory.Groupoid.{v} C] {D : Type w} [Category.{t} D]
  {F G : C ⥤ D} {x₀ : C} (hconn : ∀ x : C, Nonempty (x₀ ⟶ x))

/-- A chosen isomorphism from the weakly initial object `x₀` to an arbitrary object. -/
private def chosenIso (x : C) : x₀ ≅ x :=
  (CategoryTheory.Groupoid.isoEquivHom x₀ x).symm (hconn x).some

/-- An `End x₀`-equivariant isomorphism between the values of two functors at a
weakly initial object of a groupoid extends to a natural isomorphism.

Its component at `x₀` is the given isomorphism, by `natIsoOfEnd_app_self`. -/
def natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    F ≅ G :=
  NatIso.ofComponents
    (fun x => (F.mapIso (chosenIso hconn x)).symm ≪≫ e ≪≫ G.mapIso (chosenIso hconn x))
    (fun {x y} f => by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
        Category.assoc]
      -- Cancel the chosen transports, then apply equivariance to their discrepancy.
      rw [← cancel_epi (F.mapIso (chosenIso hconn x)).hom,
        ← cancel_mono (G.mapIso (chosenIso hconn y)).inv]
      simp only [Functor.mapIso_hom, Functor.mapIso_inv]
      rw [← F.map_comp_assoc, ← F.map_comp_assoc]
      simp only [Category.assoc]
      rw [reassoc_of% (he ((chosenIso hconn x).hom ≫ f ≫ (chosenIso hconn y).inv))]
      rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
      simp only [G.map_comp, Category.assoc]
      simp)

private theorem natIsoOfEnd_hom_app (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) (x : C) :
    (natIsoOfEnd hconn e he).hom.app x =
      F.map (chosenIso hconn x).inv ≫ e.hom ≫ G.map (chosenIso hconn x).hom := by
  simp [natIsoOfEnd]

/-- The extension of an equivariant isomorphism restricts to that isomorphism. -/
@[simp]
theorem natIsoOfEnd_app_self (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    (natIsoOfEnd hconn e he).app x₀ = e := by
  apply Iso.ext
  -- Compare the hom components using the chosen transport formula.
  change (natIsoOfEnd hconn e he).hom.app x₀ = e.hom
  rw [natIsoOfEnd_hom_app, ← he (chosenIso hconn x₀).hom, ← Category.assoc, ← F.map_comp,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

end TauCeti.Groupoid
