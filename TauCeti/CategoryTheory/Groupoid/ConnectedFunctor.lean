/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Type-valued functors on a groupoid with a weakly initial object

Let `C` be a groupoid and `x₀ : C` an object which admits a morphism to every object. Restricting
a functor `F : C ⥤ Type w` to `x₀` produces the set `F.obj x₀` together with the action of the
vertex group `End x₀` on it. This file proves that the restriction loses nothing up to
isomorphism: an `End x₀`-equivariant isomorphism `F.obj x₀ ≅ G.obj x₀` extends to a natural
isomorphism `F ≅ G`, and the extension has the given isomorphism as its component at `x₀`.

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

universe w v u

open CategoryTheory

namespace TauCeti.Groupoid

variable {C : Type u} [CategoryTheory.Groupoid.{v} C] {F G : C ⥤ Type w} {x₀ : C}
  (hconn : ∀ x : C, Nonempty (x₀ ⟶ x))

/-- A chosen isomorphism from the weakly initial object `x₀` to an arbitrary object. -/
private def chosenIso (x : C) : x₀ ≅ x :=
  (CategoryTheory.Groupoid.isoEquivHom x₀ x).symm (hconn x).some

/-- An `End x₀`-equivariant isomorphism between the values of two type-valued functors at a
weakly initial object of a groupoid extends to a natural isomorphism.

Its component at `x₀` is the given isomorphism, by `natIsoOfEnd_app_self`. -/
def natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    F ≅ G :=
  NatIso.ofComponents
    (fun x => (F.mapIso (chosenIso hconn x)).symm ≪≫ e ≪≫ G.mapIso (chosenIso hconn x))
    (fun {x y} f => by
      -- The two chosen morphisms differ by an endomorphism of `x₀`, to which equivariance
      -- applies.
      have he' : ∀ (g : x₀ ⟶ x₀) (b : F.obj x₀), e.hom (F.map g b) = G.map g (e.hom b) := by
        intro g b
        simpa using ConcreteCategory.congr_hom (he g) b
      have key : ∀ a : F.obj x,
          F.map (chosenIso hconn y).inv (F.map f a) =
            F.map ((chosenIso hconn x).hom ≫ f ≫ (chosenIso hconn y).inv)
              (F.map (chosenIso hconn x).inv a) := by
        intro a
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        congr 1
        simp
      have key' : ∀ c : G.obj x₀,
          G.map (chosenIso hconn y).hom
              (G.map ((chosenIso hconn x).hom ≫ f ≫ (chosenIso hconn y).inv) c) =
            G.map f (G.map (chosenIso hconn x).hom c) := by
        intro c
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        congr 1
        simp
      refine ConcreteCategory.hom_ext _ _ fun a => ?_
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
        types_comp_apply]
      rw [key, he', key'])

private theorem natIsoOfEnd_hom_app (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) (x : C) :
    (natIsoOfEnd hconn e he).hom.app x =
      F.map (chosenIso hconn x).inv ≫ e.hom ≫ G.map (chosenIso hconn x).hom := by
  simp [natIsoOfEnd]

/-- The extension of an equivariant isomorphism restricts to that isomorphism. -/
@[simp]
theorem natIsoOfEnd_app_self (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    (natIsoOfEnd hconn e he).hom.app x₀ = e.hom := by
  rw [natIsoOfEnd_hom_app, ← he (chosenIso hconn x₀).hom, ← Category.assoc, ← F.map_comp,
    Iso.inv_hom_id, F.map_id, Category.id_comp]

end TauCeti.Groupoid
