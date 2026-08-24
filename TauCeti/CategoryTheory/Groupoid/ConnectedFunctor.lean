/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.SingleObj

/-!
# Functors on a groupoid with a weakly initial object

Let `C` be a groupoid and `x₀ : C` an object which admits a morphism to every object. Restricting
functors `F G : C ⥤ D` to `x₀` produces objects of `D` with actions of the vertex group
`End x₀`. This file proves that an isomorphism `F.obj x₀ ≅ G.obj x₀` commuting with these
actions extends to a natural isomorphism `F ≅ G`, and the extension has the given isomorphism
as its component at `x₀`.

Nothing has to be transported by hand. Restricting along the vertex-group inclusion
`TauCeti.Groupoid.singleObjFunctor` is an equivalence of functor categories, because
`TauCeti.Groupoid.singleObjFunctor` itself is one by
`TauCeti.Groupoid.isEquivalence_singleObjFunctor`; the datum of an equivariant isomorphism
`F.obj x₀ ≅ G.obj x₀` is exactly a natural isomorphism between the two restrictions, and the
extension is its preimage under that equivalence. Being a preimage is also what pins down the
component at `x₀`, and what makes the extension unique.

The hypothesis is exactly connectedness of the groupoid when `C` is nonempty, but is stated as
the family of nonemptiness assertions `∀ x, Nonempty (x₀ ⟶ x)` rather than through
`CategoryTheory.IsConnected`: the intended source of that data is a path-connected topological
space, whose fundamental groupoid comes with paths from a chosen basepoint, and the equivalence
of the two formulations is not needed.

## Main declarations

* `TauCeti.Groupoid.natTrans_ext`: a natural transformation is determined by its component at the
  weakly initial object.
* `TauCeti.Groupoid.natIsoOfEnd`: an equivariant isomorphism of the values at a weakly initial
  object of a groupoid extends to a natural isomorphism.
* `TauCeti.Groupoid.natIsoOfEnd_app_self`: the extension restricts to the given isomorphism.
* `TauCeti.Groupoid.eq_natIsoOfEnd`: the extension is the only natural isomorphism doing so.
-/

public section
noncomputable section

universe t w v u

open CategoryTheory

namespace TauCeti.Groupoid

variable {C : Type u} [CategoryTheory.Groupoid.{v} C] {D : Type w} [Category.{t} D]
  {F G : C ⥤ D} {x₀ : C} (hconn : ∀ x : C, Nonempty (x₀ ⟶ x))

include hconn in
/-- A natural transformation between functors out of a groupoid is determined by its component at
a weakly initial object: restricting along `TauCeti.Groupoid.singleObjFunctor` is faithful. -/
theorem natTrans_ext {α β : F ⟶ G} (h : α.app x₀ = β.app x₀) : α = β := by
  have := isEquivalence_singleObjFunctor x₀ hconn
  refine ((Functor.whiskeringLeft _ _ D).obj (singleObjFunctor x₀)).map_injective ?_
  ext _
  exact h

include hconn in
/-- A natural isomorphism between functors out of a groupoid is determined by its component at
a weakly initial object. -/
theorem natIso_ext {α β : F ≅ G} (h : α.app x₀ = β.app x₀) : α = β :=
  Iso.ext (natTrans_ext hconn (by simpa using congrArg Iso.hom h))

/-- An `End x₀`-equivariant isomorphism between the values of two functors at a
weakly initial object of a groupoid extends to a natural isomorphism.

It is the preimage of the given isomorphism, read as a natural isomorphism of the restrictions
along `TauCeti.Groupoid.singleObjFunctor`, under the equivalence given by restriction. Its
component at `x₀` is the given isomorphism, by `natIsoOfEnd_app_self`. -/
def natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    F ≅ G :=
  haveI := isEquivalence_singleObjFunctor x₀ hconn
  ((Functor.whiskeringLeft _ _ D).obj (singleObjFunctor x₀)).preimageIso
    (NatIso.ofComponents (fun _ => e) fun g => he g)

/-- The extension of an equivariant isomorphism restricts to that isomorphism. -/
@[simp]
theorem natIsoOfEnd_app_self (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) :
    (natIsoOfEnd hconn e he).app x₀ = e := by
  have := isEquivalence_singleObjFunctor x₀ hconn
  refine Iso.ext ?_
  -- The restriction of the extension is the isomorphism it was built from, and restricting a
  -- natural transformation reads off its component at `x₀`.
  exact congrArg (fun α => NatTrans.app α (SingleObj.star (End x₀)))
    (((Functor.whiskeringLeft _ _ D).obj (singleObjFunctor x₀)).map_preimage
      (NatIso.ofComponents (fun _ => e) fun g => he g).hom)

/-- The extension is the only natural isomorphism restricting to the given one at the weakly
initial object. -/
theorem eq_natIsoOfEnd (e : F.obj x₀ ≅ G.obj x₀)
    (he : ∀ g : x₀ ⟶ x₀, F.map g ≫ e.hom = e.hom ≫ G.map g) (α : F ≅ G) (hα : α.app x₀ = e) :
    α = natIsoOfEnd hconn e he :=
  natIso_ext hconn (by rw [hα, natIsoOfEnd_app_self])

end TauCeti.Groupoid
