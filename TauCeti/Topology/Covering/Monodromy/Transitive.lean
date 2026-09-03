/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Monodromy.Connected

/-!
# Monodromy of connected covers over a path-connected base

Over a path-connected base the fibres of a connected covering space are nonempty, so its
monodromy action is *transitive* on each fibre and not merely pretransitive. This file records
that strengthening and lifts the monodromy functor of connected covers to the full subcategory
of fibrewise transitive fundamental-groupoid actions.

The distinction is not cosmetic. Over a base with several path components a connected cover has
its image in one of them, so its fibres over the other components are empty, which is why
`TauCeti.FundamentalGroupoidAction.isFiberwisePretransitive` is the right condition there and is
what `TauCeti.ConnectedCoveringSpace.monodromyFunctor` is stated against. Once the base is path
connected the empty action drops out of the essential image, and it has to: the empty action is
fibrewise pretransitive, while `TauCeti.ConnectedCoveringSpace` carries `ConnectedSpace` and so
has a nonempty total space. Transitivity is therefore exactly the extra condition that makes
monodromy an equivalence onto the actions, which is proved in
`TauCeti.AlgebraicTopology.UniversalCover.Classification.MonodromyEquivalence`.

## Main declarations

* `TauCeti.FundamentalGroupoidAction.isFiberwiseTransitive`: fibrewise pretransitive with
  nonempty fibres.
* `TauCeti.TransitiveFundamentalGroupoidAction`: the corresponding full subcategory.
* `TauCeti.ConnectedCoveringSpace.nonempty_fiber`: over a path-connected base every fibre of a
  connected cover is nonempty.
* `TauCeti.ConnectedCoveringSpace.transitiveMonodromyFunctor`: monodromy of connected covers,
  valued in fibrewise transitive actions.

## References

This is the connected/transitive restriction in Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks for the classification of connected covers
by *transitive* fundamental-group sets. It builds on the fibrewise pretransitive packaging in
`TauCeti.Topology.Covering.Monodromy.Connected`.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace FundamentalGroupoidAction

variable (X : TopCat.{u})

/-- A fundamental-groupoid action is fibrewise nonempty if every fibre is nonempty. -/
def isFiberwiseNonempty : ObjectProperty (FundamentalGroupoid X ⥤ Type u) :=
  fun F => ∀ x : FundamentalGroupoid X, Nonempty (F.obj x)

/-- A fundamental-groupoid action is fibrewise transitive if it is fibrewise pretransitive with
nonempty fibres. -/
def isFiberwiseTransitive : ObjectProperty (FundamentalGroupoid X ⥤ Type u) :=
  isFiberwisePretransitive X ⊓ isFiberwiseNonempty X

variable {X}

/-- Membership in the fibrewise transitive fundamental-groupoid action property. -/
@[simp]
theorem isFiberwiseTransitive_iff (F : FundamentalGroupoid X ⥤ Type u) :
    isFiberwiseTransitive X F ↔
      isFiberwisePretransitive X F ∧ ∀ x : FundamentalGroupoid X, Nonempty (F.obj x) :=
  Iff.rfl

/-- A fibrewise transitive action is fibrewise pretransitive. -/
theorem isFiberwisePretransitive_of_isFiberwiseTransitive
    {F : FundamentalGroupoid X ⥤ Type u} (hF : isFiberwiseTransitive X F) :
    isFiberwisePretransitive X F :=
  hF.1

/-- Every fibre of a fibrewise transitive action is nonempty. -/
theorem nonempty_of_isFiberwiseTransitive {F : FundamentalGroupoid X ⥤ Type u}
    (hF : isFiberwiseTransitive X F) (x : FundamentalGroupoid X) : Nonempty (F.obj x) :=
  hF.2 x

variable (X)

/-- Fibrewise transitivity is stronger than fibrewise pretransitivity. -/
theorem isFiberwiseTransitive_le : isFiberwiseTransitive X ≤ isFiberwisePretransitive X :=
  inf_le_left

/-- Fibrewise nonemptiness is preserved by natural isomorphisms of actions. -/
instance : (isFiberwiseNonempty X).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro F G e hF x
    exact ⟨e.hom.app x (hF x).some⟩

/-- Fibrewise transitivity is preserved by natural isomorphisms of actions. -/
instance : (isFiberwiseTransitive X).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro F G e hF
    exact ⟨ObjectProperty.prop_of_iso _ e hF.1, ObjectProperty.prop_of_iso _ e hF.2⟩

end FundamentalGroupoidAction

/-- Fundamental-groupoid actions that are transitive on every fibre. Morphisms are arbitrary
natural transformations between the underlying functors. -/
abbrev TransitiveFundamentalGroupoidAction (X : TopCat.{u}) : Type _ :=
  (FundamentalGroupoidAction.isFiberwiseTransitive X).FullSubcategory

namespace TransitiveFundamentalGroupoidAction

variable {X : TopCat.{u}}

/-- The fully faithful inclusion into fibrewise pretransitive actions. -/
abbrev forget (X : TopCat.{u}) :
    TransitiveFundamentalGroupoidAction X ⥤ PretransitiveFundamentalGroupoidAction X :=
  ObjectProperty.ιOfLE (FundamentalGroupoidAction.isFiberwiseTransitive_le X)

/-- Construct a fibrewise transitive action from an action and a proof of fibrewise
transitivity. -/
def mk (F : FundamentalGroupoid X ⥤ Type u)
    (hF : FundamentalGroupoidAction.isFiberwiseTransitive X F) :
    TransitiveFundamentalGroupoidAction X :=
  ⟨F, hF⟩

/-- The underlying action of a fibrewise transitive action is fibrewise transitive. -/
theorem isFiberwiseTransitive (F : TransitiveFundamentalGroupoidAction X) :
    FundamentalGroupoidAction.isFiberwiseTransitive X F.obj :=
  F.property

/-- The inclusion into fibrewise pretransitive actions is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

end TransitiveFundamentalGroupoidAction

namespace ConnectedCoveringSpace

variable {X : TopCat.{u}}

/-- Over a path-connected base, every fibre of a connected covering space is nonempty: a chosen
point of the total space is carried into the fibre by monodromy along any path. -/
theorem nonempty_fiber [PathConnectedSpace X] (p : ConnectedCoveringSpace X) (x : X) :
    Nonempty (⇑p.proj ⁻¹' {x}) := by
  obtain ⟨e⟩ := (inferInstance : Nonempty (p : TopCat))
  exact ⟨p.isCoveringMap_proj.monodromy
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (p.proj e) x)) ⟨e, rfl⟩⟩

/-- The ordinary monodromy functor of a connected cover over a path-connected base is transitive
on every fibre. -/
theorem monodromy_isFiberwiseTransitive [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    (p : ConnectedCoveringSpace X) :
    FundamentalGroupoidAction.isFiberwiseTransitive X
      ((CoveringSpace.monodromyFunctor X).obj ((forget X).obj p)) :=
  ⟨monodromy_isFiberwisePretransitive p, by
    intro x
    rw [CoveringSpace.monodromyFunctor_obj]
    rcases x with ⟨x⟩
    exact nonempty_fiber p x⟩

/-- Monodromy as a functor from connected covering spaces over a path-connected base to fibrewise
transitive fundamental-groupoid actions. -/
def transitiveMonodromyFunctor (X : TopCat.{u}) [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] :
    ConnectedCoveringSpace X ⥤ TransitiveFundamentalGroupoidAction X :=
  ObjectProperty.lift _ (forget X ⋙ CoveringSpace.monodromyFunctor X)
    monodromy_isFiberwiseTransitive

/-- The underlying action of transitive connected-cover monodromy is the ordinary monodromy
action. -/
@[simp]
theorem transitiveMonodromyFunctor_obj_obj [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    (p : ConnectedCoveringSpace X) :
    ((transitiveMonodromyFunctor X).obj p).obj =
      (CoveringSpace.monodromyFunctor X).obj ((forget X).obj p) :=
  (rfl)

/-- Transitive connected-cover monodromy is faithful. -/
instance transitiveMonodromyFunctor_faithful [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] : (transitiveMonodromyFunctor X).Faithful :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Faithful

/-- Transitive connected-cover monodromy is full. -/
instance transitiveMonodromyFunctor_full [LocallyPathConnectedSpace X] [PathConnectedSpace X] :
    (transitiveMonodromyFunctor X).Full :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Full

end ConnectedCoveringSpace

end TauCeti
