/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.MonodromyEquivalence
public import TauCeti.CategoryTheory.Action.Transitive
public import TauCeti.CategoryTheory.Groupoid.SingleObj

/-!
# Covering spaces are classified by fundamental-group sets

Let `X` be path connected, locally path connected and semilocally simply connected, and fix a
basepoint `x₀`. This file proves that taking the fibre over `x₀` with its monodromy action is an
equivalence of categories

  `TauCeti.CoveringSpace.fiberActionEquivalence :`
  `  CoveringSpace X ≌ Action (Type u) (FundamentalGroup X x₀)`,

that is, covering spaces of `X` are the same thing as sets with an action of `π₁(X, x₀)`. It
restricts to an equivalence

  `TauCeti.ConnectedCoveringSpace.transitiveFiberActionEquivalence :`
  `  ConnectedCoveringSpace X ≌ TransitiveAction (FundamentalGroup X x₀)`

between *connected* covers and *transitive* `π₁(X, x₀)`-sets.

This is the basepoint-based form of the classification. The basepoint-free form is already
available: `TauCeti.CoveringSpace.monodromyEquivalence` identifies covering spaces with functors
out of the fundamental groupoid. Passing from one to the other is pure category theory, and it
is where the hypotheses on `X` are spent a second time: path connectedness makes the fundamental
groupoid connected, and a connected groupoid is equivalent to the one-object category of its
vertex group by `TauCeti.Groupoid.singleObjEquivalence`. Precomposing a fundamental-groupoid
action with that equivalence, and reading a functor out of a one-object category as an action
through Mathlib's `CategoryTheory.Action.functorCategoryEquivalence`, gives the statement above.

No `ᵐᵒᵖ` intervenes. The vertex group of the fundamental groupoid at `x₀` *is* `π₁(X, x₀)`, since
Mathlib defines the latter as `End (FundamentalGroupoid.mk x₀)`, and the composition convention
of `CategoryTheory.SingleObj` is the one that matches `CategoryTheory.End`. The `ᵐᵒᵖ` in
`TauCeti.UniversalCover.deckFundamentalGroupEquiv` comes from comparing monodromy with *deck
transformations*, which is a different comparison and is unaffected.

The action recovered here is the monodromy action of `Mathlib/Topology/Homotopy/Lifting.lean`:
`fiberActionFunctor_obj_ρ_apply` and `fiberActionFunctor_obj_mulAction` record that the
categorical action on the fibre is `IsCoveringMap.fundamentalGroupMulAction`, and
`fiberActionFunctor_map_hom` records that a map of covers acts on fibres by restriction.

## Main declarations

* `TauCeti.CoveringSpace.fiberActionFunctor`: the functor sending a covering space to the fibre
  over `x₀` with its monodromy action of `π₁(X, x₀)`.
* `TauCeti.CoveringSpace.fiberActionFunctor_obj_V`,
  `TauCeti.CoveringSpace.fiberActionFunctor_obj_ρ_apply`,
  `TauCeti.CoveringSpace.fiberActionFunctor_obj_mulAction` and
  `TauCeti.CoveringSpace.fiberActionFunctor_map_hom`: its values.
* `TauCeti.CoveringSpace.fiberActionEquivalence`: **covering spaces of `X` are equivalent to
  `π₁(X, x₀)`-sets.**
* `TauCeti.ConnectedCoveringSpace.isTransitiveAction_fiberAction`: the `π₁(X, x₀)`-set attached to a
  connected cover is transitive, so the fibre-action functor restricts to a functor
  `TauCeti.ConnectedCoveringSpace.transitiveFiberActionFunctor` into
  `TauCeti.TransitiveAction (FundamentalGroup X x₀)`, with values given by
  `transitiveFiberActionFunctor_obj_obj` and `transitiveFiberActionFunctor_map_hom`.
* `TauCeti.ConnectedCoveringSpace.exists_fiberAction_iso`: every transitive `π₁(X, x₀)`-set is
  the fibre action of a connected cover.
* `TauCeti.ConnectedCoveringSpace.transitiveFiberActionEquivalence`: **connected covering spaces
  of `X` are equivalent to transitive `π₁(X, x₀)`-sets.**

## References

This is the `π₁(X)`-set form of the alternative lens on Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks to "phrase the classification of
connected covers via transitive `π₁(X)`-sets / the monodromy functor, with disconnected covers
as functors out of the fundamental groupoid"; see Hatcher, *Algebraic Topology*, Section 1.3. It
consumes the fundamental-groupoid classification of
`TauCeti.AlgebraicTopology.UniversalCover.Classification.MonodromyEquivalence`, the
stabiliser-cover reconstruction of
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Reconstruction`, which rests on the
based-path universal cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), and Mathlib's
`CategoryTheory.Action.functorCategoryEquivalence`; no Mathlib proof is vendored.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}} (x₀ : X)

/-- The functor taking a covering space of `X` to the fibre over `x₀`, equipped with the
monodromy action of `π₁(X, x₀)`.

It is assembled from the monodromy functor by restricting a fundamental-groupoid action along
the vertex-group inclusion `TauCeti.Groupoid.singleObjFunctor` and reading the result as an
action. It is `@[expose]`d so that its values hold by `rfl` in downstream modules. -/
@[expose] def fiberActionFunctor :
    CoveringSpace X ⥤ Action (Type u) (FundamentalGroup X x₀) :=
  monodromyFunctor X ⋙
    (Functor.whiskeringLeft _ _ _).obj (Groupoid.singleObjFunctor (FundamentalGroupoid.mk x₀)) ⋙
      Action.FunctorCategoryEquivalence.inverse

/-- The underlying set of the fundamental-group set attached to a cover is the fibre over the
basepoint. -/
@[simp]
theorem fiberActionFunctor_obj_V (p : CoveringSpace X) :
    ((fiberActionFunctor x₀).obj p).V = ↥(⇑p.proj ⁻¹' {x₀}) :=
  (rfl)

/-- A loop class acts on the fibre over the basepoint by monodromy. -/
@[simp]
theorem fiberActionFunctor_obj_ρ_apply (p : CoveringSpace X) (g : FundamentalGroup X x₀)
    (e : ⇑p.proj ⁻¹' {x₀}) :
    ((fiberActionFunctor x₀).obj p).ρ g e = p.isCoveringMap_proj.monodromy g e :=
  (rfl)

/-- The `MulAction` carried by the fundamental-group set attached to a cover is Mathlib's
monodromy action on the fibre. -/
theorem fiberActionFunctor_obj_mulAction (p : CoveringSpace X) :
    Action.instMulAction ((fiberActionFunctor x₀).obj p) =
      p.isCoveringMap_proj.fundamentalGroupMulAction x₀ :=
  (rfl)

/-- A map of covering spaces acts on the fibre over the basepoint by restriction. -/
@[simp]
theorem fiberActionFunctor_map_hom {p q : CoveringSpace X} (f : p ⟶ q) :
    ((fiberActionFunctor x₀).map f).hom =
      ↾(IsCoveringMap.fiberMap f.hom.left.hom (proj_hom_comp_hom_left_hom f) x₀) :=
  IsCoveringMap.monodromyNatTrans_app p.isCoveringMap_proj q.isCoveringMap_proj
    f.hom.left.hom (proj_hom_comp_hom_left_hom f) x₀

section Classification

variable [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The fibre-action functor is an equivalence: it is the composite of the monodromy equivalence,
restriction along the connected groupoid's vertex-group inclusion, and Mathlib's identification
of functors out of a one-object category with actions. -/
instance fiberActionFunctor_isEquivalence : (fiberActionFunctor x₀).IsEquivalence := by
  have := Groupoid.isEquivalence_singleObjFunctor (C := FundamentalGroupoid X)
    (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.nonempty_hom _)
  unfold fiberActionFunctor
  infer_instance

/-- **Covering spaces of `X` are equivalent to `π₁(X, x₀)`-sets.**

Over a path-connected, locally path-connected, semilocally simply connected base, taking the
fibre over `x₀` with its monodromy action is an equivalence of categories. -/
def fiberActionEquivalence : CoveringSpace X ≌ Action (Type u) (FundamentalGroup X x₀) :=
  (fiberActionFunctor x₀).asEquivalence

@[simp]
theorem fiberActionEquivalence_functor :
    (fiberActionEquivalence x₀).functor = fiberActionFunctor x₀ :=
  (rfl)

end Classification

end TauCeti.CoveringSpace

namespace TauCeti.ConnectedCoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

omit [SemilocallySimplyConnectedSpace X] in
/-- The fundamental-group set attached to a connected covering space is transitive. -/
theorem isTransitiveAction_fiberAction (p : ConnectedCoveringSpace X) :
    isTransitiveAction (FundamentalGroup X x₀)
      ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p)) :=
  (isTransitiveAction_iff _).mpr ⟨isPretransitive_fiberAction p x₀, nonempty_fiber p x₀⟩

/-- The fibre-action functor restricted to connected covering spaces and transitive
fundamental-group sets. -/
def transitiveFiberActionFunctor :
    ConnectedCoveringSpace X ⥤ TransitiveAction (FundamentalGroup X x₀) :=
  ObjectProperty.lift _ (forget X ⋙ CoveringSpace.fiberActionFunctor x₀)
    (isTransitiveAction_fiberAction x₀)

omit [SemilocallySimplyConnectedSpace X] in
/-- The underlying fundamental-group set of a connected cover is the one attached to it as a
cover. -/
@[simp]
theorem transitiveFiberActionFunctor_obj_obj (p : ConnectedCoveringSpace X) :
    ((transitiveFiberActionFunctor x₀).obj p).obj =
      (CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p) :=
  (rfl)

omit [SemilocallySimplyConnectedSpace X] in
/-- The underlying map of fundamental-group sets assigned to a map of connected covers is the one
assigned to it as a map of covers, hence restriction to the fibres over `x₀`. -/
@[simp]
theorem transitiveFiberActionFunctor_map_hom {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    ((transitiveFiberActionFunctor x₀).map f).hom =
      eqToHom (transitiveFiberActionFunctor_obj_obj x₀ p) ≫
        (CoveringSpace.fiberActionFunctor x₀).map ((forget X).map f) ≫
        eqToHom (transitiveFiberActionFunctor_obj_obj x₀ q).symm :=
  by
    convert ObjectProperty.ι_obj_lift_map (isTransitiveAction (FundamentalGroup X x₀))
        (forget X ⋙ CoveringSpace.fiberActionFunctor x₀) (isTransitiveAction_fiberAction x₀) f
      using 1 <;>
      rfl

instance transitiveFiberActionFunctor_faithful :
    (transitiveFiberActionFunctor x₀).Faithful :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Faithful

instance transitiveFiberActionFunctor_full : (transitiveFiberActionFunctor x₀).Full :=
  inferInstanceAs <| (ObjectProperty.lift _ _ _).Full

/-- **Every transitive `π₁(X, x₀)`-set is the fibre action of a connected cover.** The cover is
the quotient of the universal cover by the stabiliser of a point of the set. -/
theorem exists_fiberAction_iso (A : Action (Type u) (FundamentalGroup X x₀))
    (hA : isTransitiveAction (FundamentalGroup X x₀) A) :
    ∃ p : ConnectedCoveringSpace X,
      Nonempty ((CoveringSpace.fiberActionFunctor x₀).obj ((forget X).obj p) ≅ A) := by
  obtain ⟨htrans, ⟨a⟩⟩ := (isTransitiveAction_iff A).mp hA
  refine ⟨UniversalCover.stabilizerCover x₀ a, ⟨Action.mkIso
    (Equiv.toIso (UniversalCover.transitiveActionFiberEquiv x₀ a)) fun g => ?_⟩⟩
  refine ConcreteCategory.hom_ext _ _ fun e => ?_
  -- The cover has to be spelled out for the rewrite: the type of `e` mentions it only under the
  -- unfolding of `fiberActionFunctor`, so unification cannot read it off.
  rw [types_comp_apply, types_comp_apply, CoveringSpace.fiberActionFunctor_obj_ρ_apply x₀
    ((forget X).obj (UniversalCover.stabilizerCover x₀ a)) g e, ← smul_eq_ρ_apply A g]
  -- The one step left is `Equiv.toIso_hom_hom_apply`, which `rw` refuses here: the type of `e`
  -- is the `.V` projection rather than the fibre itself, so the rewritten target is not
  -- type-correct at `implicit` transparency.
  exact UniversalCover.transitiveActionFiberEquiv_apply_monodromy x₀ a g e

instance transitiveFiberActionFunctor_essSurj :
    (transitiveFiberActionFunctor x₀).EssSurj where
  mem_essImage A := by
    obtain ⟨p, ⟨e⟩⟩ := exists_fiberAction_iso x₀ A.obj (TransitiveAction.isTransitiveAction A)
    exact ⟨p, ⟨ObjectProperty.isoMk _ e⟩⟩

instance transitiveFiberActionFunctor_isEquivalence :
    (transitiveFiberActionFunctor x₀).IsEquivalence where

/-- **Connected covering spaces of `X` are equivalent to transitive `π₁(X, x₀)`-sets.** -/
def transitiveFiberActionEquivalence :
    ConnectedCoveringSpace X ≌ TransitiveAction (FundamentalGroup X x₀) :=
  (transitiveFiberActionFunctor x₀).asEquivalence

@[simp]
theorem transitiveFiberActionEquivalence_functor :
    (transitiveFiberActionEquivalence x₀).functor = transitiveFiberActionFunctor x₀ :=
  (rfl)

end TauCeti.ConnectedCoveringSpace
