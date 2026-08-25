/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Reconstruction
public import TauCeti.CategoryTheory.Groupoid.ConnectedFunctor
public import TauCeti.Topology.Covering.Monodromy.Transitive

/-!
# Covers are classified by fundamental-groupoid actions

Let `X` be path connected, locally path connected and semilocally simply connected. This file
proves that monodromy

  `TauCeti.ConnectedCoveringSpace.transitiveMonodromyFunctor X :`
  `  ConnectedCoveringSpace X ⥤ TransitiveFundamentalGroupoidAction X`

is an equivalence of categories. Full faithfulness is already available: it is the lifting
criterion, packaged in `TauCeti.Topology.Covering.Monodromy.Connected`. What is proved here is
essential surjectivity, which is the reconstruction of a cover from an action.

The reconstruction has two steps. A fibrewise transitive action `F` restricts at a basepoint
`x₀` to a transitive, nonempty action of `π₁(X, x₀)` on `F.obj x₀`; quotienting the universal
cover by the stabiliser of a point of that set produces a connected cover whose fibre over `x₀`
is equivariantly equivalent to `F.obj x₀`, which is
`TauCeti.UniversalCover.transitiveActionFiberEquiv`. That is an isomorphism of the two actions
at one object only. The second step upgrades it to a natural isomorphism of functors on the whole
fundamental groupoid, by `TauCeti.Groupoid.natIsoOfEnd`: a path from `x₀` transports the
equivalence to any other point, and the transported equivalence does not depend on the path
precisely because the two choices differ by a loop, on which equivariance applies.

Both hypotheses beyond local path-connectedness are used, and neither is an artefact. Path
connectedness makes the fundamental groupoid connected, which is what the transport needs, and it
is also what makes the fibres of a connected cover nonempty; semilocal simple connectedness is
what produces the universal cover the reconstruction quotients.

Dropping both restrictions — connectedness of the cover, transitivity of the action — gives the
classification of *all* covering spaces of `X` by *all* functors from its fundamental groupoid to
types. Full faithfulness is again the lifting criterion, already packaged in
`TauCeti.Topology.Covering.Monodromy.Basic` and `…Monodromy.Full`, and essential surjectivity is
again reconstruction at `x₀` followed by transport, but the cover reconstructed from an arbitrary
`π₁(X, x₀)`-set is the balanced product of
`TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover` rather than a quotient of
the universal cover by a stabiliser: the latter is connected, so it can only realise a transitive
action, while the former realises the disjoint union of one such quotient per orbit in one step.

## Main declarations

* `TauCeti.FundamentalGroupoidAction.basepointMulAction`: the action of `π₁(X, x₀)` on the value
  of a fundamental-groupoid action at `x₀`.
* `TauCeti.ConnectedCoveringSpace.exists_monodromyFunctor_iso`: every fibrewise transitive action
  is the monodromy of a connected cover.
* `TauCeti.ConnectedCoveringSpace.monodromyEquivalence`: **connected covering spaces of `X` are
  equivalent to transitive fundamental-groupoid actions.**
* `TauCeti.CoveringSpace.exists_monodromyFunctor_iso`: every fundamental-groupoid action is the
  monodromy of a covering space.
* `TauCeti.CoveringSpace.monodromyEquivalence`: **covering spaces of `X` are equivalent to
  functors from its fundamental groupoid to types.**

## References

This completes the alternative monodromy-functor lens on Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks for the classification of connected covers
by transitive `π₁(X)`-sets and of covers in general by functors out of the fundamental groupoid;
see Hatcher, *Algebraic Topology*, Section 1.3. It consumes the based-path universal cover
adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), the
stabiliser-cover reconstruction of
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Reconstruction`, and the balanced-product
cover of `TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover`.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace FundamentalGroupoidAction

variable {X : Type u} [TopologicalSpace X]

/-- The value of a fundamental-groupoid action at `x₀` carries an action of `π₁(X, x₀)`, the
vertex group of the fundamental groupoid at `x₀`. -/
@[instance_reducible]
def basepointMulAction (F : FundamentalGroupoid X ⥤ Type u) (x₀ : X) :
    MulAction (FundamentalGroup X x₀) (F.obj (FundamentalGroupoid.mk x₀)) where
  smul g a := F.map g a
  one_smul a := by
    have h : F.map (𝟙 (FundamentalGroupoid.mk x₀)) a = a := by
      rw [F.map_id, types_id_apply]
    exact h
  mul_smul g h a := F.map_comp_apply h g a

@[simp]
theorem basepointMulAction_smul (F : FundamentalGroupoid X ⥤ Type u) (x₀ : X)
    (g : FundamentalGroup X x₀) (a : F.obj (FundamentalGroupoid.mk x₀)) :
    letI := basepointMulAction F x₀
    g • a = F.map g a :=
  (rfl)

end FundamentalGroupoidAction

namespace ConnectedCoveringSpace

variable {X : TopCat.{u}} [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- **Every fibrewise transitive fundamental-groupoid action is the monodromy of a connected
covering space.** The cover is the quotient of the universal cover by the stabiliser of a point
in the value of the action at a basepoint. -/
theorem exists_monodromyFunctor_iso (F : FundamentalGroupoid X ⥤ Type u)
    (hF : FundamentalGroupoidAction.isFiberwiseTransitive X F) :
    ∃ p : ConnectedCoveringSpace X,
      Nonempty ((CoveringSpace.monodromyFunctor X).obj ((forget X).obj p) ≅ F) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (X : Type u))
  have hpre := FundamentalGroupoidAction.isFiberwisePretransitive_of_isFiberwiseTransitive hF
  rw [FundamentalGroupoidAction.isFiberwisePretransitive_iff] at hpre
  let _ := FundamentalGroupoidAction.basepointMulAction F x₀
  have : MulAction.IsPretransitive (FundamentalGroup X x₀)
      (F.obj (FundamentalGroupoid.mk x₀)) :=
    ⟨fun a b => hpre (FundamentalGroupoid.mk x₀) a b⟩
  obtain ⟨a⟩ :=
    FundamentalGroupoidAction.nonempty_of_isFiberwiseTransitive hF (FundamentalGroupoid.mk x₀)
  refine ⟨UniversalCover.stabilizerCover x₀ a, ⟨?_⟩⟩
  refine eqToIso (CoveringSpace.monodromyFunctor_obj _) ≪≫
    TauCeti.Groupoid.natIsoOfEnd
      (FundamentalGroupoid.nonempty_hom (FundamentalGroupoid.mk x₀))
      (UniversalCover.transitiveActionFiberEquiv x₀ a).toIso (fun g => ?_)
  refine ConcreteCategory.hom_ext _ _ fun z => ?_
  simp only [types_comp_apply]
  exact UniversalCover.transitiveActionFiberEquiv_apply_monodromy x₀ a g z

/-- Transitive connected-cover monodromy is essentially surjective. -/
instance transitiveMonodromyFunctor_essSurj :
    (transitiveMonodromyFunctor X).EssSurj where
  mem_essImage G := by
    obtain ⟨p, ⟨e⟩⟩ := exists_monodromyFunctor_iso G.obj G.property
    exact ⟨p, ⟨ObjectProperty.isoMk _ (eqToIso (transitiveMonodromyFunctor_obj_obj p) ≪≫ e)⟩⟩

/-- Transitive connected-cover monodromy is fully faithful and essentially surjective. -/
instance transitiveMonodromyFunctor_isEquivalence :
    (transitiveMonodromyFunctor X).IsEquivalence where

/-- **The classification of connected covering spaces by transitive fundamental-groupoid
actions.** Over a path-connected, locally path-connected, semilocally simply connected base,
monodromy is an equivalence from connected covering spaces to fibrewise transitive actions of
the fundamental groupoid. -/
def monodromyEquivalence (X : TopCat.{u}) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    ConnectedCoveringSpace X ≌ TransitiveFundamentalGroupoidAction X :=
  (transitiveMonodromyFunctor X).asEquivalence

@[simp]
theorem monodromyEquivalence_functor (X : TopCat.{u}) [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (monodromyEquivalence X).functor = transitiveMonodromyFunctor X :=
  (rfl)

end ConnectedCoveringSpace

namespace CoveringSpace

variable {X : TopCat.{u}} [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- **Every fundamental-groupoid action is the monodromy of a covering space.** The cover is the
balanced product of the universal cover with the value of the action at a basepoint. -/
theorem exists_monodromyFunctor_iso (F : FundamentalGroupoid X ⥤ Type u) :
    ∃ p : CoveringSpace X, Nonempty ((monodromyFunctor X).obj p ≅ F) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (X : Type u))
  let _ := FundamentalGroupoidAction.basepointMulAction F x₀
  let _ : TopologicalSpace (F.obj (FundamentalGroupoid.mk x₀)) := ⊥
  have : DiscreteTopology (F.obj (FundamentalGroupoid.mk x₀)) := ⟨rfl⟩
  refine ⟨UniversalCover.actionCoveringSpace x₀ (F.obj (FundamentalGroupoid.mk x₀)), ⟨?_⟩⟩
  refine eqToIso (monodromyFunctor_obj _) ≪≫
    TauCeti.Groupoid.natIsoOfEnd
      (FundamentalGroupoid.nonempty_hom (FundamentalGroupoid.mk x₀))
      (UniversalCover.actionCoveringSpaceFiberEquiv x₀
        (F.obj (FundamentalGroupoid.mk x₀))).toIso (fun g => ?_)
  refine ConcreteCategory.hom_ext _ _ fun z => ?_
  simp only [types_comp_apply]
  exact UniversalCover.actionCoveringSpaceFiberEquiv_apply_monodromy x₀
    (F.obj (FundamentalGroupoid.mk x₀)) g z

/-- Covering-space monodromy is essentially surjective. -/
instance monodromyFunctor_essSurj : (monodromyFunctor X).EssSurj where
  mem_essImage F := exists_monodromyFunctor_iso F

/-- Covering-space monodromy is fully faithful and essentially surjective. -/
instance monodromyFunctor_isEquivalence : (monodromyFunctor X).IsEquivalence where

/-- **The classification of covering spaces by fundamental-groupoid actions.** Over a
path-connected, locally path-connected, semilocally simply connected base, monodromy is an
equivalence from covering spaces to functors from the fundamental groupoid to types. -/
def monodromyEquivalence (X : TopCat.{u}) [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    CoveringSpace X ≌ (FundamentalGroupoid X ⥤ Type u) :=
  (monodromyFunctor X).asEquivalence

@[simp]
theorem monodromyEquivalence_functor (X : TopCat.{u}) [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (monodromyEquivalence X).functor = monodromyFunctor X :=
  (rfl)

end CoveringSpace

end TauCeti
