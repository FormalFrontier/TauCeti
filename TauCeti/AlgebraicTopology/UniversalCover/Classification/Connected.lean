/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.FundamentalGroupAction
public import TauCeti.CategoryTheory.Action.Connected
public import TauCeti.CategoryTheory.Galois.Connected

/-!
# Connected covering spaces are the categorically connected ones

Let `X` be path connected, locally path connected and semilocally simply connected. Covering
spaces of `X` carry two unrelated-looking notions of connectedness: the topological one, that the
total space is a `ConnectedSpace`, and the categorical one,
`CategoryTheory.PreGaloisCategory.IsConnected`, which asks that the cover is not an initial object
of `TauCeti.CoveringSpace X` and has no nontrivial subobject there. This file proves that they
agree.

The bridge is the classification of covers by `π₁(X, x₀)`-sets. Categorical connectedness is
invariant under an equivalence of categories (`TauCeti.isConnected_map_iff`), so it can be read off
on the other side of `TauCeti.CoveringSpace.fiberActionEquivalence`, where it says exactly that the
monodromy action on the fibre over `x₀` is transitive and nonempty
(`TauCeti.isConnected_action_iff_isTransitiveAction`). That in turn is the condition already known
to characterise connected covers: transitivity of monodromy is
`TauCeti.ConnectedCoveringSpace.isTransitiveAction_fiberAction`, and conversely a cover with
transitive monodromy has path-connected total space, because path lifting joins every point of the
total space to a point of the fibre over `x₀` and monodromy joins any two points of that fibre.
That converse needs no hypothesis on `X` beyond path connectedness, so the dictionary between
transitive monodromy and a connected total space is established before the classification is
invoked; only the passage to the categorical statement uses the full standing hypotheses.

The initial objects of `TauCeti.CoveringSpace X` play no special role here: they are the covers
with empty total space over any base, which is
`TauCeti.CoveringSpace.isInitial_iff_isEmpty` in the general covering-space API.

## Main declarations

* `TauCeti.CoveringSpace.isTransitiveAction_fiberAction_iff_connectedSpace`: the monodromy action
  on the fibre over `x₀` is transitive exactly when the total space is connected.
* `TauCeti.CoveringSpace.isConnected_iff_connectedSpace`: **a covering space of `X` is a connected
  object of `TauCeti.CoveringSpace X` exactly when its total space is a connected space.**
* `TauCeti.ConnectedCoveringSpace.isConnected_forget_obj`: a connected covering space is a
  connected object of `TauCeti.CoveringSpace X`.

## References

This is the connectedness dictionary for the alternative lens of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`. It consumes the classification of covers by
`π₁(X, x₀)`-sets and Mathlib's `CategoryTheory.PreGaloisCategory.IsConnected`; no Mathlib proof is
vendored.
-/

public section
noncomputable section

open CategoryTheory Limits Topology

universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}} (x₀ : X) [PathConnectedSpace X] [LocallyPathConnectedSpace X]

/-- The monodromy action of `π₁(X, x₀)` on the fibre of a covering space over `x₀` is transitive
exactly when the total space of that cover is connected.

This is deliberately not `@[simp]`: `TauCeti.isTransitiveAction_iff` is already a simp lemma, so
the left-hand side is not in simp normal form and `simpNF` rejects the attribute. -/
theorem isTransitiveAction_fiberAction_iff_connectedSpace (p : CoveringSpace X) :
    isTransitiveAction (FundamentalGroup X x₀) ((fiberActionFunctor x₀).obj p) ↔
      ConnectedSpace (p : TopCat) := by
  constructor
  · intro h
    obtain ⟨htrans, ⟨e₀⟩⟩ := (isTransitiveAction_iff _).mp h
    have hjoin {a b : (p : TopCat)} (q : Path.Homotopic.Quotient a b) : Joined a b := by
      induction q using Path.Homotopic.Quotient.ind with
      | mk γ => exact ⟨γ⟩
    -- Path lifting joins every point of the total space to a point of the fibre over `x₀`.
    have key (e : (p : TopCat)) : ∃ f : ⇑p.proj ⁻¹' {x₀}, Joined e (f : (p : TopCat)) :=
      ⟨_, hjoin (p.isCoveringMap_proj.liftPathQuotient
        (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (p.proj e) x₀)) ⟨e, rfl⟩)⟩
    -- Transitivity of the monodromy action joins any two points of that fibre.
    have hfib (f f' : ⇑p.proj ⁻¹' {x₀}) : Joined (f : (p : TopCat)) (f' : (p : TopCat)) := by
      obtain ⟨g, hg⟩ := htrans.exists_smul_eq f f'
      have hg' : (p.isCoveringMap_proj.monodromy g.toPath f : (p : TopCat)) = f' :=
        congrArg Subtype.val hg
      have := hjoin (p.isCoveringMap_proj.liftPathQuotient g.toPath f)
      rwa [hg'] at this
    have : PathConnectedSpace (p : TopCat) := by
      refine ⟨⟨(e₀ : ⇑p.proj ⁻¹' {x₀}).1⟩, fun a b => ?_⟩
      obtain ⟨f, hf⟩ := key a
      obtain ⟨f', hf'⟩ := key b
      exact (hf.trans (hfib f f')).trans hf'.symm
    infer_instance
  · intro h
    exact ConnectedCoveringSpace.isTransitiveAction_fiberAction x₀
      (⟨p.obj, ⟨p.property, h⟩⟩ : ConnectedCoveringSpace X)

variable [SemilocallySimplyConnectedSpace X]

/-- **A covering space of `X` is a connected object of `TauCeti.CoveringSpace X` exactly when its
total space is a connected space.** -/
@[simp]
theorem isConnected_iff_connectedSpace (p : CoveringSpace X) :
    PreGaloisCategory.IsConnected p ↔ ConnectedSpace (p : TopCat) := by
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := (X : Type u))
  exact ((isConnected_map_iff (fiberActionFunctor x₀) p).symm.trans
      (isConnected_action_iff_isTransitiveAction _)).trans
    (isTransitiveAction_fiberAction_iff_connectedSpace x₀ p)

end TauCeti.CoveringSpace

namespace TauCeti.ConnectedCoveringSpace

variable {X : TopCat.{u}} [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- A connected covering space is a connected object of `TauCeti.CoveringSpace X`. -/
theorem isConnected_forget_obj (p : ConnectedCoveringSpace X) :
    PreGaloisCategory.IsConnected ((forget X).obj p) :=
  (CoveringSpace.isConnected_iff_connectedSpace ((forget X).obj p)).mpr p.property.2

end TauCeti.ConnectedCoveringSpace

end
