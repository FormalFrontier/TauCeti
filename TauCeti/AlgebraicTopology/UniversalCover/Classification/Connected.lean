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
`TauCeti.ConnectedCoveringSpace.isTransitiveAction_fiberAction`, and conversely a cover realising a
transitive action is isomorphic to a connected one by
`TauCeti.ConnectedCoveringSpace.exists_fiberAction_iso`, hence has homeomorphic total space.

The only topology used is path lifting, through `TauCeti.CoveringSpace.nonempty_fiber`: the
initial objects of `TauCeti.CoveringSpace X` are the covers with empty total space, and to read
that off the fibre over `x₀` one needs a nonempty cover to have a nonempty fibre. Everything else
is the transport of a categorical condition along an already-established equivalence. The
statement is what lets the Galois-theoretic vocabulary — connected objects, and the Galois
correspondence phrased through them — be used on covering spaces.

## Main declarations

* `TauCeti.CoveringSpace.isTransitiveAction_fiberAction_iff_connectedSpace`: the monodromy action
  on the fibre over `x₀` is transitive exactly when the total space is connected.
* `TauCeti.CoveringSpace.isInitial_iff_isEmpty`: a covering space is an initial object exactly
  when its total space is empty.
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
  [SemilocallySimplyConnectedSpace X]

/-- The monodromy action of `π₁(X, x₀)` on the fibre of a covering space over `x₀` is transitive
exactly when the total space of that cover is connected. -/
theorem isTransitiveAction_fiberAction_iff_connectedSpace (p : CoveringSpace X) :
    isTransitiveAction (FundamentalGroup X x₀) ((fiberActionFunctor x₀).obj p) ↔
      ConnectedSpace (p : TopCat) := by
  constructor
  · intro h
    obtain ⟨q, ⟨e⟩⟩ :=
      ConnectedCoveringSpace.exists_fiberAction_iso x₀ ((fiberActionFunctor x₀).obj p) h
    have hq : ConnectedSpace ((totalSpace X).obj ((ConnectedCoveringSpace.forget X).obj q)) :=
      q.property.2
    exact (TopCat.homeoOfIso
      ((totalSpace X).mapIso ((fiberActionFunctor x₀).preimageIso e))).connectedSpace_iff.mp hq
  · intro h
    exact ConnectedCoveringSpace.isTransitiveAction_fiberAction x₀
      (⟨p.obj, ⟨p.property, h⟩⟩ : ConnectedCoveringSpace X)

/-- **A covering space of `X` is an initial object of `TauCeti.CoveringSpace X` exactly when its
total space is empty.** The empty cover is therefore the initial object, and a cover is
"non-initial" in the sense of the definition of a connected object exactly when it is nonempty. -/
theorem isInitial_iff_isEmpty (p : CoveringSpace X) :
    Nonempty (IsInitial p) ↔ IsEmpty (p : TopCat) := by
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := (X : Type u))
  constructor
  · rintro ⟨h⟩
    have hf : IsEmpty (ToType ((fiberActionFunctor x₀).obj p)) :=
      isEmpty_of_isInitial_action (h.isInitialObj (fiberActionFunctor x₀) p)
    by_contra hne
    exact hf.elim (nonempty_fiber p (not_isEmpty_iff.mp hne) x₀).some
  · intro h
    exact ⟨isInitialOfIsInitialObj (fiberActionFunctor x₀)
      (isInitialActionOfIsEmpty (A := (fiberActionFunctor x₀).obj p) ⟨fun a => h.elim a.1⟩)⟩

/-- **A covering space of `X` is a connected object of `TauCeti.CoveringSpace X` exactly when its
total space is a connected space.** -/
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
