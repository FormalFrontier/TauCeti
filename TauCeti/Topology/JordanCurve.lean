/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Jordan curves

A **Jordan curve** — a simple closed curve — is a subset of a topological space homeomorphic to
the circle. This file introduces the predicate `TauCeti.IsJordanCurve` and its basic API.

The circle is Mathlib's `Circle`, the unit circle of `ℂ` as a topological group; the notion itself
is purely topological, so `TauCeti.IsJordanCurve` is stated for a subset of an arbitrary
topological space, and only the model curve is complex-analytic.

Phrasing the predicate as *the set is homeomorphic to the circle*, rather than *the set is the
range of a continuous map on `[0, 1]` that is injective except for matching endpoints*, is what
makes it usable: the two agree, because a continuous injection out of a compact space into a
Hausdorff space is an embedding, but the parametrized form buries that argument in every use. It is
recovered where needed from `TauCeti.IsJordanCurve.of_image`, which says exactly that a compact set
carried injectively and continuously onto a Jordan curve is itself one.

## Main definitions

* `TauCeti.IsJordanCurve` — a set homeomorphic to the circle.

## Main results

* `TauCeti.IsJordanCurve.isCompact`, `TauCeti.IsJordanCurve.isPathConnected`,
  `TauCeti.IsJordanCurve.nonempty` and `TauCeti.IsJordanCurve.not_subsingleton` — a Jordan curve is
  a nonempty compact path-connected set with more than one point.
* `TauCeti.IsJordanCurve.image` and `TauCeti.IsJordanCurve.of_image` — being a Jordan curve
  transfers in both directions along a map that is continuous and injective on the set, provided
  the codomain is Hausdorff (and, in the direction that creates the curve out of nothing, the
  source set is known to be compact).
* `TauCeti.IsJordanCurve.image_homeomorph` — the image of a Jordan curve under a homeomorphism of
  the ambient spaces is a Jordan curve; no separation axiom is needed.

## Motivation

This is the vocabulary layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) is stated in: its milestone, the Carathéodory
boundary correspondence, is about the Riemann map of a *Jordan domain*, and the roadmap records
that the pinned Mathlib has no Jordan-curve vocabulary to state it against. The complex-analytic
half — Jordan domains, the circle as the boundary of a disc, and the boundary of a domain that a
conformal map carries onto a disc — is in
`TauCeti/Analysis/Complex/Conformal/JordanDomain.lean`.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 3 (1887).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C : Set X}

/-- A **Jordan curve**, or simple closed curve, in a topological space: a subset homeomorphic to
the circle.

The predicate is `Nonempty (C ≃ₜ Circle)` rather than a chosen homeomorphism, so that it is a
`Prop`; `TauCeti.isJordanCurve_iff` recovers the homeomorphism from another module, where the
definition itself is not exposed. -/
def IsJordanCurve (C : Set X) : Prop := Nonempty (C ≃ₜ Circle)

/-- A set is a Jordan curve exactly when it is homeomorphic to the circle. This is the interface
to `TauCeti.IsJordanCurve` outside its defining module. -/
theorem isJordanCurve_iff : IsJordanCurve C ↔ Nonempty (C ≃ₜ Circle) := Iff.rfl

/-- A continuous injection defined on a compact set is a homeomorphism onto its image, the image
carrying the subspace topology of a Hausdorff space. This is the set-level form of
`Continuous.homeoOfEquivCompactToT2`, and the engine of both transfer lemmas below. -/
private noncomputable def imageHomeomorphOfIsCompact [T2Space Y] (hC : IsCompact C) {g : X → Y}
    (hg : ContinuousOn g C) (hgi : InjOn g C) : C ≃ₜ g '' C :=
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  Continuous.homeoOfEquivCompactToT2 (f := hgi.bijOn_image.equiv g)
    (hg.mapsToRestrict hgi.bijOn_image.mapsTo)

/-- A Jordan curve is compact: the circle is. -/
theorem IsJordanCurve.isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨e⟩ := h
  exact isCompact_iff_compactSpace.mpr e.symm.compactSpace

/-- A Jordan curve in a Hausdorff space is closed. -/
theorem IsJordanCurve.isClosed [T2Space X] (h : IsJordanCurve C) : IsClosed C :=
  h.isCompact.isClosed

/-- A Jordan curve is path connected: the circle is. -/
theorem IsJordanCurve.isPathConnected (h : IsJordanCurve C) : IsPathConnected C := by
  obtain ⟨e⟩ := h
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (e.symm.surjective.pathConnectedSpace e.symm.continuous)

/-- A Jordan curve is connected. -/
theorem IsJordanCurve.isConnected (h : IsJordanCurve C) : IsConnected C :=
  h.isPathConnected.isConnected

/-- A Jordan curve is nonempty. -/
theorem IsJordanCurve.nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

/-- A Jordan curve has more than one point: the circle contains both `1` and `-1`. Together with
`TauCeti.IsJordanCurve.isConnected` this rules out the degenerate curves, so a Jordan curve is a
nondegenerate continuum. -/
theorem IsJordanCurve.not_subsingleton (h : IsJordanCurve C) : ¬ C.Subsingleton := by
  obtain ⟨e⟩ := h
  intro hsub
  exact Circle.neg_ne_self 1
    (e.symm.injective (Subtype.ext (hsub (e.symm (-1)).2 (e.symm 1).2)))

/-- **A Jordan curve is carried to a Jordan curve by a continuous injection.** Only continuity and
injectivity *on the curve* are needed, the curve supplying the compactness that upgrades them to a
homeomorphism onto the image. -/
theorem IsJordanCurve.image [T2Space Y] (h : IsJordanCurve C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) : IsJordanCurve (g '' C) := by
  have hC := h.isCompact
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).symm.trans e⟩

/-- **A compact set carried onto a Jordan curve by a continuous injection is a Jordan curve.**
This is the converse of `TauCeti.IsJordanCurve.image`; compactness of the source has to be assumed
here, since it is no longer inherited from the curve. It is the form in which the predicate is
usually verified: one exhibits a continuous injective parametrization or, as in the boundary
correspondence, a continuous injective map of the set onto a circle. -/
theorem IsJordanCurve.of_image [T2Space Y] (hC : IsCompact C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) (h : IsJordanCurve (g '' C)) : IsJordanCurve C := by
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).trans e⟩

/-- The image of a Jordan curve under a homeomorphism of the ambient spaces is a Jordan curve.
Unlike `TauCeti.IsJordanCurve.image` this needs no separation axiom on the codomain, because
`Homeomorph.image` supplies the homeomorphism onto the image outright. -/
theorem IsJordanCurve.image_homeomorph (h : IsJordanCurve C) (e : X ≃ₜ Y) :
    IsJordanCurve (e '' C) := by
  obtain ⟨f⟩ := h
  exact ⟨(e.image C).symm.trans f⟩

end TauCeti
