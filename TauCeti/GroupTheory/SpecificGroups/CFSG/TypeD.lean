/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Closure

/-!
# The ambient group of the families on a type-`D` diagram

Three classification-list families are built on the diagram `Dₙ`: the untwisted `Dₙ(q)`, the
graph-twisted `²Dₙ(q)`, and, at rank four, the triality-twisted `³D₄(q)`. They share a diagram, so
they share a carrier, and `TauCeti.TypeDDiagramLieIndex` is the subtype that collects exactly them.
This file attaches to such an index the group of algebraic-closure-valued points of Tau Ceti's
explicit full-weight type-`D` spin Chevalley carrier at the index's own rank,
`TauCeti.TypeDSpinCarrier.points`.

The rank is available because it is at least four on this subtype, by
`TauCeti.TypeDDiagramLieIndex.four_le_rank`, which is exactly the hypothesis the carrier takes: the
carrier is built from the type-`Dₙ` Serre presentation, whose diagram is `A₁ × A₁` at rank two and
`A₃` at rank three, so it is offered only in the range where `Dₙ` is a valid Dynkin type.

The spin carrier rather than the Geck carrier is used because the Geck carrier is built from the
adjoint representation, so its weights span the whole character lattice exactly in the types `E₈`,
`F₄` and `G₂`, by `TauCeti.DynkinType.span_range_geckWeight_eq_top_iff`. A type-`D` diagram is not
one of those, by `TauCeti.LieTypeIndex.not_hasUnimodularDiagram_of_hasTypeDDiagram`, and the full
spin representation is what sees both spinor cosets of the type-`D` root lattice; its weights span
that lattice, by `TauCeti.TypeDSpinCarrier.span_range_basisWeight_eq_top`.

What is *not* here is the Steinberg map, and hence not the finite-group candidate either. On these
three branches the Steinberg map is `γ ∘ Frob_q` for the diagram permutation the index carries,
which is the identity on `Dₙ(q)`, the fork exchange on `²Dₙ(q)` and triality on `³D₄(q)`. Both
factors are point-level data that the carrier does not yet carry, and both have their pinning
equations stated against its numbered root subgroups on matrix points, which it does not yet carry
either. Neither map is formed until those exist, which is the same point at which
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeB2.lean` stops for the Suzuki family.

Nothing here asserts that the spin carrier is reductive, that its weight torus is maximal, or that
any group below is finite, perfect, or simple.

## Main declaration

* `TauCeti.TypeDDiagramLieIndex.AmbientGroup`: the algebraic-closure-valued points of the
  full-weight type-`D` spin carrier at the rank the index names, the group the classification
  recipe will be run inside on all three type-`D` branches.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the spin representation the
  carrier is built from.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 14.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV, for the numbering of the
  `Dₙ` diagram that the index's rank and diagram permutation are read in.
* The target signature realized here follows the human-authored formal skeleton
  `TauCetiRoadmap/CFSGStatement/Suggested.lean`, whose `ValidLieTypeIndex.AmbientGroup` is taken on
  a validated-index subtype.

## Roadmap

Milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for the points of the *pinned* simply
connected Chevalley--Demazure group scheme of `TauCeti.DynkinType.simplyConnectedRootDatum` at the
diagram the index names, with its root subgroups. **This file does not close L0 on the three
type-`D` branches, and the spin carrier is not offered as a substitute for that pinned group.** The
pinned group scheme, its pinning, and any identification of a carrier with it are Layer 9 targets
of `TauCetiRoadmap/ReductiveGroups/README.md` that the CFSG roadmap consumes rather than builds;
none of them is proved of `TauCeti.TypeDSpinCarrier.groupScheme` here or in the files this one
imports. What this file supplies is the branch's explicit carrier evaluated at the algebraic
closure the index names; it transfers to the L0 carrier along that Layer 9 identification, and not
before. The counterparts on the branches already assembled are
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeA.lean`,
`TauCeti/GroupTheory/SpecificGroups/CFSG/TypeE6.lean` and
`TauCeti/GroupTheory/SpecificGroups/CFSG/Unimodular.lean`.
-/

public section

namespace TauCeti

namespace TypeDDiagramLieIndex

noncomputable section

variable (d : TypeDDiagramLieIndex)

/-- **The ambient group this file attaches to a validated index on a type-`D` diagram**: the points
of the explicit full-weight type-`Dₙ` spin Chevalley carrier, at the rank the index names, over the
algebraic closure of its prime field.

It is infinite, and it is the same group for the untwisted, graph-twisted and triality-twisted
families of a given rank and field order, those three differing only in the Steinberg map taken of
it. No finiteness, reductivity, pinning or maximality statement is attached to it, and it is not
claimed to be the pinned `Dₙ` group scheme's points that milestone L0 asks for, that identification
being the Layer 9 target described in the module docstring. -/
abbrev AmbientGroup : Type :=
  TypeDSpinCarrier.points d.1.rank d.four_le_rank d.1.Closure

/-- Milestone L3 will run its recipe inside this group, so it carries a group structure; the
carrier being a subgroup of a general linear group supplies it. -/
example : Group d.AmbientGroup := inferInstance

end

end TypeDDiagramLieIndex

end TauCeti
