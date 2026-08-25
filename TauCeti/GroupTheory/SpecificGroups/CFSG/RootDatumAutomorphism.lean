/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism

/-!
# The root-datum graph automorphism of a graph-twisted index

The graph part of the Steinberg endomorphism of a graph-twisted finite group of Lie type is the
automorphism of the pinned Chevalley--Demazure group scheme which the isomorphism theorem for pinned
groups produces from an automorphism of its root datum. This file supplies that root-datum
automorphism for every `TauCeti.GraphTwistedIndex`, by feeding the pinned diagram permutation
`TauCeti.GraphTwistedIndex.diagramPerm` into
`TauCeti.DynkinType.diagramAut`.

The two inputs are already pinned, and the only step taken here is to read one as the other. The
index supplies a permutation of the Bourbaki-numbered nodes together with the proof that it
preserves the Cartan matrix, and the root-datum construction consumes exactly a member of the
symmetry group `TauCeti.DynkinType.diagramSymmetry` of that matrix. That reading is
`TauCeti.GraphTwistedIndex.diagramPerm_mem_diagramSymmetry`, and it is the only thing this file
adds to the general construction: with it in hand a consumer applies the `TauCeti.DynkinType`
lemmas about `diagramAut` directly, so none of them is restated at `σ = d.diagramPerm` here. The
order relation of the resulting automorphism is the image of
`TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder`, so `γ ^ 2 = 1` on `²Aₙ`, `²Dₙ` and `²E₆`
and `γ ^ 3 = 1` on `³D₄` hold of the root datum before any group scheme is built. On an untwisted
family the permutation is the identity and so is the automorphism.

## Main declarations

* `TauCeti.GraphTwistedIndex.diagramPerm_mem_diagramSymmetry`: the diagram permutation of an index
  is a symmetry of the Cartan matrix of its Dynkin type.
* `TauCeti.GraphTwistedIndex.datumGraphAut`: the resulting automorphism of the pinned simply
  connected root datum.
* `TauCeti.GraphTwistedIndex.datumGraphAut_pow_twistOrder`: its order relation.

## Roadmap

The construction consumed here is Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, "Pinnings
... This is what makes 'the' graph automorphism well defined", whose isomorphism theorem for pinned
groups takes an isomorphism of root data as its input. This file is the instance of that input
required by milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`, which forms the graph-twisted
Steinberg maps `γ ∘ Frob_q` and requires the order relations of `γ`. Nothing about a group scheme,
its points, or a finite group is asserted.
-/

public section

namespace TauCeti.GraphTwistedIndex

variable (d : GraphTwistedIndex)

/-- The diagram permutation of a graph-twisted index is a symmetry of the Cartan matrix of its
Dynkin type, which is the form in which `TauCeti.DynkinType.diagramAut` consumes it. -/
theorem diagramPerm_mem_diagramSymmetry :
    d.diagramPerm ∈ d.1.dynkinType.diagramSymmetry :=
  DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm

noncomputable section

/-- **The graph automorphism of the pinned simply connected root datum** attached to a graph-twisted
index: the automorphism realizing its pinned diagram permutation. It is the identity on an untwisted
family, where that permutation is the identity. -/
def datumGraphAut :
    (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).Aut :=
  DynkinType.diagramAut d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry

/-- **The order relation of the root-datum graph automorphism.** This is `γ ^ 2 = 1` for `²Aₙ`,
`²Dₙ` and `²E₆`, `γ ^ 3 = 1` for `³D₄`, and the trivial relation on an untwisted family, all read
off the twist order recorded by the index. -/
@[simp] theorem datumGraphAut_pow_twistOrder : d.datumGraphAut ^ d.twistOrder = 1 :=
  DynkinType.diagramAut_pow_eq_one d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry
    d.diagramPerm_pow_twistOrder

end

end TauCeti.GraphTwistedIndex
