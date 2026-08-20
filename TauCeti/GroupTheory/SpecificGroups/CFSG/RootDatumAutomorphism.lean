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
symmetry group `TauCeti.DynkinType.diagramSymmetry` of that matrix. The order relation of the
resulting automorphism is the image of `TauCeti.GraphTwistedIndex.diagramPerm_pow_twistOrder`, so
`γ ^ 2 = 1` on `²Aₙ`, `²Dₙ` and `²E₆` and `γ ^ 3 = 1` on `³D₄` hold of the root datum before any
group scheme is built. On an untwisted family the permutation is the identity and so is the
automorphism.

## Main declarations

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

noncomputable section

/-- **The graph automorphism of the pinned simply connected root datum** attached to a graph-twisted
index: the automorphism realizing its pinned diagram permutation. It is the identity on an untwisted
family, where that permutation is the identity. -/
def datumGraphAut :
    (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).Aut :=
  DynkinType.diagramAut d.1.dynkinType_valid
    (DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm)

/-- The root-datum graph automorphism acts on the full root enumeration by the permutation induced
from the diagram permutation of the index. -/
@[simp] theorem datumGraphAut_indexEquiv :
    d.datumGraphAut.indexEquiv =
      DynkinType.diagramRootPerm d.1.dynkinType_valid
        (DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm) := by
  rw [datumGraphAut, DynkinType.diagramAut_indexEquiv]

/-- The weight map of the root-datum graph automorphism permutes the fundamental-weight
coordinates by the diagram permutation of the index. -/
@[simp] theorem datumGraphAut_weightMap :
    d.datumGraphAut.toHom.weightMap =
      (LinearEquiv.funCongrLeft ℤ ℤ d.diagramPerm.symm).toLinearMap := by
  rw [datumGraphAut, DynkinType.diagramAut_weightMap]

/-- The coweight map of the root-datum graph automorphism permutes the simple-coroot coordinates by
the diagram permutation of the index. -/
@[simp] theorem datumGraphAut_coweightMap :
    d.datumGraphAut.toHom.coweightMap =
      (LinearEquiv.funCongrLeft ℤ ℤ d.diagramPerm).toLinearMap := by
  rw [datumGraphAut, DynkinType.diagramAut_coweightMap]

/-- The root-datum graph automorphism permutes the Bourbaki-numbered simple roots by the diagram
permutation of the index. -/
theorem datumGraphAut_indexEquiv_simpleIndex (i : Fin d.1.rank) :
    d.datumGraphAut.indexEquiv (d.1.dynkinType.simpleIndex d.1.dynkinType_valid i) =
      d.1.dynkinType.simpleIndex d.1.dynkinType_valid (d.diagramPerm i) := by
  rw [datumGraphAut, DynkinType.diagramAut_indexEquiv, DynkinType.diagramRootPerm_simpleIndex]

/-- Every root of the pinned datum has its fundamental-weight coordinates permuted by the diagram
permutation of the index. -/
@[simp] theorem root_datumGraphAut_indexEquiv (k : Fin d.1.dynkinType.numRoots) :
    d.datumGraphAut •
        (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root k =
      fun j => (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).root k
        (d.diagramPerm.symm j) := by
  rw [← RootPairing.Equiv.root_indexEquiv_eq_smul]
  rw [datumGraphAut, DynkinType.diagramAut_indexEquiv]
  exact DynkinType.root_diagramRootPerm d.1.dynkinType_valid
    (DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm) k

/-- Every coroot of the pinned datum has its simple-coroot coordinates permuted by the diagram
permutation of the index. -/
theorem coroot_datumGraphAut_indexEquiv (k : Fin d.1.dynkinType.numRoots) :
    (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).coroot
        (d.datumGraphAut.indexEquiv k) =
      fun j => (d.1.dynkinType.simplyConnectedRootDatum d.1.dynkinType_valid).coroot k
        (d.diagramPerm.symm j) := by
  rw [datumGraphAut, DynkinType.diagramAut_indexEquiv]
  exact DynkinType.coroot_diagramRootPerm d.1.dynkinType_valid
    (DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm) k

/-- **The order relation of the root-datum graph automorphism.** This is `γ ^ 2 = 1` for `²Aₙ`,
`²Dₙ` and `²E₆`, `γ ^ 3 = 1` for `³D₄`, and the trivial relation on an untwisted family, all read
off the twist order recorded by the index. -/
@[simp] theorem datumGraphAut_pow_twistOrder : d.datumGraphAut ^ d.twistOrder = 1 :=
  DynkinType.diagramAut_pow_eq_one d.1.dynkinType_valid
    (DynkinType.mem_diagramSymmetry_iff.mpr d.cartanMatrix_diagramPerm)
    d.diagramPerm_pow_twistOrder

end

end TauCeti.GraphTwistedIndex
