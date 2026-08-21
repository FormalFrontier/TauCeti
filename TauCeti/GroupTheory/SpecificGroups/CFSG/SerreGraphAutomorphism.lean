/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre.Automorphism
public import TauCeti.GroupTheory.SpecificGroups.CFSG.GraphTwisted

/-!
# Serre graph automorphisms for the graph-twisted families

For a graph-twisted finite group of Lie type, the graph part of its Steinberg endomorphism starts
with the automorphism of the split semisimple Lie algebra which permutes the Chevalley generators
according to the symmetry of the Dynkin diagram. This file constructs that automorphism on the
explicit Serre presentation attached to every `TauCeti.GraphTwistedIndex`.

The construction joins two existing pieces of pinned data. The permutation
`TauCeti.GraphTwistedIndex.diagramPerm` records the Bourbaki-numbered diagram symmetry selected by
the CFSG index, and `TauCeti.serreDiagramAut` turns any Cartan-matrix symmetry into an automorphism
of the corresponding Serre Lie algebra. The matrix invariance proof here is the audit boundary
between them. No root datum, Lie algebra, or automorphism is selected by choice.

The resulting automorphism sends each of the three generator families without signs,

```text
H_i ↦ H_{γ i},   E_i ↦ E_{γ i},   F_i ↦ F_{γ i},
```

and its iterate at `twistOrder` is the identity. Thus the order-two relations for `²Aₙ`, `²Dₙ`
and `²E₆`, and the order-three relation for `³D₄`, are already present before the automorphism
is descended through the Kostant form to the pinned group scheme. It also commutes with the
Chevalley involution, as both automorphisms visibly do on the Serre generators.

## Main declarations

* `TauCeti.GraphTwistedIndex.serreGraphAut`: the graph automorphism of the Serre Lie algebra of an
  indexed Dynkin diagram.
* `TauCeti.GraphTwistedIndex.serreGraphAut_serreH`, `serreGraphAut_serreE`, and
  `serreGraphAut_serreF`: its action on the Chevalley generators.
* `TauCeti.GraphTwistedIndex.serreGraphAut_iterate_twistOrder`: the required order relation.
* `TauCeti.GraphTwistedIndex.serreChevalleyInvolution_comm_serreGraphAut`: compatibility with the
  Chevalley involution.

## Roadmap and references

This is a prerequisite for the Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. That construction descends diagram automorphisms from
the Lie algebra through the Kostant integral form to the pinned group scheme. It is consumed by
milestone L1 of `TauCetiRoadmap/CFSGStatement/README.md`, which forms graph-twisted Steinberg maps
and requires `γ² = 1` or `γ³ = 1` together with the displayed simple-root-subgroup equation.

The conventions follow R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex
Characters*, §1.15, and the Bourbaki numbering pinned by the root-systems roadmap.
-/

public section

namespace TauCeti.GraphTwistedIndex

universe u

variable (d : GraphTwistedIndex)
variable (R : Type u) [CommRing R]

/-- The diagram permutation selected by a graph-twisted index preserves the Cartan matrix of its
underlying untwisted Dynkin diagram. This is the matrix form consumed by `serreDiagramAut`. -/
@[simp]
theorem cartanMatrix_submatrix_diagramPerm :
    d.1.dynkinType.cartanMatrix.submatrix d.diagramPerm d.diagramPerm =
      d.1.dynkinType.cartanMatrix := by
  ext i j
  exact d.cartanMatrix_diagramPerm i j

/-- The diagram permutation also preserves the transposed Cartan matrix used by the Serre
presentation of the pinned Lie algebra. -/
@[simp]
theorem cartanMatrix_transpose_submatrix_diagramPerm :
    (Matrix.transpose d.1.dynkinType.cartanMatrix).submatrix d.diagramPerm d.diagramPerm =
      Matrix.transpose d.1.dynkinType.cartanMatrix := by
  ext i j
  exact d.cartanMatrix_diagramPerm j i

/-- The graph automorphism of the Serre Lie algebra attached to a graph-twisted index.

It is induced by the pinned permutation of the Bourbaki-numbered nodes. On an untwisted family the
permutation is the identity; on `²Aₙ`, `²Dₙ`, `²E₆`, and `³D₄` it is respectively the chain
reversal, fork exchange, `E₆` involution, or triality. -/
noncomputable def serreGraphAut :
    Matrix.ToLieAlgebra R (Matrix.transpose d.1.dynkinType.cartanMatrix) ≃ₗ⁅R⁆
      Matrix.ToLieAlgebra R (Matrix.transpose d.1.dynkinType.cartanMatrix) :=
  serreDiagramAut R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm

/-- The graph automorphism sends the `i`-th Cartan generator to the generator indexed by the
diagram permutation. -/
@[simp]
theorem serreGraphAut_serreH (i : Fin d.1.rank) :
    d.serreGraphAut R
        (serreH R (Matrix.transpose d.1.dynkinType.cartanMatrix) i) =
      serreH R (Matrix.transpose d.1.dynkinType.cartanMatrix) (d.diagramPerm i) :=
  serreDiagramAut_serreH R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm i

/-- The graph automorphism sends the `i`-th positive simple-root generator to the generator indexed
by the diagram permutation, without changing its sign. -/
@[simp]
theorem serreGraphAut_serreE (i : Fin d.1.rank) :
    d.serreGraphAut R
        (serreE R (Matrix.transpose d.1.dynkinType.cartanMatrix) i) =
      serreE R (Matrix.transpose d.1.dynkinType.cartanMatrix) (d.diagramPerm i) :=
  serreDiagramAut_serreE R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm i

/-- The graph automorphism sends the `i`-th negative simple-root generator to the generator indexed
by the diagram permutation, without changing its sign. -/
@[simp]
theorem serreGraphAut_serreF (i : Fin d.1.rank) :
    d.serreGraphAut R
        (serreF R (Matrix.transpose d.1.dynkinType.cartanMatrix) i) =
      serreF R (Matrix.transpose d.1.dynkinType.cartanMatrix) (d.diagramPerm i) :=
  serreDiagramAut_serreF R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm i

/-- Applying the Serre graph automorphism `twistOrder` times is the identity. This is the uniform
form of `γ² = 1` on `²Aₙ`, `²Dₙ`, and `²E₆`, and `γ³ = 1` on `³D₄`; on an untwisted family
the twist order is one and the automorphism itself is the identity. -/
@[simp]
theorem serreGraphAut_iterate_twistOrder :
    (d.serreGraphAut R : _ → _)^[d.twistOrder] = id :=
  serreDiagramAut_iterate_eq_id R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm d.diagramPerm_pow_twistOrder

/-- The Chevalley involution commutes with the graph automorphism selected by the index. The former
exchanges positive and negative generators with a sign, while the latter applies the same node
permutation to all three Serre-generator families. -/
theorem serreChevalleyInvolution_comm_serreGraphAut :
    (serreChevalleyInvolution R (Matrix.transpose d.1.dynkinType.cartanMatrix)).trans
        (d.serreGraphAut R) =
      (d.serreGraphAut R).trans
        (serreChevalleyInvolution R (Matrix.transpose d.1.dynkinType.cartanMatrix)) :=
  serreChevalleyInvolution_comm_serreDiagramAut R
    (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm

end TauCeti.GraphTwistedIndex
