/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Weight.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Cardinality of plumbing-lattice cube vertex sets

This file records the finite combinatorics of the vertex set of a plumbing-lattice cube. A cube
with direction set `S` has one vertex for each subset of `S`, so its vertex set has cardinality
`2 ^ S.card`.

The result is independent of the plumbing graph and of the characteristic weight function: it is
the cubical bookkeeping underneath the lattice-homology chain groups, where a generator is a
lattice cube indexed by a base point and a finite set of basis directions.

## Main results

* `TauCeti.PlumbingGraph.cubeVertex_injective`: different direction subsets give different
  vertices.
* `TauCeti.PlumbingGraph.cubeVertexSubsetEquiv`: vertices of an `S`-cube are equivalent to
  subsets of `S`.
* `TauCeti.PlumbingGraph.cubeVertices_eq_image_powerset`: the vertex set is the image of the
  powerset of the direction set.
* `TauCeti.PlumbingGraph.card_cubeVertices`: an `S`-cube has `2 ^ S.card` vertices.

## References

This supplies a small prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane L ("lattice homology"), whose cubical complex is built from plumbing-lattice cubes and their
finite vertex sets. The convention is the standard cubical one used in Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

/-- Distinct subsets of basis directions determine distinct vertices of a plumbing-lattice cube.

At coordinate `v`, the vertex remembers whether `v` was selected by adding `1` precisely in the
selected directions, so equality of vertices recovers membership in the subset. -/
theorem cubeVertex_injective (x : V → ℤ) : Function.Injective (cubeVertex x) := by
  intro T U hTU
  ext v
  constructor
  · intro hT
    by_contra hU
    have hcoord := congr_fun hTU v
    simp [cubeVertex_apply, hT, hU] at hcoord
  · intro hU
    by_contra hT
    have hcoord := congr_fun hTU v
    simp [cubeVertex_apply, hT, hU] at hcoord

variable [DecidableEq (V → ℤ)]

/-- The equivalence between subsets of the direction set and vertices of the corresponding
plumbing-lattice cube. This is the precise "one vertex for each subset of directions" statement
behind the cardinality formula. -/
noncomputable def cubeVertexSubsetEquiv (x : V → ℤ) (S : Finset V) :
    {T : Finset V // T ⊆ S} ≃ {y : V → ℤ // y ∈ cubeVertices x S} where
  toFun T := ⟨cubeVertex x T.1, cubeVertex_subset_mem_cubeVertices T.2 x⟩
  invFun y :=
    ⟨Classical.choose ((mem_cubeVertices x S y.1).mp y.2),
      (Classical.choose_spec ((mem_cubeVertices x S y.1).mp y.2)).1⟩
  left_inv T := by
    apply Subtype.ext
    exact cubeVertex_injective x
      (Classical.choose_spec
        ((mem_cubeVertices x S (cubeVertex x T.1)).mp
          (cubeVertex_subset_mem_cubeVertices T.2 x))).2
  right_inv y := by
    apply Subtype.ext
    exact (Classical.choose_spec ((mem_cubeVertices x S y.1).mp y.2)).2

private theorem cubeVertexSubsetEquiv_apply_aux
    (x : V → ℤ) (S : Finset V) (T : {T : Finset V // T ⊆ S}) :
    (cubeVertexSubsetEquiv x S T).1 = cubeVertex x T.1 :=
  rfl

/-- The subset-to-vertex equivalence sends a subset of directions to its cube vertex. -/
@[simp]
theorem cubeVertexSubsetEquiv_apply (x : V → ℤ) (S : Finset V) (T : {T : Finset V // T ⊆ S}) :
    (cubeVertexSubsetEquiv x S T).1 = cubeVertex x T.1 :=
  cubeVertexSubsetEquiv_apply_aux x S T

/-- The inverse of the subset-to-vertex equivalence returns a subset whose vertex is the
specified cube vertex. -/
@[simp]
theorem cubeVertexSubsetEquiv_apply_symm_apply (x : V → ℤ) (S : Finset V)
    (y : {y : V → ℤ // y ∈ cubeVertices x S}) :
    cubeVertex x ((cubeVertexSubsetEquiv x S).symm y).1 = y.1 := by
  exact Subtype.ext_iff.mp ((cubeVertexSubsetEquiv x S).right_inv y)

/-- The vertex set of the cube with direction set `S` is exactly the image of the powerset of
`S` under the subset-to-vertex map. -/
theorem cubeVertices_eq_image_powerset (x : V → ℤ) (S : Finset V) :
    cubeVertices x S = S.powerset.image (cubeVertex x) := by
  ext y
  rw [mem_cubeVertices, Finset.mem_image]
  constructor
  · rintro ⟨T, hTS, rfl⟩
    exact ⟨T, Finset.mem_powerset.mpr hTS, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T, Finset.mem_powerset.mp hT, rfl⟩

/-- A plumbing-lattice cube with direction set `S` has one vertex for each subset of `S`. -/
@[simp]
theorem card_cubeVertices (x : V → ℤ) (S : Finset V) :
    (cubeVertices x S).card = 2 ^ S.card := by
  rw [cubeVertices_eq_image_powerset, Finset.card_image_of_injective _ (cubeVertex_injective x),
    Finset.card_powerset]

end PlumbingGraph

end TauCeti
