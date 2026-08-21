/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Face.Basic

/-!
# The cube-weight recursion in a plumbing lattice

The lattice-homology cube weight `characteristicCubeWeight k x S` is the maximum of the point
weights `χ_k` over the `2 ^ |S|` vertices of the cube with base point `x` and directions `S`
(`CubeWeight.lean`). The two faces of this cube in a direction `v ∈ S` are themselves cubes one
dimension lower: the lower face is the cube based at `x` with directions `S.erase v`, and the
upper face is the cube based at `x + E_v` with directions `S.erase v` (`CubeFace.lean`). Every
vertex of the ambient cube belongs to exactly one of the two faces, according to whether its
direction subset contains `v`, so the vertex set splits as a union of the two face vertex sets.

Taking the maximum over this splitting turns the cube weight into a recursion: the cube weight is
the larger of its two face weights,

`characteristicCubeWeight k x S =
  max (characteristicCubeWeight k x (S.erase v))
    (characteristicCubeWeight k (x + E_v) (S.erase v))`.

This is the cubical recursion underneath Némethi's lattice-homology differential. Its immediate
consequence is that, in any direction, at least one of the two face exponents vanishes: since the
cube weight equals the larger face weight, the difference to that face is zero. The face exponents
are the `U`-powers attached to the two faces in the lattice-homology differential, so this records
that the two opposite codimension-one faces in a direction never both carry a positive `U`-power.

## Main results

* `TauCeti.PlumbingGraph.cubeVertices_eq_union_erase`: the vertices of a cube split, along a
  direction `v ∈ S`, into the vertices of its lower face and the vertices of its upper face.
* `TauCeti.PlumbingGraph.characteristicCubeWeight_eq_max_erase`: the cube weight is the maximum of
  its lower- and upper-face weights in any direction `v ∈ S`.
* `TauCeti.PlumbingGraph.characteristicCubeWeight_insert_eq_max`: the dual "add a direction" form,
  expressing the weight of an enlarged cube as the maximum of the two faces in the new direction.
* `TauCeti.PlumbingGraph.min_characteristicFaceExponent_eq_zero`: in any direction, the smaller of
  the lower- and upper-face exponents is zero.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose differential is built from the cubical face weights of a plumbing
lattice. The recursive maximum and the resulting `U`-exponent bookkeeping are standard in Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [DecidableEq (V → ℤ)]

/-- The vertices of a cube split along a direction `v ∈ S` into the vertices of its two faces: a
vertex whose direction subset avoids `v` lies in the lower face (same base point, directions
`S.erase v`), while a vertex whose direction subset contains `v` lies in the upper face (base
point `x + E_v`, directions `S.erase v`). -/
theorem cubeVertices_eq_union_erase {S : Finset V} {v : V} (hv : v ∈ S) (x : V → ℤ) :
    cubeVertices x S =
      cubeVertices x (S.erase v) ∪ cubeVertices (x + Pi.single v (1 : ℤ)) (S.erase v) := by
  apply Finset.Subset.antisymm
  · intro y hy
    rw [mem_cubeVertices] at hy
    obtain ⟨T, hTS, rfl⟩ := hy
    rw [Finset.mem_union]
    by_cases hvT : v ∈ T
    · refine Or.inr ?_
      rw [mem_cubeVertices]
      refine ⟨T.erase v, Finset.erase_subset_erase v hTS, ?_⟩
      rw [cubeVertex_add_single_eq_insert (Finset.notMem_erase v T), Finset.insert_erase hvT]
    · refine Or.inl ?_
      rw [mem_cubeVertices]
      exact ⟨T, Finset.subset_erase.mpr ⟨hTS, hvT⟩, rfl⟩
  · rw [Finset.union_subset_iff]
    exact ⟨cubeVertices_subset (Finset.erase_subset v S) x, cubeVertices_upperFace_subset hv⟩

variable [Fintype V] (P : PlumbingGraph V) (k : P.characteristicVectors)

/-- The cube weight is the maximum of its two face weights in any direction `v ∈ S`: the lower
face (base point `x`, directions `S.erase v`) and the upper face (base point `x + E_v`, directions
`S.erase v`). This is the cubical recursion at the heart of the lattice-homology differential. -/
theorem characteristicCubeWeight_eq_max_erase (x : V → ℤ) {S : Finset V} {v : V} (hv : v ∈ S) :
    P.characteristicCubeWeight k x S =
      max (P.characteristicCubeWeight k x (S.erase v))
        (P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v)) := by
  apply le_antisymm
  · apply P.characteristicCubeWeight_le k
    intro y hy
    rw [cubeVertices_eq_union_erase hv, Finset.mem_union] at hy
    rcases hy with hy | hy
    · exact le_max_of_le_left (P.characteristicWeight_le_characteristicCubeWeight k hy)
    · exact le_max_of_le_right (P.characteristicWeight_le_characteristicCubeWeight k hy)
  · exact max_le (P.characteristicCubeWeight_mono k (Finset.erase_subset v S) x)
      (P.characteristicUpperFaceWeight_le k hv)

/-- The "add a direction" form of the cube-weight recursion: adjoining a new direction `v ∉ S` to
a cube gives the maximum of the original cube weight and the weight of the cube shifted by the new
basis vector `E_v`. -/
theorem characteristicCubeWeight_insert_eq_max (x : V → ℤ) {S : Finset V} {v : V} (hv : v ∉ S) :
    P.characteristicCubeWeight k x (insert v S) =
      max (P.characteristicCubeWeight k x S)
        (P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) S) := by
  rw [P.characteristicCubeWeight_eq_max_erase k x (Finset.mem_insert_self v S),
    Finset.erase_insert hv]

/-- In any cube direction `v ∈ S`, at least one of the two face exponents is zero: the cube weight
agrees with the larger of its two face weights, so the difference to that face vanishes. The face
exponents are the `U`-powers of the lattice-homology differential, so in any direction the two
opposite codimension-one faces never both carry a positive `U`-power. -/
@[simp]
theorem min_characteristicFaceExponent_eq_zero (x : V → ℤ) {S : Finset V} {v : V} (hv : v ∈ S) :
    min (P.characteristicLowerFaceExponent k x S v)
      (P.characteristicUpperFaceExponent k x S hv) = 0 := by
  rcases le_total (P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v))
    (P.characteristicCubeWeight k x (S.erase v)) with hUL | hLU
  · have hlow : P.characteristicLowerFaceExponent k x S v = 0 := by
      rw [P.characteristicLowerFaceExponent_eq_zero_iff k,
        P.characteristicCubeWeight_eq_max_erase k x hv, max_eq_left hUL]
    simp [hlow]
  · have hup : P.characteristicUpperFaceExponent k x S hv = 0 := by
      rw [P.characteristicUpperFaceExponent_eq_zero_iff k hv,
        P.characteristicCubeWeight_eq_max_erase k x hv, max_eq_right hLU]
    simp [hup]

end PlumbingGraph

end TauCeti
