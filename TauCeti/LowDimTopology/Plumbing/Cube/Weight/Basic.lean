/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight.Basic
public import Mathlib.Combinatorics.Additive.SubsetSum

/-!
# Cube weights in a plumbing lattice

This file packages the finite cube weights used in Némethi's lattice homology. A cube is
specified by a base lattice point `x : V → ℤ` and a finite set `S : Finset V` of basis
directions. Its vertices are the points

`x + ∑ v ∈ T, E_v`

for subsets `T ⊆ S`. For a characteristic covector `k`, the cube weight is the maximum of the
already-defined point weights `χ_k` over these vertices.

## Main definitions

* `TauCeti.PlumbingGraph.cubeVertex`: the vertex indexed by a subset of directions.
* `TauCeti.PlumbingGraph.cubeVertices`: the finite set of all vertices of a cube.
* `TauCeti.PlumbingGraph.characteristicCubeWeight`: the maximum `χ_k` over those vertices.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The cube weight is the standard maximum over vertices used in the
lattice-homology cubical complex; see Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

/-- The lattice point obtained from a base point `x` by adding the plumbing basis vectors in
`T`. This is the vertex of a lattice cube indexed by the subset `T` of its directions. -/
noncomputable def cubeVertex (x : V → ℤ) (T : Finset V) : V → ℤ :=
  x + ∑ v ∈ T, Pi.single v (1 : ℤ)

/-- A plumbing cube vertex is the base point shifted by the basis spheres in the chosen
directions. This is definitionally `cubeVertex`, packaged for rewriting. -/
theorem cubeVertex_def (x : V → ℤ) (T : Finset V) :
    cubeVertex x T = x + ∑ v ∈ T, Pi.single v (1 : ℤ) := by
  rw [cubeVertex]

/-- The vertex indexed by the empty subset is the base point. -/
@[simp]
theorem cubeVertex_empty (x : V → ℤ) : cubeVertex x ∅ = x := by
  simp [cubeVertex]

/-- Adding a direction not already present adds the corresponding basis vector to the cube
vertex. -/
theorem cubeVertex_insert {T : Finset V} {v : V} (hv : v ∉ T) (x : V → ℤ) :
    cubeVertex x (insert v T) = cubeVertex x T + Pi.single v (1 : ℤ) := by
  ext w
  simp [cubeVertex, hv, add_assoc, add_comm]

/-- The coordinate value of a cube vertex. It is `x v + 1` in directions selected by `T`, and
`x v` otherwise. -/
@[simp]
theorem cubeVertex_apply (x : V → ℤ) (T : Finset V) (v : V) :
    cubeVertex x T v = x v + if v ∈ T then 1 else 0 := by
  classical
  simp [cubeVertex, Finset.sum_apply, Pi.single_apply]

/-- Shifting the base point by a basis vector `E_v` and adjoining `v` to the directions describe
the same cube vertex, provided `v` was not already a direction. -/
theorem cubeVertex_add_single_eq_insert {T : Finset V} {v : V} (hv : v ∉ T) (x : V → ℤ) :
    cubeVertex (x + Pi.single v (1 : ℤ)) T = cubeVertex x (insert v T) := by
  ext w
  by_cases hw : w = v
  · subst hw
    simp [cubeVertex_apply, hv]
  · simp [cubeVertex_apply, hw]

variable [DecidableEq (V → ℤ)]

omit [DecidableEq (V → ℤ)] in
private theorem single_one_injective : Function.Injective fun v : V => Pi.single v (1 : ℤ) := by
  intro v w hvw
  by_contra hne
  have hcoord := congr_fun hvw v
  simp [Pi.single, hne] at hcoord

private theorem cubeVertex_sum_mem_subsetSum {T S : Finset V} (hTS : T ⊆ S) :
    (∑ v ∈ T, Pi.single v (1 : ℤ)) ∈
      (S.image fun v => Pi.single v (1 : ℤ)).subsetSum := by
  rw [Finset.mem_subsetSum_iff]
  refine ⟨T.image fun v => Pi.single v (1 : ℤ), Finset.image_subset_image hTS, ?_⟩
  rw [Finset.sum_image single_one_injective.injOn]

/-- The finite set of all vertices of the cube with base point `x` and directions `S`. -/
noncomputable def cubeVertices (x : V → ℤ) (S : Finset V) : Finset (V → ℤ) :=
  ((S.image fun v => Pi.single v (1 : ℤ)).subsetSum).image fun z => x + z

/-- A point is a vertex of the cube based at `x` with directions `S` exactly when it is
`cubeVertex x T` for some subset `T ⊆ S` of the directions. -/
theorem mem_cubeVertices (x : V → ℤ) (S : Finset V) (y : V → ℤ) :
    y ∈ cubeVertices x S ↔ ∃ T ⊆ S, cubeVertex x T = y := by
  rw [cubeVertices, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_subsetSum_iff] at hz
    obtain ⟨U, hU, rfl⟩ := hz
    rw [Finset.subset_image_iff] at hU
    obtain ⟨T, hTS, rfl⟩ := hU
    exact ⟨T, hTS, by rw [cubeVertex, Finset.sum_image single_one_injective.injOn]⟩
  · rintro ⟨T, hTS, rfl⟩
    exact ⟨∑ v ∈ T, Pi.single v (1 : ℤ), cubeVertex_sum_mem_subsetSum hTS, rfl⟩

/-- The base point is a vertex of every cube. -/
@[simp]
theorem base_mem_cubeVertices (x : V → ℤ) (S : Finset V) :
    x ∈ cubeVertices x S := by
  rw [mem_cubeVertices]
  exact ⟨∅, Finset.empty_subset S, cubeVertex_empty x⟩

/-- The vertex set of a cube is nonempty. -/
theorem cubeVertices_nonempty (x : V → ℤ) (S : Finset V) :
    (cubeVertices x S).Nonempty :=
  ⟨x, base_mem_cubeVertices x S⟩

/-- A direction subset determines a vertex of any cube containing those directions. -/
theorem cubeVertex_subset_mem_cubeVertices {T S : Finset V} (hTS : T ⊆ S) (x : V → ℤ) :
    cubeVertex x T ∈ cubeVertices x S := by
  rw [mem_cubeVertices]
  exact ⟨T, hTS, rfl⟩

/-- The vertices of a subcube are vertices of the larger cube. -/
theorem cubeVertices_subset {S T : Finset V} (hST : S ⊆ T) (x : V → ℤ) :
    cubeVertices x S ⊆ cubeVertices x T := by
  intro y hy
  rw [mem_cubeVertices] at hy ⊢
  obtain ⟨U, hUS, rfl⟩ := hy
  exact ⟨U, hUS.trans hST, rfl⟩

/-- The zero-dimensional cube has its base point as its only vertex. -/
@[simp]
theorem cubeVertices_empty (x : V → ℤ) : cubeVertices x ∅ = {x} := by
  ext y
  rw [mem_cubeVertices, Finset.mem_singleton]
  constructor
  · rintro ⟨T, hT, rfl⟩
    rw [Finset.subset_empty.mp hT]
    exact cubeVertex_empty x
  · rintro rfl
    exact ⟨∅, Finset.empty_subset _, cubeVertex_empty _⟩

variable [Fintype V]

/-- The characteristic weight values attained on the vertices of a plumbing cube. -/
private noncomputable def characteristicCubeWeightValues
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) : Finset ℤ :=
  (cubeVertices x S).image fun y => P.characteristicWeight k y

/-- The value set for a plumbing cube is nonempty. -/
private theorem characteristicCubeWeightValues_nonempty
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    (characteristicCubeWeightValues P k x S).Nonempty :=
  Finset.image_nonempty.mpr (cubeVertices_nonempty x S)

/-- The characteristic cube weight is the maximum of the point weights over the cube's vertices. -/
noncomputable def characteristicCubeWeight
  (P : PlumbingGraph V)
  (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) : ℤ :=
  (characteristicCubeWeightValues P k x S).max'
    (characteristicCubeWeightValues_nonempty P k x S)

/-- A vertex weight is one of the values used to form the characteristic cube weight. -/
private theorem characteristicWeight_mem_characteristicCubeWeightValues
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {y : V → ℤ}
    (hy : y ∈ cubeVertices x S) :
    P.characteristicWeight k y ∈ characteristicCubeWeightValues P k x S := by
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- The point weight at any vertex is bounded above by the characteristic cube weight. -/
theorem characteristicWeight_le_characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {y : V → ℤ}
    (hy : y ∈ cubeVertices x S) :
    P.characteristicWeight k y ≤ P.characteristicCubeWeight k x S := by
  exact Finset.le_max'
    (characteristicCubeWeightValues P k x S)
    (P.characteristicWeight k y)
    (characteristicWeight_mem_characteristicCubeWeightValues P k hy)

/-- To bound a characteristic cube weight above, bound the weight at every vertex. -/
theorem characteristicCubeWeight_le
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {n : ℤ}
    (h : ∀ y ∈ cubeVertices x S, P.characteristicWeight k y ≤ n) :
    P.characteristicCubeWeight k x S ≤ n := by
  unfold characteristicCubeWeight
  exact Finset.max'_le _ _ _ fun m hm => by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
    exact h y hy

/-- A characteristic cube weight is bounded above by `n` iff every vertex weight is. -/
theorem characteristicCubeWeight_le_iff
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {n : ℤ} :
    P.characteristicCubeWeight k x S ≤ n ↔
      ∀ y ∈ cubeVertices x S, P.characteristicWeight k y ≤ n :=
  ⟨fun h _ hy => (P.characteristicWeight_le_characteristicCubeWeight k hy).trans h,
    P.characteristicCubeWeight_le k⟩

/-- The characteristic cube weight is attained at some vertex of the cube. -/
theorem exists_characteristicWeight_eq_characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    ∃ y ∈ cubeVertices x S, P.characteristicWeight k y = P.characteristicCubeWeight k x S := by
  unfold characteristicCubeWeight
  have hmax : (characteristicCubeWeightValues P k x S).max'
      (characteristicCubeWeightValues_nonempty P k x S) ∈
        characteristicCubeWeightValues P k x S :=
    Finset.max'_mem _ _
  obtain ⟨y, hy, hweight⟩ := Finset.mem_image.mp hmax
  exact ⟨y, hy, hweight⟩

/-- The point weight at a direction subset is bounded above by the characteristic cube weight. -/
theorem characteristicWeight_cubeVertex_le_characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {T S : Finset V} (hTS : T ⊆ S) (x : V → ℤ) :
    P.characteristicWeight k (cubeVertex x T) ≤ P.characteristicCubeWeight k x S :=
  P.characteristicWeight_le_characteristicCubeWeight k
    (cubeVertex_subset_mem_cubeVertices hTS x)

/-- The base point's weight is bounded above by every cube weight based at that point. -/
theorem characteristicWeight_le_characteristicCubeWeight_base
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    P.characteristicWeight k x ≤ P.characteristicCubeWeight k x S := by
  simpa using
    P.characteristicWeight_cubeVertex_le_characteristicCubeWeight k (Finset.empty_subset S) x

/-- Characteristic cube weight is monotone under enlarging the set of cube directions. -/
theorem characteristicCubeWeight_mono
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {S T : Finset V} (hST : S ⊆ T) (x : V → ℤ) :
    P.characteristicCubeWeight k x S ≤ P.characteristicCubeWeight k x T := by
  apply P.characteristicCubeWeight_le k
  intro y hy
  exact P.characteristicWeight_le_characteristicCubeWeight k (cubeVertices_subset hST x hy)

/-- The characteristic cube weight of the zero-dimensional cube is the point weight of its base
point. -/
@[simp]
theorem characteristicCubeWeight_empty (P : PlumbingGraph V) (k : P.characteristicVectors)
    (x : V → ℤ) :
    P.characteristicCubeWeight k x ∅ = P.characteristicWeight k x := by
  apply le_antisymm
  · apply P.characteristicCubeWeight_le k
    intro z hz
    rw [cubeVertices_empty, Finset.mem_singleton] at hz
    rw [hz]
  · exact P.characteristicWeight_le_characteristicCubeWeight_base k x ∅

end PlumbingGraph

end TauCeti
