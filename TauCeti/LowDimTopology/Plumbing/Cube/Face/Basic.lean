/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Weight.Basic

/-!
# Face weights for plumbing-lattice cubes

This file adds the codimension-one face bookkeeping needed for the cubical boundary in
Némethi's lattice homology. A cube with base point `x` and directions `S` has two faces in a
direction `v`: the lower face with the same base point and directions `S.erase v`, and the
upper face with base point `x + E_v` and directions `S.erase v`.

The cube weight is the maximum of the point weights over all vertices, so each face weight is
bounded above by the ambient cube weight. The resulting nonnegative differences are the
exponents of the `U`-powers in the later lattice-homology differential.

## Main results

* `TauCeti.PlumbingGraph.cubeVertices_upperFace_subset`: the upper face's vertices are
  vertices of the ambient cube, when `v ∈ S`.
* `TauCeti.PlumbingGraph.characteristicUpperFaceWeight_le`: the upper face weight is bounded by
  the ambient cube weight.
* `TauCeti.PlumbingGraph.characteristicLowerFaceExponent` and
  `TauCeti.PlumbingGraph.characteristicUpperFaceExponent`: the corresponding natural-number
  weight differences.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The face-weight exponents are the standard cubical-boundary
weights in Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

variable [DecidableEq (V → ℤ)]

/-- The upper face in a direction has its vertices among the vertices of the ambient cube. -/
theorem cubeVertices_upperFace_subset {x : V → ℤ} {S : Finset V} {v : V} (hv : v ∈ S) :
    cubeVertices (x + Pi.single v (1 : ℤ)) (S.erase v) ⊆ cubeVertices x S := by
  intro y hy
  rw [mem_cubeVertices] at hy ⊢
  obtain ⟨T, hTS, hTy⟩ := hy
  refine ⟨insert v T, ?_, ?_⟩
  · exact Finset.insert_subset hv (hTS.trans (Finset.erase_subset v S))
  · rw [← hTy]
    have hvT : v ∉ T := fun h => Finset.notMem_erase v S (hTS h)
    exact (cubeVertex_add_single_eq_insert hvT x).symm

variable [Fintype V] (P : PlumbingGraph V) (k : P.characteristicVectors)

/-- The upper face's characteristic cube weight is bounded by the ambient cube weight. -/
theorem characteristicUpperFaceWeight_le {x : V → ℤ} {S : Finset V} {v : V} (hv : v ∈ S) :
    P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v) ≤
      P.characteristicCubeWeight k x S := by
  apply P.characteristicCubeWeight_le k
  intro y hy
  exact P.characteristicWeight_le_characteristicCubeWeight k
    (cubeVertices_upperFace_subset hv hy)

/-- The nonnegative `U`-exponent contributed by the lower face in a cube direction. -/
noncomputable def characteristicLowerFaceExponent
    (x : V → ℤ) (S : Finset V) (v : V) : ℕ :=
  Int.toNat (P.characteristicCubeWeight k x S -
    P.characteristicCubeWeight k x (S.erase v))

/-- The lower-face exponent, cast back to `ℤ`, is the difference between the ambient cube weight
and the lower face weight. -/
@[simp]
theorem characteristicLowerFaceExponent_natCast
    {x : V → ℤ} {S : Finset V} {v : V} :
    (P.characteristicLowerFaceExponent k x S v : ℤ) =
      P.characteristicCubeWeight k x S - P.characteristicCubeWeight k x (S.erase v) := by
  rw [characteristicLowerFaceExponent]
  exact Int.toNat_of_nonneg
    (sub_nonneg.mpr (P.characteristicCubeWeight_mono k (Finset.erase_subset v S) x))

/-- The lower-face exponent is zero exactly when the lower face has the same weight as the
ambient cube. -/
theorem characteristicLowerFaceExponent_eq_zero_iff
    {x : V → ℤ} {S : Finset V} {v : V} :
    P.characteristicLowerFaceExponent k x S v = 0 ↔
      P.characteristicCubeWeight k x S = P.characteristicCubeWeight k x (S.erase v) := by
  constructor
  · intro h
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    rw [characteristicLowerFaceExponent_natCast (P := P) (k := k)] at hcast
    omega
  · intro h
    rw [characteristicLowerFaceExponent, h, sub_self, Int.toNat_zero]

/-- The nonnegative `U`-exponent contributed by the upper face in a direction. -/
noncomputable def characteristicUpperFaceExponent
    (x : V → ℤ) (S : Finset V) {v : V} (_hv : v ∈ S) : ℕ :=
  Int.toNat (P.characteristicCubeWeight k x S -
    P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v))

/-- The upper-face exponent, cast back to `ℤ`, is the difference between the ambient cube weight
and the upper face weight. -/
@[simp]
theorem characteristicUpperFaceExponent_natCast
    {x : V → ℤ} {S : Finset V} {v : V} (hv : v ∈ S) :
    (P.characteristicUpperFaceExponent k x S hv : ℤ) =
      P.characteristicCubeWeight k x S -
        P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v) := by
  rw [characteristicUpperFaceExponent]
  exact Int.toNat_of_nonneg (sub_nonneg.mpr (P.characteristicUpperFaceWeight_le k hv))

/-- The upper-face exponent is zero exactly when the upper face has the same weight as the
ambient cube. -/
theorem characteristicUpperFaceExponent_eq_zero_iff
    {x : V → ℤ} {S : Finset V} {v : V} (hv : v ∈ S) :
    P.characteristicUpperFaceExponent k x S hv = 0 ↔
      P.characteristicCubeWeight k x S =
        P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v) := by
  constructor
  · intro h
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    rw [characteristicUpperFaceExponent_natCast (P := P) (k := k) hv] at hcast
    omega
  · intro h
    rw [characteristicUpperFaceExponent, h, sub_self, Int.toNat_zero]

end PlumbingGraph

end TauCeti
