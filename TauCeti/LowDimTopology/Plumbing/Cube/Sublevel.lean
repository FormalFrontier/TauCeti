/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.Cube.Generator
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# Characteristic-weight sublevels of plumbing cubes

For a characteristic covector `k` and an integer `N`, this file defines the plumbing cubes whose
characteristic cube weight is at most `N`. These sublevels are closed under cubical faces and are
finite when the plumbing form is negative definite.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L. The filtration by
sublevel cubical complexes is the construction in A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The set of plumbing cubes whose characteristic weight is at most `N`. -/
@[expose] def characteristicCubeWeightSublevel (P : PlumbingGraph V) (k : P.characteristicVectors)
    (N : ℤ) : Set (PlumbingCube V) :=
  {C | C.characteristicWeight P k ≤ N}

/-- Membership in a cube-weight sublevel set is the corresponding weight inequality. -/
@[simp]
theorem mem_characteristicCubeWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (C : PlumbingCube V) :
    C ∈ P.characteristicCubeWeightSublevel k N ↔ C.characteristicWeight P k ≤ N :=
  Iff.rfl

/-- Characteristic cube-weight sublevel sets increase with the level. -/
theorem characteristicCubeWeightSublevel_mono (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) :
    P.characteristicCubeWeightSublevel k N ⊆ P.characteristicCubeWeightSublevel k M :=
  fun _ hC ↦ hC.trans hNM

/-- The lower face of a cube in a characteristic-weight sublevel remains in that sublevel. -/
theorem lowerFace_mem_characteristicCubeWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {C : PlumbingCube V}
    (hC : C ∈ P.characteristicCubeWeightSublevel k N) {v : V} (hv : v ∈ C.directions) :
    C.lowerFace v hv ∈ P.characteristicCubeWeightSublevel k N :=
  (PlumbingCube.characteristicWeight_lowerFace_le P k C hv).trans hC

/-- The upper face of a cube in a characteristic-weight sublevel remains in that sublevel. -/
theorem upperFace_mem_characteristicCubeWeightSublevel (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N : ℤ} {C : PlumbingCube V}
    (hC : C ∈ P.characteristicCubeWeightSublevel k N) {v : V} (hv : v ∈ C.directions) :
    C.upperFace v hv ∈ P.characteristicCubeWeightSublevel k N :=
  (PlumbingCube.characteristicWeight_upperFace_le P k C hv).trans hC

/-- On a negative-definite plumbing every characteristic cube-weight sublevel set is finite.

A cube in the sublevel has its base point in the point-weight sublevel, while its direction set
belongs to the finite type `Finset V`. The pair of these data determines the cube. -/
theorem finite_characteristicCubeWeightSublevel (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) (N : ℤ) :
    (P.characteristicCubeWeightSublevel k N).Finite := by
  let encode : PlumbingCube V → (V → ℤ) × Finset V := fun C ↦ (C.base, C.directions)
  have hencode : Function.Injective encode := by
    intro C D hCD
    exact PlumbingCube.ext (congrArg Prod.fst hCD) (congrArg Prod.snd hCD)
  have hproduct :
      ({x : V → ℤ | P.characteristicWeight k x ≤ N} ×ˢ
        (Set.univ : Set (Finset V))).Finite :=
    (P.finite_setOfPred_characteristicWeight_le h k N).prod Set.finite_univ
  refine (hproduct.preimage hencode.injOn).subset ?_
  intro C hC
  refine ⟨?_, Set.mem_univ C.directions⟩
  have hbase := P.characteristicWeight_le_characteristicCubeWeight_base
    k C.base C.directions
  rw [← PlumbingCube.characteristicWeight_mk] at hbase
  exact hbase.trans ((P.mem_characteristicCubeWeightSublevel k N C).mp hC)

end PlumbingGraph

end TauCeti
