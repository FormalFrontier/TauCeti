/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import TauCeti.LowDimTopology.Plumbing.Differential

/-!
# The cubical grading of the lattice differential

The generators of Némethi's lattice complex are plumbing cubes, graded by the cardinality of
their direction sets. This file splits the total plumbing-chain module into its cubical-degree
submodules and restricts the lattice differential to maps

`C_{q + 1} → C_q`.

Every term in the differential of a cube is one of its lower or upper codimension-one faces, so
the degree drop follows from the face-dimension API. Restricting the already-proved total
square-zero identity then shows that consecutive graded differentials compose to zero. These
maps are the data needed to package lattice homology as a `ℕ`-indexed chain complex, rather than
only as the ungraded short complex currently used for its total homology.

## Main definitions

* `TauCeti.PlumbingChain.degreePart`: chains supported on cubes of one cubical dimension.
* `TauCeti.PlumbingGraph.latticeDifferentialDegree`: the lattice differential restricted from
  cubical degree `q + 1` to degree `q`.

## Main results

* `TauCeti.PlumbingGraph.latticeDifferentialOnGenerator_mem_degreePart`: every face term of a
  degree-`q + 1` cube has degree `q`.
* `TauCeti.PlumbingGraph.latticeDifferential_mem_degreePart`: the total differential maps the
  degree-`q + 1` submodule into the degree-`q` submodule.
* `TauCeti.PlumbingGraph.latticeDifferentialDegree_comp`: consecutive graded differentials
  compose to zero.

## References

This supplies the cubical grading needed by the lattice-homology construction in
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"). The grading
by cube dimension and its degree-minus-one differential follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

namespace PlumbingChain

variable (V : Type*)

/-- The submodule of plumbing chains supported on cubes of cubical dimension `q`. -/
noncomputable def degreePart (q : ℕ) : Submodule PlumbingCoefficient (PlumbingChain V) :=
  Finsupp.supported PlumbingCoefficient PlumbingCoefficient {C | C.dimension = q}

/-- A chain lies in cubical degree `q` exactly when every cube in its support has dimension
`q`. -/
theorem mem_degreePart (q : ℕ) (c : PlumbingChain V) :
    c ∈ degreePart V q ↔ ∀ C ∈ c.support, C.dimension = q := by
  rw [degreePart, Finsupp.mem_supported]
  rfl

/-- A single cube of dimension `q` gives a chain in cubical degree `q`, with any coefficient. -/
theorem single_mem_degreePart {q : ℕ} (C : PlumbingCube V) (a : PlumbingCoefficient)
    (hC : C.dimension = q) :
    Finsupp.single C a ∈ degreePart V q :=
  Finsupp.single_mem_supported PlumbingCoefficient a hC

/-- A nonzero single-cube chain has cubical degree `q` exactly when its cube has dimension `q`. -/
theorem single_mem_degreePart_iff {q : ℕ} (C : PlumbingCube V) {a : PlumbingCoefficient}
    (ha : a ≠ 0) :
    Finsupp.single C a ∈ degreePart V q ↔ C.dimension = q := by
  rw [mem_degreePart]
  simp [Finsupp.support_single C ha]

/-- Distinct cubical-degree submodules intersect trivially. -/
theorem disjoint_degreePart {q r : ℕ} (hqr : q ≠ r) :
    Disjoint (degreePart V q) (degreePart V r) := by
  rw [Submodule.disjoint_def]
  intro c hcq hcr
  apply Finsupp.ext
  intro C
  by_cases hC : C ∈ c.support
  · exact (hqr (((mem_degreePart V q c).mp hcq C hC).symm.trans
      ((mem_degreePart V r c).mp hcr C hC))).elim
  · simp [Finsupp.notMem_support_iff.mp hC]

end PlumbingChain

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The differential of a degree-`q + 1` cube is supported on cubes of degree `q`. -/
theorem latticeDifferentialOnGenerator_mem_degreePart
    (P : PlumbingGraph V) (k : P.characteristicVectors) {q : ℕ} (C : PlumbingCube V)
    (hC : C.dimension = q + 1) :
    P.latticeDifferentialOnGenerator k C ∈ PlumbingChain.degreePart V q := by
  classical
  rw [PlumbingChain.mem_degreePart]
  intro D hD
  rw [latticeDifferentialOnGenerator_def] at hD
  obtain ⟨v, hv, hDv⟩ := Finsupp.mem_support_finsetSum D hD
  rw [Finsupp.mem_support_iff] at hDv
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hDv
  split at hDv
  · rename_i hLower
    subst D
    rw [C.dimension_lowerFace_of_mem v.property, hC, Nat.add_sub_cancel]
  · split at hDv
    · rename_i hUpper
      subst D
      rw [C.dimension_upperFace_of_mem v.property, hC, Nat.add_sub_cancel]
    · simp at hDv

/-- The lattice differential maps chains of cubical degree `q + 1` to chains of degree `q`. -/
theorem latticeDifferential_mem_degreePart
    (P : PlumbingGraph V) (k : P.characteristicVectors) {q : ℕ} {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.degreePart V (q + 1)) :
    P.latticeDifferential k c ∈ PlumbingChain.degreePart V q := by
  rw [PlumbingChain.degreePart, Finsupp.supported_eq_span_single] at hc
  refine Submodule.span_induction
    (p := fun c _ => P.latticeDifferential k c ∈ PlumbingChain.degreePart V q)
    ?_ (by simpa only [map_zero] using Submodule.zero_mem (PlumbingChain.degreePart V q))
      ?_ ?_ hc
  · rintro _ ⟨C, hC, rfl⟩
    rw [latticeDifferential_single]
    exact Submodule.smul_mem _ _
      (P.latticeDifferentialOnGenerator_mem_degreePart k C hC)
  · intro x y _ _ hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- The lattice differential restricted from cubical degree `q + 1` to cubical degree `q`. -/
noncomputable def latticeDifferentialDegree
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    PlumbingChain.degreePart V (q + 1) →ₗ[PlumbingCoefficient]
      PlumbingChain.degreePart V q :=
  ((P.latticeDifferential k).domRestrict (PlumbingChain.degreePart V (q + 1))).codRestrict
    (PlumbingChain.degreePart V q) fun c =>
      P.latticeDifferential_mem_degreePart k c.property

/-- The graded differential agrees with the total lattice differential after forgetting the
degree-submodule wrappers. -/
@[simp]
theorem latticeDifferentialDegree_apply
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ)
    (c : PlumbingChain.degreePart V (q + 1)) :
    (P.latticeDifferentialDegree k q c : PlumbingChain V) =
      P.latticeDifferential k c :=
  (rfl)

/-- Consecutive cubical-degree lattice differentials compose to zero. -/
theorem latticeDifferentialDegree_comp
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeDifferentialDegree k q).comp
        (P.latticeDifferentialDegree k (q + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have h := LinearMap.congr_fun (P.latticeDifferential_comp_self k) (c : PlumbingChain V)
  change P.latticeDifferential k (P.latticeDifferential k (c : PlumbingChain V)) = 0
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

end PlumbingGraph

end TauCeti
