/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Grading
public import TauCeti.LowDimTopology.Plumbing.Homology
public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# The `U`-tower in characteristic-two lattice homology

This file proves that the lattice homology of a negative-definite plumbing graph is nonzero, and
locates a free `𝔽₂[U]`-tower inside it.

The mechanism is an augmentation. Write `m` for the minimal value `sInfCharacteristicWeight` of
the characteristic weight function `χ_k`, which a negative-definite plumbing attains. Send the
zero-dimensional cube at a lattice point `x` to `U ^ (χ_k(x) - m)` and every cube of positive
dimension to `0`. The resulting `𝔽₂[U]`-linear map kills the lattice differential: a cube of
dimension at least two has all its codimension-one faces of positive dimension, and the two faces
of an edge contribute `U ^ (w - m)` each, for the same edge weight `w`, hence cancel in
characteristic two. So the augmentation vanishes on boundaries, while a lattice point of minimal
weight is a cycle sent to `1`.

Two consequences follow. First, lattice homology is not zero: the short complex of the lattice
differential is not exact. Second, and more precisely, the class of a minimal-weight lattice point
generates a *free* `𝔽₂[U]`-submodule: no nonzero multiple `U ^ j` of it is a boundary, an infinite
`U`-tower. Nothing here locates that tower in a homological grading, so no `d`-invariant is
identified; in Némethi's theory it is the graded bottom of such a tower that gives the
`d`-invariant of the plumbed three-manifold, and a graded statement to that effect is left to
future work.

## Main definitions

* `TauCeti.PlumbingGraph.latticeAugmentation`: the `𝔽₂[U]`-linear augmentation of the plumbing
  chain module.

## Main results

* `TauCeti.PlumbingGraph.latticeAugmentation_comp_latticeDifferential`: the augmentation kills
  boundaries.
* `TauCeti.PlumbingGraph.exists_cycle_latticeAugmentation_eq_one`: a lattice point of minimal
  characteristic weight is a cycle with augmentation `1`.
* `TauCeti.PlumbingGraph.exists_cycle_eq_zero_of_smul_mem_range_latticeDifferential`: that cycle
  satisfies the chain-level nonboundary criterion for the `U`-tower.
* `TauCeti.PlumbingGraph.exists_injective_latticeHomologyCycleMap`: the resulting map from
  `𝔽₂[U]` into lattice homology is injective.
* `TauCeti.PlumbingGraph.not_isZero_latticeHomology`: the lattice homology of a negative-definite
  plumbing is nonzero.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L ("lattice homology"),
which asks for Némethi's lattice homology as a `ℤ[U]`-module together with computations of
concrete negative-definite plumbings and `d`-invariant analogues. The `U`-tower and the role of
`min χ_k` follow A. Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory

namespace PlumbingGraph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- The coefficient the lattice augmentation assigns to a plumbing cube: the power
`U ^ (χ_k(x) - min χ_k)` on the zero-dimensional cube at the lattice point `x`, and `0` on every
cube of positive dimension. -/
noncomputable def latticeAugmentationCoefficient (P : PlumbingGraph V)
    (k : P.characteristicVectors) (C : PlumbingCube V) : PlumbingCoefficient :=
  if C.directions = ∅ then
    Polynomial.X ^ (P.characteristicWeight k C.base - P.sInfCharacteristicWeight k).toNat
  else 0

/-- On a zero-dimensional cube the augmentation coefficient is the `U`-power measuring how far the
base point sits above the minimal characteristic weight. -/
@[simp]
theorem latticeAugmentationCoefficient_of_directions_eq_empty (P : PlumbingGraph V)
    (k : P.characteristicVectors) {C : PlumbingCube V} (hC : C.directions = ∅) :
    P.latticeAugmentationCoefficient k C =
      Polynomial.X ^ (P.characteristicWeight k C.base - P.sInfCharacteristicWeight k).toNat := by
  simp [latticeAugmentationCoefficient, hC]

/-- On a cube of positive dimension the augmentation coefficient vanishes. -/
@[simp]
theorem latticeAugmentationCoefficient_of_directions_ne_empty (P : PlumbingGraph V)
    (k : P.characteristicVectors) {C : PlumbingCube V} (hC : C.directions ≠ ∅) :
    P.latticeAugmentationCoefficient k C = 0 := by
  simp [latticeAugmentationCoefficient, hC]

/-- The `𝔽₂[U]`-linear augmentation of the plumbing chain module. -/
noncomputable def latticeAugmentation (P : PlumbingGraph V) (k : P.characteristicVectors) :
    PlumbingChain V →ₗ[PlumbingCoefficient] PlumbingCoefficient :=
  Finsupp.linearCombination PlumbingCoefficient (P.latticeAugmentationCoefficient k)

/-- The augmentation of a single cube with coefficient `a` is `a` times the cube's augmentation
coefficient. -/
@[simp]
theorem latticeAugmentation_single (P : PlumbingGraph V) (k : P.characteristicVectors)
    (C : PlumbingCube V) (a : PlumbingCoefficient) :
    P.latticeAugmentation k (Finsupp.single C a) = a * P.latticeAugmentationCoefficient k C := by
  rw [latticeAugmentation, Finsupp.linearCombination_single, smul_eq_mul]

/-- The augmentation vanishes on chains supported in positive cubical degree: it only sees
lattice points. -/
theorem latticeAugmentation_eq_zero_of_mem_degreePart (P : PlumbingGraph V)
    (k : P.characteristicVectors) {q : ℕ} (hq : q ≠ 0) {c : PlumbingChain V}
    (hc : c ∈ PlumbingChain.degreePart V q) : P.latticeAugmentation k c = 0 := by
  rw [latticeAugmentation, Finsupp.linearCombination_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  have hdim : C.dimension = q := (PlumbingChain.mem_degreePart V q c).mp hc C hC
  have hne : C.directions ≠ ∅ := by
    intro hempty
    rw [PlumbingCube.dimension, hempty, Finset.card_empty] at hdim
    exact hq hdim.symm
  simp [P.latticeAugmentationCoefficient_of_directions_ne_empty k hne]

/-- The augmentation kills the differential of a single cube.

A cube of dimension at least two has every codimension-one face of positive dimension, so all the
augmentation coefficients occurring vanish. For an edge the two faces contribute the *same*
`U`-power `U ^ (w - m)`, where `w` is the weight of the edge and `m` the minimal characteristic
weight, because a face exponent is exactly the drop from `w` to the weight of that face. In
characteristic two the two contributions cancel. -/
theorem latticeAugmentation_latticeDifferentialOnGenerator (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) (C : PlumbingCube V) :
    P.latticeAugmentation k (P.latticeDifferentialOnGenerator k C) = 0 := by
  classical
  rw [latticeDifferentialOnGenerator_def, map_sum]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [map_add, latticeAugmentation_single, latticeAugmentation_single]
  by_cases herase : C.directions.erase v.val = ∅
  · -- The cube is an edge: both faces are lattice points and their contributions agree.
    have hlower : (C.lowerFace v.val v.property).directions = ∅ := by
      rw [PlumbingCube.lowerFace_directions, herase]
    have hupper : (C.upperFace v.val v.property).directions = ∅ := by
      rw [PlumbingCube.upperFace_directions, herase]
    rw [P.latticeAugmentationCoefficient_of_directions_eq_empty k hlower,
      P.latticeAugmentationCoefficient_of_directions_eq_empty k hupper,
      ← pow_add, ← pow_add]
    have hlowerbase :
        P.characteristicWeight k (C.lowerFace v.val v.property).base =
          PlumbingCube.characteristicWeight P k (C.lowerFace v.val v.property) := by
      rw [PlumbingCube.characteristicWeight_def, hlower,
        PlumbingGraph.characteristicCubeWeight_empty]
    have hupperbase :
        P.characteristicWeight k (C.upperFace v.val v.property).base =
          PlumbingCube.characteristicWeight P k (C.upperFace v.val v.property) := by
      rw [PlumbingCube.characteristicWeight_def, hupper,
        PlumbingGraph.characteristicCubeWeight_empty]
    have hlowerexp :
        (PlumbingCube.characteristicLowerFaceExponent P k C v.val : ℤ) =
          PlumbingCube.characteristicWeight P k C -
            PlumbingCube.characteristicWeight P k (C.lowerFace v.val v.property) := by
      rw [PlumbingCube.characteristicLowerFaceExponent_natCast, PlumbingCube.lowerFace_def]
    have hupperexp :
        (PlumbingCube.characteristicUpperFaceExponent P k C v.property : ℤ) =
          PlumbingCube.characteristicWeight P k C -
            PlumbingCube.characteristicWeight P k (C.upperFace v.val v.property) :=
      PlumbingCube.characteristicUpperFaceExponent_natCast P k C v.property
    have hlowerle :
        PlumbingCube.characteristicWeight P k (C.lowerFace v.val v.property) ≤
          PlumbingCube.characteristicWeight P k C :=
      PlumbingCube.characteristicWeight_lowerFace_le P k C v.property
    have hupperle :
        PlumbingCube.characteristicWeight P k (C.upperFace v.val v.property) ≤
          PlumbingCube.characteristicWeight P k C :=
      PlumbingCube.characteristicWeight_upperFace_le P k C v.property
    have hlowermin :
        P.sInfCharacteristicWeight k ≤
          P.characteristicWeight k (C.lowerFace v.val v.property).base :=
      P.sInfCharacteristicWeight_le h k _
    have huppermin :
        P.sInfCharacteristicWeight k ≤
          P.characteristicWeight k (C.upperFace v.val v.property).base :=
      P.sInfCharacteristicWeight_le h k _
    have hexp :
        PlumbingCube.characteristicLowerFaceExponent P k C v.val +
            (P.characteristicWeight k (C.lowerFace v.val v.property).base -
              P.sInfCharacteristicWeight k).toNat =
          PlumbingCube.characteristicUpperFaceExponent P k C v.property +
            (P.characteristicWeight k (C.upperFace v.val v.property).base -
              P.sInfCharacteristicWeight k).toNat := by
      rw [hlowerbase] at hlowermin ⊢
      rw [hupperbase] at huppermin ⊢
      omega
    rw [hexp]
    exact CharTwo.add_self_eq_zero (R := PlumbingCoefficient) _
  · -- The cube has dimension at least two, so neither face is a lattice point.
    have hlower : (C.lowerFace v.val v.property).directions ≠ ∅ := by
      rw [PlumbingCube.lowerFace_directions]
      exact herase
    have hupper : (C.upperFace v.val v.property).directions ≠ ∅ := by
      rw [PlumbingCube.upperFace_directions]
      exact herase
    rw [P.latticeAugmentationCoefficient_of_directions_ne_empty k hlower,
      P.latticeAugmentationCoefficient_of_directions_ne_empty k hupper]
    simp

/-- The augmentation kills the lattice differential, so it descends to lattice homology. -/
theorem latticeAugmentation_comp_latticeDifferential (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) :
    (P.latticeAugmentation k).comp (P.latticeDifferential k) = 0 := by
  classical
  refine Finsupp.lhom_ext' fun C => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
  rw [latticeDifferential_single, map_smul,
    P.latticeAugmentation_latticeDifferentialOnGenerator h k C, smul_zero]

/-- The augmentation vanishes on every boundary. -/
theorem latticeAugmentation_eq_zero_of_mem_range (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) {c : PlumbingChain V}
    (hc : c ∈ LinearMap.range (P.latticeDifferential k)) :
    P.latticeAugmentation k c = 0 := by
  obtain ⟨b, rfl⟩ := hc
  exact congrFun (congrArg DFunLike.coe (P.latticeAugmentation_comp_latticeDifferential h k)) b

/-- A lattice point of minimal characteristic weight gives a cycle whose augmentation is `1`. -/
theorem exists_cycle_latticeAugmentation_eq_one (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) :
    ∃ c : PlumbingChain V, P.latticeDifferential k c = 0 ∧ P.latticeAugmentation k c = 1 := by
  obtain ⟨x, hx⟩ := P.exists_characteristicWeight_eq_sInfCharacteristicWeight h k
  refine ⟨Finsupp.single ({ base := x, directions := ∅ } : PlumbingCube V) 1, ?_, ?_⟩
  · rw [latticeDifferential_single,
      P.latticeDifferentialOnGenerator_eq_zero_of_directions_eq_empty k rfl, smul_zero]
  · rw [latticeAugmentation_single,
      P.latticeAugmentationCoefficient_of_directions_eq_empty k rfl, hx]
    simp

/-- The `U`-tower: the class of a minimal-weight lattice point spans a free `𝔽₂[U]`-submodule of
lattice homology, since no nonzero multiple of that cycle is a boundary. -/
theorem exists_cycle_eq_zero_of_smul_mem_range_latticeDifferential (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) :
    ∃ c : PlumbingChain V, P.latticeDifferential k c = 0 ∧
      ∀ a : PlumbingCoefficient,
        a • c ∈ LinearMap.range (P.latticeDifferential k) → a = 0 := by
  obtain ⟨c, hcycle, hone⟩ := P.exists_cycle_latticeAugmentation_eq_one h k
  refine ⟨c, hcycle, fun a ha => ?_⟩
  have := P.latticeAugmentation_eq_zero_of_mem_range h k ha
  rwa [map_smul, hone, smul_eq_mul, mul_one] at this

/-- A cycle with augmentation `1` generates a free copy of `𝔽₂[U]` in lattice homology. -/
theorem latticeHomologyCycleMap_injective (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) (c : PlumbingChain V)
    (hc : P.latticeDifferential k c = 0) (hone : P.latticeAugmentation k c = 1) :
    Function.Injective (P.latticeHomologyCycleMap k c hc) := by
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  have hrange : a • c ∈ LinearMap.range (P.latticeDifferential k) :=
    (P.latticeHomologyCycleMap_apply_eq_zero_iff k c hc a).mp ha
  have hzero := P.latticeAugmentation_eq_zero_of_mem_range h k hrange
  rwa [map_smul, hone, smul_eq_mul, mul_one] at hzero

/-- The class of a minimal-weight lattice point embeds a free `𝔽₂[U]`-submodule into the
lattice homology of a negative-definite plumbing. -/
theorem exists_injective_latticeHomologyCycleMap (P : PlumbingGraph V)
    (h : P.IsNegativeDefinite) (k : P.characteristicVectors) :
    ∃ (c : PlumbingChain V) (hc : P.latticeDifferential k c = 0),
      P.latticeAugmentation k c = 1 ∧
        Function.Injective (P.latticeHomologyCycleMap k c hc) := by
  obtain ⟨c, hc, hone⟩ := P.exists_cycle_latticeAugmentation_eq_one h k
  exact ⟨c, hc, hone, P.latticeHomologyCycleMap_injective h k c hc hone⟩

/-! ### Nonvanishing of lattice homology -/

/-- The lattice short complex of a negative-definite plumbing is not exact: the class of a
minimal-weight lattice point is a cycle that is not a boundary. -/
theorem not_exact_latticeShortComplex (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) : ¬ (P.latticeShortComplex k).Exact := by
  obtain ⟨c, hcycle, hone⟩ := P.exists_cycle_latticeAugmentation_eq_one h k
  rw [P.latticeShortComplex_exact_iff_range_eq_ker k]
  intro hexact
  have hzero := P.latticeAugmentation_eq_zero_of_mem_range h k
    (hexact ▸ LinearMap.mem_ker.mpr hcycle)
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- The characteristic-two lattice homology of a negative-definite plumbing is nonzero.

This is the first nonvanishing statement for the invariant: up to now the only computed lattice
homology was that of the zero-vertex plumbing. -/
theorem not_isZero_latticeHomology (P : PlumbingGraph V) (h : P.IsNegativeDefinite)
    (k : P.characteristicVectors) : ¬ Limits.IsZero (P.latticeHomology k) := by
  rw [latticeHomology_def, ← ShortComplex.exact_iff_isZero_homology]
  exact P.not_exact_latticeShortComplex h k

end PlumbingGraph

end TauCeti
