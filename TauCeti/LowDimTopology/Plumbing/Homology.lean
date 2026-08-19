/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.LowDimTopology.Plumbing.Differential
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Lattice homology over `𝔽₂[U]`

This file packages the characteristic-two plumbing-lattice differential as a short complex and
defines its homology. For a plumbing graph `P` and characteristic covector `k`, the same weighted
differential occurs on both sides of the short complex

`PlumbingChain V → PlumbingChain V → PlumbingChain V`.

The relation `∂² = 0` proved in `Differential.lean` makes this a short complex. Its homology is
therefore the kernel of the differential modulo its range, with coefficients in `𝔽₂[U]`.

The construction deliberately uses Mathlib's `ShortComplex` homology API. Thus its existing
`cycles`, `homologyπ`, and homology-map interfaces apply directly, without a parallel
plumbing-specific quotient API.

This is the ungraded total module obtained from all cubical dimensions. The cubical and weight
gradings, integral signs, the `ℍ⁰` variant, and invariance under Neumann moves are separate later
stages. As a first computation, the zero-vertex plumbing has zero differential, so its homology is
canonically isomorphic to its whole chain module.

## Main definitions

* `TauCeti.PlumbingGraph.latticeShortComplex`: the short complex with the lattice differential
  in both positions.
* `TauCeti.PlumbingGraph.latticeShortComplex_exact_iff_range_eq_ker`: that short complex is exact
  exactly when the boundaries of the lattice differential are all of its cycles.
* `TauCeti.PlumbingGraph.latticeHomology`: its canonical `𝔽₂[U]`-module homology.
* `TauCeti.PlumbingGraph.latticeHomologyCycleMap`: the map taking a coefficient to the homology
  class of its multiple of a fixed cycle.
* `TauCeti.PlumbingGraph.latticeHomologyIsoChainOfIsEmpty`: the homology of a zero-vertex
  plumbing is its full chain module.
* `TauCeti.PlumbingGraph.latticeHomologyIsoCoefficientOfIsEmpty`: that chain module has one
  generator, so the homology is a universe-lifted copy of `𝔽₂[U]`.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology `ℍ⁻` as a polynomial module built from lattice points and weight
functions. The characteristic-two coefficient stage and the weighted cubical differential follow
A. Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory

namespace PlumbingGraph

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]

/-- The short complex whose two maps are the characteristic-two lattice differential.

The three objects are the total plumbing-chain module on all cubical dimensions. The short-complex
condition is exactly `latticeDifferential_comp_self`. -/
noncomputable def latticeShortComplex
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    ShortComplex (ModuleCat PlumbingCoefficient) :=
  ShortComplex.moduleCatMk (P.latticeDifferential k) (P.latticeDifferential k)
    (P.latticeDifferential_comp_self k)

/-- The left object of the lattice short complex is the plumbing-chain module. -/
@[simp]
theorem latticeShortComplex_X₁ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.latticeShortComplex k).X₁ =
      ModuleCat.of PlumbingCoefficient (PlumbingChain V) := (rfl)

/-- The middle object of the lattice short complex is the plumbing-chain module. -/
@[simp]
theorem latticeShortComplex_X₂ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.latticeShortComplex k).X₂ =
      ModuleCat.of PlumbingCoefficient (PlumbingChain V) := (rfl)

/-- The right object of the lattice short complex is the plumbing-chain module. -/
@[simp]
theorem latticeShortComplex_X₃ (P : PlumbingGraph V) (k : P.characteristicVectors) :
    (P.latticeShortComplex k).X₃ =
      ModuleCat.of PlumbingCoefficient (PlumbingChain V) := (rfl)

/-- The left map of the lattice short complex is the lattice differential. -/
@[simp]
theorem latticeShortComplex_f (P : PlumbingGraph V) (k : P.characteristicVectors) :
    HEq (P.latticeShortComplex k).f
      (ModuleCat.ofHom (P.latticeDifferential k)) := (HEq.rfl)

/-- The right map of the lattice short complex is the lattice differential. -/
@[simp]
theorem latticeShortComplex_g (P : PlumbingGraph V) (k : P.characteristicVectors) :
    HEq (P.latticeShortComplex k).g
      (ModuleCat.ofHom (P.latticeDifferential k)) := (HEq.rfl)

/-- Exactness of the lattice short complex says exactly that the boundaries of the lattice
differential are all of its cycles.

This is the chain-level reading of the vanishing of lattice homology. It has to be stated here:
the body of `latticeShortComplex` is not exposed, so a downstream file cannot see that its three
objects and two maps are the plumbing-chain module and the lattice differential, and hence cannot
apply `ShortComplex.moduleCat_exact_iff_range_eq_ker` to it. -/
theorem latticeShortComplex_exact_iff_range_eq_ker (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    (P.latticeShortComplex k).Exact ↔
      LinearMap.range (P.latticeDifferential k) = LinearMap.ker (P.latticeDifferential k) :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker _

/-- The characteristic-two lattice homology module: the homology of the weighted
plumbing-lattice short complex.

This is Mathlib's canonical homology object, so the generic `ShortComplex.cycles`,
`ShortComplex.homologyπ`, and homology-map API can be used directly via `latticeHomology_def`. -/
noncomputable def latticeHomology
    (P : PlumbingGraph V) (k : P.characteristicVectors) : ModuleCat PlumbingCoefficient :=
  (P.latticeShortComplex k).homology

/-- Lattice homology is the canonical homology object of the lattice short complex. -/
@[simp]
theorem latticeHomology_def (P : PlumbingGraph V) (k : P.characteristicVectors) :
    P.latticeHomology k = (P.latticeShortComplex k).homology := by
  unfold latticeHomology
  rfl

/-- The linear map sending `a : 𝔽₂[U]` to the homology class of `a • c`, for a lattice
cycle `c`. -/
noncomputable def latticeHomologyCycleMap (P : PlumbingGraph V) (k : P.characteristicVectors)
    (c : PlumbingChain V) (hc : P.latticeDifferential k c = 0) :
    PlumbingCoefficient →ₗ[PlumbingCoefficient] P.latticeHomology k :=
  let S := P.latticeShortComplex k
  let z : LinearMap.ker S.g.hom := ⟨c, by
    change P.latticeDifferential k c = 0
    exact hc⟩
  let q : S.moduleCatLeftHomologyData.H :=
    (LinearMap.range S.moduleCatToCycles).mkQ z
  S.moduleCatHomologyIso.inv.hom.comp
    (LinearMap.toSpanSingleton PlumbingCoefficient S.moduleCatLeftHomologyData.H q)

/-- A coefficient maps to zero under `latticeHomologyCycleMap` exactly when its multiple of the
cycle is a boundary. -/
theorem latticeHomologyCycleMap_apply_eq_zero_iff (P : PlumbingGraph V)
    (k : P.characteristicVectors) (c : PlumbingChain V)
    (hc : P.latticeDifferential k c = 0) (a : PlumbingCoefficient) :
    P.latticeHomologyCycleMap k c hc a = 0 ↔
      a • c ∈ LinearMap.range (P.latticeDifferential k) := by
  let S := P.latticeShortComplex k
  let z : LinearMap.ker S.g.hom := ⟨c, by
    change P.latticeDifferential k c = 0
    exact hc⟩
  let q : S.moduleCatLeftHomologyData.H :=
    (LinearMap.range S.moduleCatToCycles).mkQ z
  change S.moduleCatHomologyIso.inv (a • q) = 0 ↔ _
  constructor
  · intro ha
    have hq : a • q = 0 := by
      have hz := S.moduleCatHomologyIso.inv_hom_id_apply (a • q)
      rw [ha, map_zero] at hz
      exact hz.symm
    change (LinearMap.range S.moduleCatToCycles).mkQ (a • z) = 0 at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨b, hb⟩ := hq
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hz : a • z ∈ LinearMap.range S.moduleCatToCycles := by
      refine ⟨b, ?_⟩
      apply Subtype.ext
      exact hb
    have hq : a • q = 0 := by
      change (LinearMap.range S.moduleCatToCycles).mkQ (a • z) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hz
    exact (congrArg (fun x => S.moduleCatHomologyIso.inv x) hq).trans (map_zero _)

/-- The characteristic-two lattice homology of a zero-vertex plumbing is canonically isomorphic
to its whole plumbing-chain module. -/
noncomputable def latticeHomologyIsoChainOfIsEmpty [IsEmpty V]
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    P.latticeHomology k ≅ ModuleCat.of PlumbingCoefficient (PlumbingChain V) := by
  let S := P.latticeShortComplex k
  have hf : S.f = 0 := by
    have h := P.latticeShortComplex_f k
    rw [P.latticeDifferential_eq_zero_of_isEmpty k] at h
    exact eq_of_heq h
  have hg : S.g = 0 := by
    have h := P.latticeShortComplex_g k
    rw [P.latticeDifferential_eq_zero_of_isEmpty k] at h
    exact eq_of_heq h
  exact (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoX₂ hg

/-- The characteristic-two lattice homology of a zero-vertex plumbing is a universe-lifted copy
of the coefficient module `𝔽₂[U]`. -/
noncomputable def latticeHomologyIsoCoefficientOfIsEmpty [IsEmpty V]
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    P.latticeHomology k ≅
      ModuleCat.of PlumbingCoefficient (ULift.{u} PlumbingCoefficient) := by
  let C : PlumbingCube V := { base := isEmptyElim, directions := ∅ }
  letI : Subsingleton (PlumbingCube V) :=
    ⟨fun A B => PlumbingCube.ext (Subsingleton.elim A.base B.base)
      (Subsingleton.elim A.directions B.directions)⟩
  exact P.latticeHomologyIsoChainOfIsEmpty k ≪≫
    ((Finsupp.uniqueLinearEquiv PlumbingCoefficient PlumbingCoefficient C).trans
      ULift.moduleEquiv.symm).toModuleIso

end PlumbingGraph

end TauCeti
