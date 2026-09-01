/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.InnerProductSpace.PiL2

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# The realization of a simplex boundary

This file proves that the geometric realization of the boundary of the standard
`(n + 1)`-simplex is homeomorphic to the unit `n`-sphere.  It completes the
"realization round-trips" acceptance check in layer 11 of the geometric-topology roadmap.

The proof uses barycentric coordinates twice.  First, they identify the weak realization of the
abstract boundary with the frontier of the convex hull of an affine basis of
`EuclideanSpace ℝ (Fin (n + 1))`.  On each facet the inverse is the ordinary barycentric-coordinate
map, and a finite closed-cover argument proves that these local inverses assemble continuously.
Second, Mathlib's `exists_homeomorph_image_interior_closure_frontier_eq_unitBall` sends the
frontier of this full-dimensional convex simplex to the unit sphere.

The simplex-boundary model follows Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 2.

## Main definitions

* `AbstractSimplicialComplex.standardSuccSimplexBoundary`: the boundary complex of the standard
  `(n + 1)`-simplex, with vertex type `Fin (n + 2)`.
* `AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere`: its
  realization is homeomorphic to the unit sphere in `EuclideanSpace ℝ (Fin (n + 1))`.
-/

public section

noncomputable section

open Bornology Metric Set TauCeti.SetLike

namespace AbstractSimplicialComplex

/-- Decide equality on `Fin n` classically, at high priority, throughout this file.  The
realization of a complex is indexed by a `DecidableEq` instance on its vertex type, and the
arguments below combine terms whose instances would otherwise be the syntactically different
`instDecidableEqFin`; forcing a single classical instance keeps them definitionally equal. -/
local instance (priority := 2000) finDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  Classical.decEq _

private noncomputable def sphereAffineBasis (n : ℕ) :
    AffineBasis (Fin (n + 2)) ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  Classical.choice (AffineBasis.exists_affineBasis_of_finiteDimensional (by simp))

private noncomputable def simplexPolytope (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  convexHull ℝ (range (sphereAffineBasis n))

private theorem mem_frontier_simplexPolytope_iff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    x ∈ frontier (simplexPolytope n) ↔
      (∀ i, 0 ≤ (sphereAffineBasis n).coord i x) ∧
        ∃ i, (sphereAffineBasis n).coord i x = 0 := by
  let b := sphereAffineBasis n
  have hclosed : IsClosed (convexHull ℝ (range b)) :=
    ((finite_range b).isCompact_convexHull ℝ).isClosed
  rw [simplexPolytope, frontier, hclosed.closure_eq, b.interior_convexHull,
    b.convexHull_eq_nonneg_coord]
  simp only [mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨hnonneg, hnotpos⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnotpos
    exact ⟨hnonneg, i, le_antisymm (le_of_not_gt hi) (hnonneg i)⟩
  · rintro ⟨hnonneg, i, hi⟩
    exact ⟨hnonneg, fun hpos => (hpos i).ne' hi⟩

private theorem realization_sum_eq_one (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) :
    ∑ i, x.1 i = 1 := by
  let y : StandardSimplex (carrier (standardSuccSimplexBoundary n) x).1 :=
    ⟨x.1, mem_convexHull_carrier _ x⟩
  rw [← Finsupp.sum_fintype x.1 (fun _ r => r) (fun _ => rfl)]
  exact StandardSimplex.sum_eq_one y

private noncomputable def boundaryToPolytope (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  Finset.univ.affineCombination ℝ (sphereAffineBasis n) fun i => x.1 i

private theorem boundaryToPolytope_eq_sum (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) :
    boundaryToPolytope n x = ∑ i, x.1 i • sphereAffineBasis n i := by
  rw [boundaryToPolytope,
    Finset.affineCombination_eq_linear_combination _ _ _ (realization_sum_eq_one n x)]

@[simp]
private theorem boundaryToPolytope_coord (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) (i : Fin (n + 2)) :
    (sphereAffineBasis n).coord i (boundaryToPolytope n x) = x.1 i := by
  rw [boundaryToPolytope]
  exact (sphereAffineBasis n).coord_apply_combination_of_mem
    (Finset.mem_univ i) (realization_sum_eq_one n x)

private theorem continuous_boundaryToPolytope (n : ℕ) :
    Continuous (boundaryToPolytope n) := by
  apply continuous_iff_faceInclusion.2
  intro σ
  have hcoord (i : Fin (n + 2)) :
      Continuous (fun x : StandardSimplex σ.1 => (x.1 : Fin (n + 2) → ℝ) i) :=
    (continuous_apply i).comp continuous_induced_dom
  have hsum : Continuous (fun x : StandardSimplex σ.1 =>
      ∑ i, x.1 i • sphereAffineBasis n i) := by
    fun_prop
  exact hsum.congr fun x => by
    rw [Function.comp_apply, boundaryToPolytope_eq_sum]
    simp only [faceInclusion_val]

private theorem boundaryToPolytope_mem_frontier (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) :
    boundaryToPolytope n x ∈ frontier (simplexPolytope n) := by
  rw [mem_frontier_simplexPolytope_iff]
  refine ⟨fun i => boundaryToPolytope_coord n x i ▸ Realization.nonneg _ x i, ?_⟩
  have hsupp := support_mem (standardSuccSimplexBoundary n) x
  rw [mem_standardSuccSimplexBoundary_iff] at hsupp
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 2), i ∉ x.1.support := by
    by_contra h
    have huniv : x.1.support = Finset.univ :=
      Finset.Subset.antisymm (Finset.subset_univ _) fun i _ => by
        by_contra hi
        exact h ⟨i, hi⟩
    exact hsupp.2.ne huniv
  exact ⟨i, by rw [boundaryToPolytope_coord]; exact Finsupp.notMem_support_iff.mp hi⟩

private noncomputable def boundaryWeights (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) : Fin (n + 2) →₀ ℝ :=
  Finsupp.equivFunOnFinite.symm fun i => (sphereAffineBasis n).coord i y.1

@[simp]
private theorem boundaryWeights_apply (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) (i : Fin (n + 2)) :
    boundaryWeights n y i = (sphereAffineBasis n).coord i y.1 :=
  Finsupp.equivFunOnFinite_symm_apply_apply _ _

private theorem boundaryWeights_nonneg (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) (i : Fin (n + 2)) :
    0 ≤ boundaryWeights n y i := by
  rw [boundaryWeights_apply]
  exact (mem_frontier_simplexPolytope_iff n y.1).mp y.2 |>.1 i

private theorem boundaryWeights_sum_eq_one (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    (boundaryWeights n y).sum (fun _ r => r) = 1 := by
  rw [Finsupp.sum_fintype (boundaryWeights n y) (fun _ r => r) (fun _ => rfl)]
  simp only [boundaryWeights_apply]
  exact (sphereAffineBasis n).sum_coord_apply_eq_one y.1

private theorem boundaryWeights_support_mem (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    (boundaryWeights n y).support ∈ standardSuccSimplexBoundary n := by
  rw [mem_standardSuccSimplexBoundary_iff]
  constructor
  · rw [Finsupp.support_nonempty_iff]
    intro hzero
    have hsum := boundaryWeights_sum_eq_one n y
    rw [hzero] at hsum
    simp at hsum
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    obtain ⟨i, hi⟩ := (mem_frontier_simplexPolytope_iff n y.1).mp y.2 |>.2
    intro heq
    have himem : i ∈ (boundaryWeights n y).support := heq.symm ▸ Finset.mem_univ i
    exact (Finsupp.mem_support_iff.mp himem) (by simpa using hi)

private noncomputable def boundaryWeightsPoint (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    StandardSimplex (boundaryWeights n y).support :=
  ⟨boundaryWeights n y, by
    rw [Finset.coe_image, mem_standardSimplex_iff]
    exact ⟨boundaryWeights_nonneg n y, boundaryWeights_sum_eq_one n y, Finset.Subset.rfl⟩⟩

@[simp]
private theorem boundaryWeightsPoint_val (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    (boundaryWeightsPoint n y : Fin (n + 2) →₀ ℝ) = boundaryWeights n y :=
  rfl

private noncomputable def polytopeToBoundary (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    Realization (standardSuccSimplexBoundary n) :=
  faceInclusion (standardSuccSimplexBoundary n)
    ⟨(boundaryWeights n y).support, boundaryWeights_support_mem n y⟩
    (boundaryWeightsPoint n y)

private theorem boundaryToPolytope_polytopeToBoundary (n : ℕ)
    (y : {y // y ∈ frontier (simplexPolytope n)}) :
    boundaryToPolytope n (polytopeToBoundary n y) = y.1 := by
  rw [boundaryToPolytope_eq_sum]
  simp only [polytopeToBoundary, faceInclusion_val]
  exact (sphereAffineBasis n).linear_combination_coord_eq_self y.1

private theorem polytopeToBoundary_boundaryToPolytope (n : ℕ)
    (x : Realization (standardSuccSimplexBoundary n)) :
    polytopeToBoundary n ⟨boundaryToPolytope n x, boundaryToPolytope_mem_frontier n x⟩ = x := by
  apply Subtype.ext
  rw [polytopeToBoundary, faceInclusion_val, boundaryWeightsPoint_val]
  apply Finsupp.ext
  intro i
  rw [boundaryWeights_apply, boundaryToPolytope_coord]

private noncomputable def boundaryEquivPolytopeFrontier (n : ℕ) :
    Realization (standardSuccSimplexBoundary n) ≃
      {y // y ∈ frontier (simplexPolytope n)} where
  toFun x := ⟨boundaryToPolytope n x, boundaryToPolytope_mem_frontier n x⟩
  invFun := polytopeToBoundary n
  left_inv := polytopeToBoundary_boundaryToPolytope n
  right_inv y := Subtype.ext (boundaryToPolytope_polytopeToBoundary n y)

private def zeroCoordSet (n : ℕ) (i : Fin (n + 2)) :
    Set {y // y ∈ frontier (simplexPolytope n)} :=
  {y | (sphereAffineBasis n).coord i y.1 = 0}

private theorem isClosed_zeroCoordSet (n : ℕ) (i : Fin (n + 2)) :
    IsClosed (zeroCoordSet n i) := by
  apply isClosed_eq
  · exact (continuous_barycentric_coord (sphereAffineBasis n) i).comp continuous_subtype_val
  · exact continuous_const

private theorem iUnion_zeroCoordSet (n : ℕ) :
    ⋃ i, zeroCoordSet n i = univ := by
  ext y
  simp only [mem_iUnion, mem_univ, iff_true, zeroCoordSet, mem_ofPred_eq]
  exact (mem_frontier_simplexPolytope_iff n y.1).mp y.2 |>.2

private def boundaryFacet (n : ℕ) (i : Fin (n + 2)) :
    Face (standardSuccSimplexBoundary n) :=
  ⟨Finset.univ.erase i, by
    rw [mem_standardSuccSimplexBoundary_iff]
    refine ⟨?_, Finset.erase_ssubset (Finset.mem_univ i)⟩
    exact (Finset.erase_nonempty (Finset.mem_univ i)).2 Finset.univ_nontrivial⟩

private noncomputable def fixedBoundaryWeightsPoint (n : ℕ) (i : Fin (n + 2))
    (y : zeroCoordSet n i) : StandardSimplex (boundaryFacet n i).1 :=
  ⟨boundaryWeights n y.1, by
    rw [Finset.coe_image, mem_standardSimplex_iff]
    refine ⟨boundaryWeights_nonneg n y.1, boundaryWeights_sum_eq_one n y.1, ?_⟩
    intro j hj
    simp only [boundaryFacet, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ j⟩
    intro hji
    subst j
    have hyzero : (sphereAffineBasis n).coord i y.1.1 = 0 := y.2
    exact (Finsupp.mem_support_iff.mp hj) (by
      simpa only [boundaryWeights_apply] using hyzero)⟩

@[simp]
private theorem fixedBoundaryWeightsPoint_val (n : ℕ) (i : Fin (n + 2))
    (y : zeroCoordSet n i) :
    (fixedBoundaryWeightsPoint n i y : Fin (n + 2) →₀ ℝ) = boundaryWeights n y.1 :=
  rfl

private noncomputable def fixedPolytopeToBoundary (n : ℕ) (i : Fin (n + 2))
    (y : zeroCoordSet n i) : Realization (standardSuccSimplexBoundary n) :=
  faceInclusion (standardSuccSimplexBoundary n) (boundaryFacet n i)
    (fixedBoundaryWeightsPoint n i y)

private theorem continuous_fixedPolytopeToBoundary (n : ℕ) (i : Fin (n + 2)) :
    Continuous (fixedPolytopeToBoundary n i) := by
  apply (continuous_faceInclusion (standardSuccSimplexBoundary n) (boundaryFacet n i)).comp
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  exact (continuous_barycentric_coord (sphereAffineBasis n) j).comp
    (continuous_subtype_val.comp continuous_subtype_val)

private theorem polytopeToBoundary_eq_fixed (n : ℕ) (i : Fin (n + 2))
    (y : zeroCoordSet n i) :
    polytopeToBoundary n y.1 = fixedPolytopeToBoundary n i y := by
  apply Subtype.ext
  rw [polytopeToBoundary, fixedPolytopeToBoundary, faceInclusion_val, faceInclusion_val]
  rw [boundaryWeightsPoint_val, fixedBoundaryWeightsPoint_val]

private theorem continuous_polytopeToBoundary (n : ℕ) :
    Continuous (polytopeToBoundary n) :=
  (locallyFinite_of_finite (zeroCoordSet n)).continuous (iUnion_zeroCoordSet n)
    (isClosed_zeroCoordSet n) fun i => by
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : (zeroCoordSet n i).domRestrict (polytopeToBoundary n) =
          fixedPolytopeToBoundary n i := by
        funext y
        exact polytopeToBoundary_eq_fixed n i y
      rw [heq]
      exact continuous_fixedPolytopeToBoundary n i

private noncomputable def realizationBoundaryHomeomorphPolytopeFrontier (n : ℕ) :
    Realization (standardSuccSimplexBoundary n) ≃ₜ
      {y // y ∈ frontier (simplexPolytope n)} where
  toEquiv := boundaryEquivPolytopeFrontier n
  continuous_toFun := (continuous_boundaryToPolytope n).subtype_mk _
  continuous_invFun := continuous_polytopeToBoundary n

private theorem simplexPolytope_interior_nonempty (n : ℕ) :
    (interior (simplexPolytope n)).Nonempty := by
  rw [simplexPolytope]
  exact ⟨_, (sphereAffineBasis n).centroid_mem_interior_convexHull⟩

private theorem simplexPolytope_bounded (n : ℕ) : IsBounded (simplexPolytope n) := by
  rw [simplexPolytope, isBounded_convexHull]
  exact (finite_range (sphereAffineBasis n)).isBounded

private theorem exists_simplexPolytope_homeomorph_sphere (n : ℕ) :
    ∃ h : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)),
      h '' frontier (simplexPolytope n) = sphere 0 1 := by
  obtain ⟨h, -, -, hfrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (range (sphereAffineBasis n)))
      (simplexPolytope_interior_nonempty n) (simplexPolytope_bounded n)
  exact ⟨h, hfrontier⟩

private noncomputable def polytopeFrontierHomeomorphSphere (n : ℕ) :
    {y // y ∈ frontier (simplexPolytope n)} ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  let h := Classical.choose (exists_simplexPolytope_homeomorph_sphere n)
  (Homeomorph.image h (frontier (simplexPolytope n))).trans
    (Homeomorph.setCongr (Classical.choose_spec (exists_simplexPolytope_homeomorph_sphere n)))

/-- The realization of the boundary of the standard `(n + 1)`-simplex is homeomorphic to the
unit `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))`. -/
noncomputable def realizationStandardSuccSimplexBoundaryHomeomorphSphere (n : ℕ) :
    Realization (standardSuccSimplexBoundary n) ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (realizationBoundaryHomeomorphPolytopeFrontier n).trans
    (polytopeFrontierHomeomorphSphere n)

end AbstractSimplicialComplex
