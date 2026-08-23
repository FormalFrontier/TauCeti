/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Basic

/-!
# The realization map of a barycentric subdivision

Every vertex of the barycentric subdivision of a simplicial complex `K` is a nonempty face of
`K`. Send that vertex to the barycenter of its face and extend affinely over every simplex. Since
the faces indexing a subdivision simplex form a chain, all their barycenters lie in the largest
face in that chain. The affine extension therefore lands in the realization of `K`.

This file constructs that canonical continuous map. It is the forward map in the homeomorphism
between the realizations of a complex and its barycentric subdivision required by Layer 11 of the
GeometricTopology roadmap. Proving that it is a homeomorphism requires the inverse obtained by
sorting the barycentric coordinates of a point, and is left to the next step.

The construction follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2,
"Derived Subdivisions".

## Main definitions

* `AbstractSimplicialComplex.barycentricSubdivisionRealizationMap`: the canonical continuous map
  from the realization of the barycentric subdivision to the original realization.

## Main results

* `AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_vertex`: a subdivision vertex
  maps to the barycenter of the face it represents.
-/

public section

noncomputable section

open Finset Set TauCeti TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- A finite nonempty chain in a partial order has a greatest element. -/
private theorem exists_greatest_of_isChain {α : Type*} [PartialOrder α] (s : Finset α)
    (hs : s.Nonempty) (hchain : IsChain (· ≤ ·) (s : Set α)) :
    ∃ a ∈ s, ∀ b ∈ s, b ≤ a := by
  classical
  obtain ⟨a, hmax⟩ := s.exists_maximal hs
  refine ⟨a, hmax.prop, fun b hb => ?_⟩
  rcases hchain.total hb hmax.prop with hba | hab
  · exact hba
  · exact hmax.le_of_ge hb hab

/-- The linear extension which sends every subdivision vertex to its face barycenter. The
restriction of this map to the subdivision realization lands in the original realization. -/
noncomputable def barycentricSubdivisionLinearMap (K : AbstractSimplicialComplex ι) :
    (Face K →₀ ℝ) →ₗ[ℝ] (ι →₀ ℝ) :=
  Finsupp.linearCombination ℝ (faceBarycenter K)

@[simp]
theorem barycentricSubdivisionLinearMap_single (K : AbstractSimplicialComplex ι)
    (σ : Face K) :
    barycentricSubdivisionLinearMap K (Finsupp.single σ 1) = faceBarycenter K σ := by
  simp [barycentricSubdivisionLinearMap]

private theorem barycentricSubdivisionLinearMap_mem_closedSimplex
    (K : AbstractSimplicialComplex ι) {ρ : Finset (Face K)} (σ : Face K)
    (x : StandardSimplex ρ) (hρσ : ∀ τ ∈ ρ, τ ≤ σ) :
    barycentricSubdivisionLinearMap K x.1 ∈
      convexHull ℝ (σ.1.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  rw [barycentricSubdivisionLinearMap, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (convex_convexHull ℝ _).sum_mem
  · intro τ hτ
    exact StandardSimplex.nonneg x τ
  · exact StandardSimplex.sum_eq_one x
  · intro τ hτ
    apply convexHull_mono
    · intro y hy
      rw [Finset.mem_coe] at hy ⊢
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr
        ⟨v, hρσ τ (StandardSimplex.support_subset x hτ) hv, rfl⟩
    exact faceBarycenter_mem K τ

private theorem barycentricSubdivisionLinearMap_mem (K : AbstractSimplicialComplex ι)
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    barycentricSubdivisionLinearMap K x.1 ∈ (standardGeometricComplex K).space := by
  let ρ := carrier
    (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) x
  have hρ : ρ.1 ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex := ρ.2
  have hρ' := TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp hρ
  obtain ⟨σ, hσρ, hσmax⟩ := exists_greatest_of_isChain ρ.1 hρ'.1 hρ'.2
  rw [mem_realization_iff]
  refine ⟨σ.1, σ.2, ?_⟩
  let x' : StandardSimplex ρ.1 := ⟨x.1, mem_convexHull_carrier _ x⟩
  exact barycentricSubdivisionLinearMap_mem_closedSimplex K σ x' hσmax

/-- The canonical map from the realization of the barycentric subdivision of `K` to the
realization of `K`. It sends each face-vertex to that face's barycenter and is affine on each
subdivision simplex. -/
noncomputable def barycentricSubdivisionRealizationMap (K : AbstractSimplicialComplex ι) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) → Realization K :=
  fun x => ⟨barycentricSubdivisionLinearMap K x.1,
    barycentricSubdivisionLinearMap_mem K x⟩

/-- The realization map has the expected underlying affine formula. -/
@[simp]
theorem barycentricSubdivisionRealizationMap_val (K : AbstractSimplicialComplex ι)
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    (barycentricSubdivisionRealizationMap K x : ι →₀ ℝ) =
      barycentricSubdivisionLinearMap K x.1 :=
  (rfl)

/-- A vertex of the barycentric subdivision maps to the barycenter of the original face it
represents. -/
theorem barycentricSubdivisionRealizationMap_vertex (K : AbstractSimplicialComplex ι)
    (σ : Face K) :
    (barycentricSubdivisionRealizationMap K
      (vertex (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex) σ) : ι →₀ ℝ) = faceBarycenter K σ := by
  rw [barycentricSubdivisionRealizationMap_val, vertex_val,
    barycentricSubdivisionLinearMap_single]

/-- The barycentric-subdivision realization map is continuous for the weak topologies on both
realizations. -/
theorem continuous_barycentricSubdivisionRealizationMap (K : AbstractSimplicialComplex ι) :
    Continuous (barycentricSubdivisionRealizationMap K) := by
  apply continuous_iff_faceInclusion.2
  intro ρ
  have hρ := TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp ρ.2
  obtain ⟨σ, hσρ, hσmax⟩ := exists_greatest_of_isChain ρ.1 hρ.1 hρ.2
  let toFace : StandardSimplex ρ.1 → StandardSimplex σ.1 := fun x =>
    ⟨barycentricSubdivisionLinearMap K x.1,
      barycentricSubdivisionLinearMap_mem_closedSimplex K σ x hσmax⟩
  -- The induced topology exposes the underlying `Finsupp`; record its value explicitly rather
  -- than relying on unfolding `toFace` through both subtype coercions below.
  have htoFace_val (x : StandardSimplex ρ.1) :
      (toFace x : ι →₀ ℝ) = barycentricSubdivisionLinearMap K x.1 := rfl
  have hlinear : Continuous (fun x : StandardSimplex ρ.1 =>
      (barycentricSubdivisionLinearMap K x.1 : ι → ℝ)) := by
    apply continuous_pi
    intro v
    have hformula :
        (fun x : StandardSimplex ρ.1 => (barycentricSubdivisionLinearMap K x.1) v) =
      fun x => ∑ τ ∈ ρ.1, x.1 τ * faceBarycenter K τ v := by
      funext x
      have hsupp : x.1 ∈ Finsupp.supported ℝ ℝ (↑ρ.1 : Set (Face K)) :=
        (Finsupp.mem_supported ℝ x.1).mpr (StandardSimplex.support_subset x)
      rw [barycentricSubdivisionLinearMap,
        Finsupp.linearCombination_apply_of_mem_supported ℝ hsupp]
      simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
      rfl
    rw [hformula]
    apply continuous_finsetSum
    intro τ _
    have hcoe : Continuous (fun x : StandardSimplex ρ.1 => (x.1 : Face K → ℝ)) :=
      continuous_induced_dom
    exact ((continuous_apply τ).comp hcoe).mul continuous_const
  have htoFace : Continuous toFace := by
    apply continuous_induced_rng.mpr
    convert hlinear using 1
    funext x v
    exact DFunLike.congr_fun (htoFace_val x) v
  have hfactor :
      barycentricSubdivisionRealizationMap K ∘ faceInclusion _ ρ =
        faceInclusion K ⟨σ.1, σ.2⟩ ∘ toFace := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, barycentricSubdivisionRealizationMap_val, faceInclusion_val,
      toFace]
  rw [hfactor]
  exact (continuous_faceInclusion K ⟨σ.1, σ.2⟩).comp htoFace

end AbstractSimplicialComplex
