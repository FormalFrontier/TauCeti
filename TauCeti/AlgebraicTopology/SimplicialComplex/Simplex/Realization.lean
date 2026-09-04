/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Normed.Module.RCLike.Real

public import Mathlib.Analysis.Convex.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Realizations of the standard one-simplex and its boundary

This file identifies the geometric realization of the full abstract complex on a finite vertex
type with Mathlib's standard simplex of barycentric coordinate functions. Specializing to two
vertices gives a homeomorphism from the standard one-simplex to the unit interval. Its boundary,
the bottom abstract complex on `Fin 2`, is then identified with the unit zero-sphere.

These are the first realization round-trips in layer 11 of the geometric-topology roadmap. The
roadmap asks that the realization of the boundary of the standard `n`-simplex be homeomorphic to
`Sⁿ⁻¹`; `realizationOneSimplexBoundaryHomeomorphSphereZero` establishes the base case `n = 1`.
The interval identification also supplies the standard topological model for the simplicial
interval used in the later product-and-collapse formulation of Zeeman's conjecture.

The barycentric simplex uses Mathlib's `Convexity.StdSimplex`, and its homeomorphism with the
unit interval is Mathlib's `Convexity.StdSimplex.homeomorphI`. The zero-sphere identification is
the elementary equivalence between its two points and `Fin 2`.

## Main results

* `realizationTopHomeomorphStdSimplex`: the full complex realizes to Mathlib's standard simplex.
* `realizationOneSimplexHomeomorphUnitInterval`: the standard one-simplex realizes to `[0, 1]`.
* `realizationOneSimplexBoundaryHomeomorphSphereZero`: its boundary realizes to `S⁰`.
-/

public section

noncomputable section

open Metric Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [Nonempty ι]

attribute [local instance] Classical.decEq

private theorem univ_mem_top : (Finset.univ : Finset ι) ∈ (⊤ : AbstractSimplicialComplex ι) :=
  Finset.univ_nonempty

private def topFace : Face (⊤ : AbstractSimplicialComplex ι) :=
  ⟨Finset.univ, univ_mem_top⟩

/-- The realization of the full abstract complex on a finite vertex type is homeomorphic to
Mathlib's standard simplex of nonnegative coordinate functions summing to one. -/
noncomputable def realizationTopHomeomorphStdSimplex :
    Realization (⊤ : AbstractSimplicialComplex ι) ≃ₜ Convexity.StdSimplex ℝ ι where
  toFun x := by
    refine ⟨x.1, fun i => ?_, ?_⟩ <;>
      let y : StandardSimplex (carrier (⊤ : AbstractSimplicialComplex ι) x).1 :=
        ⟨x.1, mem_convexHull_carrier _ x⟩
    · exact StandardSimplex.nonneg y i
    · exact StandardSimplex.sum_eq_one y
  invFun x :=
    faceInclusion (⊤ : AbstractSimplicialComplex ι)
      (topFace (ι := ι))
      ⟨x.weights, by
        rw [Finset.coe_image, mem_standardSimplex_iff]
        exact ⟨x.weights_nonneg, x.total, Finset.subset_univ _⟩⟩
  left_inv x := Subtype.ext (faceInclusion_val _ _ _)
  right_inv x := Convexity.StdSimplex.ext (faceInclusion_val _ _ _)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff]
    apply continuous_pi
    intro i
    apply continuous_iff_faceInclusion.2
    intro σ
    exact ((continuous_apply i).comp
      (continuous_induced_dom :
        Continuous (fun y : StandardSimplex σ.1 => (y.1 : ι → ℝ)))).congr fun y => by
          exact congrArg (fun z : ι →₀ ℝ => z i) (faceInclusion_val _ _ y).symm
  continuous_invFun := by
    apply (continuous_faceInclusion (⊤ : AbstractSimplicialComplex ι)
      (topFace (ι := ι))).comp
    apply continuous_induced_rng.mpr
    exact continuous_pi fun i => Convexity.StdSimplex.continuous_weights_apply ℝ i

/-- The full-complex realization homeomorphism reads the same barycentric coordinates. -/
@[simp]
theorem realizationTopHomeomorphStdSimplex_apply (x : Realization
    (⊤ : AbstractSimplicialComplex ι)) (i : ι) :
    (realizationTopHomeomorphStdSimplex x).weights i = x.1 i := by
  rfl

/-- The inverse full-complex realization homeomorphism has the prescribed barycentric
coordinates. -/
@[simp]
theorem realizationTopHomeomorphStdSimplex_symm_apply_val (x : Convexity.StdSimplex ℝ ι) (i : ι) :
    (realizationTopHomeomorphStdSimplex.symm x : ι →₀ ℝ) i = x.weights i := by
  rw [realizationTopHomeomorphStdSimplex]
  exact congrArg (fun z : ι →₀ ℝ => z i)
    (faceInclusion_val (⊤ : AbstractSimplicialComplex ι)
      (topFace (ι := ι)) _)

/-- The realization of the standard one-simplex is homeomorphic to the unit interval. The zeroth
vertex maps to `0` and the first vertex maps to `1`; see the two endpoint lemmas below. -/
noncomputable def realizationOneSimplexHomeomorphUnitInterval :
    Realization (⊤ : AbstractSimplicialComplex (Fin 2)) ≃ₜ unitInterval :=
  (realizationTopHomeomorphStdSimplex (ι := Fin 2)).trans Convexity.StdSimplex.homeomorphI

private theorem homeomorphI_symm_apply_coe (x : unitInterval) :
    ((Convexity.StdSimplex.homeomorphI.symm x).weights : Fin 2 → ℝ) =
      ![1 - (x : ℝ), (x : ℝ)] := by
  have h : Convexity.StdSimplex.homeomorphI.symm x =
      Convexity.StdSimplex.duple (s := 1 - (x : ℝ)) (t := (x : ℝ)) 0 1
        (sub_nonneg.mpr x.2.2) x.2.1 (by ring) := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext (by
      simp [Convexity.StdSimplex.homeomorphI_apply_coe,
        Convexity.StdSimplex.weights_duple])
  rw [h, Convexity.StdSimplex.weights_duple]
  funext i
  fin_cases i <;> simp

/-- The one-simplex homeomorphism is its second barycentric coordinate. -/
@[simp]
theorem realizationOneSimplexHomeomorphUnitInterval_coe (x : Realization
    (⊤ : AbstractSimplicialComplex (Fin 2))) :
    (realizationOneSimplexHomeomorphUnitInterval x : ℝ) = x.1 1 := by
  rw [realizationOneSimplexHomeomorphUnitInterval, Homeomorph.trans_apply,
    Convexity.StdSimplex.homeomorphI_apply_coe, realizationTopHomeomorphStdSimplex_apply]

/-- The zeroth barycentric coordinate of the interval inverse is one minus the interval
coordinate. -/
@[simp]
theorem realizationOneSimplexHomeomorphUnitInterval_symm_apply_val_zero (x : unitInterval) :
    (realizationOneSimplexHomeomorphUnitInterval.symm x : Fin 2 →₀ ℝ) 0 =
      1 - (x : ℝ) := by
  rw [realizationOneSimplexHomeomorphUnitInterval, Homeomorph.symm_trans_apply,
    realizationTopHomeomorphStdSimplex_symm_apply_val,
    homeomorphI_symm_apply_coe]
  rfl

/-- The first barycentric coordinate of the interval inverse is the interval coordinate. -/
@[simp]
theorem realizationOneSimplexHomeomorphUnitInterval_symm_apply_val_one (x : unitInterval) :
    (realizationOneSimplexHomeomorphUnitInterval.symm x : Fin 2 →₀ ℝ) 1 = (x : ℝ) := by
  rw [realizationOneSimplexHomeomorphUnitInterval, Homeomorph.symm_trans_apply,
    realizationTopHomeomorphStdSimplex_symm_apply_val,
    homeomorphI_symm_apply_coe]
  rfl

/-- The zeroth vertex of the realized one-simplex is the left endpoint of the interval. -/
@[simp]
theorem realizationOneSimplexHomeomorphUnitInterval_vertex_zero :
    realizationOneSimplexHomeomorphUnitInterval
      (vertex (⊤ : AbstractSimplicialComplex (Fin 2)) 0) = 0 := by
  apply Subtype.ext
  simp

/-- The first vertex of the realized one-simplex is the right endpoint of the interval. -/
@[simp]
theorem realizationOneSimplexHomeomorphUnitInterval_vertex_one :
    realizationOneSimplexHomeomorphUnitInterval
      (vertex (⊤ : AbstractSimplicialComplex (Fin 2)) 1) = 1 := by
  apply Subtype.ext
  simp

private noncomputable def finTwoEquivSphereZero : Fin 2 ≃ sphere (0 : ℝ) 1 := by
  let f : Fin 2 → sphere (0 : ℝ) 1 := fun i =>
    if i = 0 then ⟨1, by simp⟩ else ⟨-1, by simp⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij ⊢ <;> norm_num at hij
  · intro x
    have hx : |(x : ℝ)| = 1 := by
      simpa only [Real.norm_eq_abs] using norm_eq_of_mem_sphere x
    rcases (abs_eq zero_le_one).mp hx with hx | hx
    · exact ⟨0, by apply Subtype.ext; simp [f, hx]⟩
    · exact ⟨1, by apply Subtype.ext; simp [f, hx]⟩

private noncomputable def finTwoHomeomorphSphereZero : Fin 2 ≃ₜ sphere (0 : ℝ) 1 := by
  letI : Finite (sphere (0 : ℝ) 1) :=
    Finite.of_equiv (Fin 2) finTwoEquivSphereZero
  exact Homeomorph.ofDiscrete finTwoEquivSphereZero

@[simp]
private theorem finTwoHomeomorphSphereZero_zero : (finTwoHomeomorphSphereZero 0 : ℝ) = 1 :=
  rfl

@[simp]
private theorem finTwoHomeomorphSphereZero_one : (finTwoHomeomorphSphereZero 1 : ℝ) = -1 :=
  rfl

/-- The realization of the boundary of the standard one-simplex is homeomorphic to the unit
zero-sphere. By `simplexBoundary_univ_fin_two`, the underlying precomplex of the source is exactly
the boundary of the simplex on the two vertices. -/
noncomputable def realizationOneSimplexBoundaryHomeomorphSphereZero :
    Realization (⊥ : AbstractSimplicialComplex (Fin 2)) ≃ₜ sphere (0 : ℝ) 1 :=
  (realizationBotHomeomorph (ι := Fin 2)).trans finTwoHomeomorphSphereZero

/-- The zeroth boundary vertex maps to `1` on the zero-sphere. -/
@[simp]
theorem realizationOneSimplexBoundaryHomeomorphSphereZero_vertex_zero :
    (realizationOneSimplexBoundaryHomeomorphSphereZero
      (vertex (⊥ : AbstractSimplicialComplex (Fin 2)) 0) : ℝ) = 1 := by
  rw [realizationOneSimplexBoundaryHomeomorphSphereZero, Homeomorph.trans_apply,
    realizationBotHomeomorph_apply_vertex, finTwoHomeomorphSphereZero_zero]

/-- The first boundary vertex maps to `-1` on the zero-sphere. -/
@[simp]
theorem realizationOneSimplexBoundaryHomeomorphSphereZero_vertex_one :
    (realizationOneSimplexBoundaryHomeomorphSphereZero
      (vertex (⊥ : AbstractSimplicialComplex (Fin 2)) 1) : ℝ) = -1 := by
  rw [realizationOneSimplexBoundaryHomeomorphSphereZero, Homeomorph.trans_apply,
    realizationBotHomeomorph_apply_vertex, finTwoHomeomorphSphereZero_one]

/-- The inverse zero-sphere homeomorphism sends `1` to the zeroth boundary vertex. -/
@[simp]
theorem realizationOneSimplexBoundaryHomeomorphSphereZero_symm_apply_one :
    realizationOneSimplexBoundaryHomeomorphSphereZero.symm ⟨1, by simp⟩ =
      vertex (⊥ : AbstractSimplicialComplex (Fin 2)) 0 := by
  apply realizationOneSimplexBoundaryHomeomorphSphereZero.injective
  apply Subtype.ext
  simp

/-- The inverse zero-sphere homeomorphism sends `-1` to the first boundary vertex. -/
@[simp]
theorem realizationOneSimplexBoundaryHomeomorphSphereZero_symm_apply_neg_one :
    realizationOneSimplexBoundaryHomeomorphSphereZero.symm ⟨-1, by simp⟩ =
      vertex (⊥ : AbstractSimplicialComplex (Fin 2)) 1 := by
  apply realizationOneSimplexBoundaryHomeomorphSphereZero.injective
  apply Subtype.ext
  simp

end AbstractSimplicialComplex

