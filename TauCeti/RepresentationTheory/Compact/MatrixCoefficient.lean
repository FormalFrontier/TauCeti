/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.RepresentationTheory.Continuous.Unitary
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Matrix coefficients of continuous representations

This file defines the matrix coefficient
`g ↦ ⟪π g v, w⟫` of a representation whose operator-valued action is continuous. It records
sesquilinearity, translation formulas, the unitary inversion identity, the uniform norm bound, and
the image of a matrix coefficient in `L²` of normalized Haar measure.

Mathlib's `ContRepresentation` bundles continuous linear action operators but does not require the
map from the acting topological group to those operators to be continuous. The continuity hypothesis
is therefore explicit in `matrixCoeff` and its API.

This is the matrix-coefficient milestone in Layer 3 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

section Coefficients

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The matrix coefficient `g ↦ ⟪π g v, w⟫` of a representation with continuous
operator-valued action. -/
noncomputable def matrixCoeff (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : C(G, 𝕜) where
  toFun g := ⟪π g v, w⟫_𝕜
  continuous_toFun := by fun_prop

/-- Evaluation of a matrix coefficient. -/
@[simp]
theorem matrixCoeff_apply (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) (g : G) :
    matrixCoeff π hπ v w g = ⟪π g v, w⟫_𝕜 :=
  (rfl)

/-- A matrix coefficient at the identity is the inner product of its defining vectors. -/
theorem matrixCoeff_apply_one (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) :
    matrixCoeff π hπ v w 1 = ⟪v, w⟫_𝕜 := by
  simp

/-- A matrix coefficient is additive in its first vector. -/
@[simp]
theorem matrixCoeff_add_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v₁ v₂ w : V) :
    matrixCoeff π hπ (v₁ + v₂) w =
      matrixCoeff π hπ v₁ w + matrixCoeff π hπ v₂ w := by
  ext g
  simp only [ContinuousMap.coe_add, Pi.add_apply, matrixCoeff_apply, map_add, inner_add_left]

/-- A matrix coefficient is conjugate-linear in its first vector. -/
@[simp]
theorem matrixCoeff_smul_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (c : 𝕜) (v w : V) :
    matrixCoeff π hπ (c • v) w = star c • matrixCoeff π hπ v w := by
  ext g
  rw [ContinuousMap.smul_apply, matrixCoeff_apply, matrixCoeff_apply, map_smul, inner_smul_left]
  rfl

/-- A matrix coefficient is additive in its second vector. -/
@[simp]
theorem matrixCoeff_add_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w₁ w₂ : V) :
    matrixCoeff π hπ v (w₁ + w₂) =
      matrixCoeff π hπ v w₁ + matrixCoeff π hπ v w₂ := by
  ext g
  simp only [ContinuousMap.coe_add, Pi.add_apply, matrixCoeff_apply, inner_add_right]

/-- A matrix coefficient is linear in its second vector. -/
@[simp]
theorem matrixCoeff_smul_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (c : 𝕜) (v w : V) :
    matrixCoeff π hπ v (c • w) = c • matrixCoeff π hπ v w := by
  ext g
  rw [ContinuousMap.smul_apply, matrixCoeff_apply, matrixCoeff_apply, inner_smul_right]
  rfl

/-- A matrix coefficient vanishes when its first vector is zero. -/
@[simp]
theorem matrixCoeff_zero_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (w : V) :
    matrixCoeff π hπ 0 w = 0 := by
  ext g
  simp

/-- A matrix coefficient vanishes when its second vector is zero. -/
@[simp]
theorem matrixCoeff_zero_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v : V) :
    matrixCoeff π hπ v 0 = 0 := by
  ext g
  simp

end Coefficients

section Group

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- Right translation of a matrix coefficient acts on its first defining vector. -/
theorem matrixCoeff_comp_mulRight (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) (g : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulRight g) =
      matrixCoeff π hπ (π g v) w := by
  ext x
  simp only [ContinuousMap.coe_comp, Function.comp_apply, ContinuousMap.coe_mulRight,
    matrixCoeff_apply, map_mul, mul_apply_eq_comp]

/-- For a unitary representation, left translation of a matrix coefficient acts by the inverse
on its second defining vector. -/
theorem matrixCoeff_comp_mulLeft (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) (g : G) :
    (matrixCoeff π hπ v w).comp (ContinuousMap.mulLeft g) =
      matrixCoeff π hπ v (π g⁻¹ w) := by
  ext x
  simp only [ContinuousMap.coe_comp, Function.comp_apply, ContinuousMap.coe_mulLeft,
    matrixCoeff_apply, map_mul, mul_apply_eq_comp]
  exact hunitary.inner_map_left g (π x v) w

omit [IsTopologicalGroup G] in
/-- For a unitary representation, inversion and conjugation exchange the two defining vectors of
a matrix coefficient. -/
theorem star_matrixCoeff_apply_inv (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) (g : G) :
    star (matrixCoeff π hπ v w g⁻¹) = matrixCoeff π hπ w v g := by
  rw [matrixCoeff_apply, matrixCoeff_apply]
  calc
    star ⟪π g⁻¹ v, w⟫_𝕜 = ⟪w, π g⁻¹ v⟫_𝕜 := by
      simpa only [starRingEnd_apply] using inner_conj_symm w (π g⁻¹ v)
    _ = ⟪π g w, v⟫_𝕜 := by
      simpa only [inv_inv] using hunitary.inner_map_right g⁻¹ w v

end Group

section CompactDomain

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G] [CompactSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The uniform norm of a matrix coefficient of a unitary representation is at most the product
of the norms of its defining vectors. -/
theorem norm_matrixCoeff_le (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (v w : V) :
    ‖matrixCoeff π hπ v w‖ ≤ ‖v‖ * ‖w‖ := by
  rw [ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact fun g ↦ hunitary.norm_inner_map_le g v w

end CompactDomain

section CompactGroup

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The image of a matrix coefficient in `L²` of normalized Haar probability measure. -/
noncomputable def matrixCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) : Lp 𝕜 2 (haarProb G) :=
  ContinuousMap.toLp 2 (haarProb G) 𝕜 (matrixCoeff π hπ v w)

/-- A matrix coefficient in `L²` is represented almost everywhere by its continuous
matrix-coefficient function. -/
theorem coeFn_matrixCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) :
    matrixCoeffLp π hπ v w =ᵐ[haarProb G] matrixCoeff π hπ v w :=
  ContinuousMap.coeFn_toLp (p := 2) (μ := haarProb G) (𝕜 := 𝕜) (matrixCoeff π hπ v w)

/-- The `L²` matrix coefficient vanishes when its first vector is zero. -/
@[simp]
theorem matrixCoeffLp_zero_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (w : V) :
    matrixCoeffLp π hπ 0 w = 0 := by
  simp [matrixCoeffLp]

/-- The `L²` matrix coefficient vanishes when its second vector is zero. -/
@[simp]
theorem matrixCoeffLp_zero_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v : V) :
    matrixCoeffLp π hπ v 0 = 0 := by
  simp [matrixCoeffLp]

/-- The `L²` matrix coefficient is additive in its first vector. -/
@[simp]
theorem matrixCoeffLp_add_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v₁ v₂ w : V) :
    matrixCoeffLp π hπ (v₁ + v₂) w =
      matrixCoeffLp π hπ v₁ w + matrixCoeffLp π hπ v₂ w := by
  simp [matrixCoeffLp]

/-- The `L²` matrix coefficient is conjugate-linear in its first vector. -/
@[simp]
theorem matrixCoeffLp_smul_left (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (c : 𝕜) (v w : V) :
    matrixCoeffLp π hπ (c • v) w = star c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp]

/-- The `L²` matrix coefficient is additive in its second vector. -/
@[simp]
theorem matrixCoeffLp_add_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w₁ w₂ : V) :
    matrixCoeffLp π hπ v (w₁ + w₂) =
      matrixCoeffLp π hπ v w₁ + matrixCoeffLp π hπ v w₂ := by
  simp [matrixCoeffLp]

/-- The `L²` matrix coefficient is linear in its second vector. -/
@[simp]
theorem matrixCoeffLp_smul_right (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (c : 𝕜) (v w : V) :
    matrixCoeffLp π hπ v (c • w) = c • matrixCoeffLp π hπ v w := by
  simp [matrixCoeffLp]

end CompactGroup

end ContRepresentation

end TauCeti
