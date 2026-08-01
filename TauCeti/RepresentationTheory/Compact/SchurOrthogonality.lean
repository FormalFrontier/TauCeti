/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Compact.Intertwiner
public import TauCeti.RepresentationTheory.Continuous.Schur
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Schur orthogonality for one irreducible compact-group representation

This file proves the first Schur orthogonality relation for matrix coefficients of a
finite-dimensional irreducible unitary representation of a compact group. Haar-averaging a
rank-one operator produces a self-intertwiner. Schur's lemma makes that intertwiner scalar, and
preservation of the trace determines the scalar to be the reciprocal of the dimension.

The coordinate-free result is accompanied by its orthonormal-basis form. The latter fixes both the
order of the Kronecker deltas and the placement of complex conjugation in Mathlib's convention that
the inner product is conjugate-linear in its first argument.

## Main statements

* `TauCeti.ContRepresentation.averageOperator_eq_finrank_inv_mul_trace_smul_id`: the average of a
  self-map is its normalized trace times the identity.
* `TauCeti.ContRepresentation.schur_orthogonality_self`: the coordinate-free first Schur
  orthogonality relation.
* `TauCeti.ContRepresentation.schur_orthogonality_basis`: the corresponding Kronecker-delta
  formula in an orthonormal basis.

This completes the first-orthogonality item of Layer 4 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The mathematical argument follows Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace
open scoped MonoidAlgebra

namespace TauCeti

namespace ContRepresentation

section CompactGroup

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V]
  [FiniteDimensional 𝕜 V]

local instance instCompleteSpaceSchurOrthogonality : CompleteSpace V :=
  FiniteDimensional.complete 𝕜 V

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-! ### The scalar selected by Haar averaging -/

/-- On an irreducible finite-dimensional representation, the Haar average of a self-map is its
normalized trace times the identity.

Schur's lemma first gives an unspecified scalar. Since averaging preserves the trace, that scalar
times `finrank 𝕜 V` equals the trace of the original map; irreducibility ensures that the dimension
is nonzero. -/
theorem averageOperator_eq_finrank_inv_mul_trace_smul_id
    (hirr : Representation.IsIrreducible π.toRepresentation) (T : V →L[𝕜] V) :
    averageOperator π hπ π hπ T =
      ((Module.finrank 𝕜 V : 𝕜)⁻¹ * LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V)) •
        ContinuousLinearMap.id 𝕜 V := by
  letI : Representation.IsIrreducible π.toRepresentation := hirr
  haveI : IsSimpleModule 𝕜[G] π.toRepresentation.asModule := inferInstance
  haveI : Nontrivial V := IsSimpleModule.nontrivial 𝕜[G] π.toRepresentation.asModule
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_irreducible π hirr
    (averageIntertwiner π hπ π hπ T)
  have hc := congrArg ContIntertwiningMap.toContinuousLinearMap hc
  simp only [toContinuousLinearMap_averageIntertwiner,
    ContIntertwiningMap.toContinuousLinearMap_smul,
    ContIntertwiningMap.toContinuousLinearMap_one] at hc
  have htrace := trace_averageOperator π hπ T
  rw [hc] at htrace
  have hdim : (Module.finrank 𝕜 V : 𝕜) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := 𝕜) (M := V)).ne'
  have hc' : c = (Module.finrank 𝕜 V : 𝕜)⁻¹ *
      LinearMap.trace 𝕜 V (T : V →ₗ[𝕜] V) := by
    apply (eq_inv_mul_iff_mul_eq₀ hdim).2
    simpa [mul_comm] using htrace
  rw [hc, hc']
  rfl

/-! ### The first Schur orthogonality relation -/

/-- **Schur orthogonality for one irreducible representation, in coordinate-free form.**

For a unitary irreducible representation of dimension `d`, the `L²` inner product of the matrix
coefficients determined by `(v₁, w₁)` and `(v₂, w₂)` is
`d⁻¹ * conj ⟪v₁, v₂⟫ * ⟪w₁, w₂⟫`. The conjugation on the first vector factor is forced by Mathlib's
inner-product convention. -/
theorem schur_orthogonality_self (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation) (v₁ w₁ v₂ w₂ : V) :
    ⟪matrixCoeffLp π hπ v₁ w₁, matrixCoeffLp π hπ v₂ w₂⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ *
        ((starRingEnd 𝕜) ⟪v₁, v₂⟫_𝕜 * ⟪w₁, w₂⟫_𝕜) := by
  rw [inner_matrixCoeffLp_eq_inner_averageOperator π hπ π hπ hunitary,
    averageOperator_eq_finrank_inv_mul_trace_smul_id π hπ hirr,
    smul_apply, ContinuousLinearMap.id_apply, InnerProductSpace.trace_rankOne, inner_smul_right]
  rw [← inner_conj_symm v₂ v₁]
  ring

/-- **Schur orthogonality in an orthonormal basis.** If
`πᵢⱼ(g) = ⟪π(g)eⱼ, eᵢ⟫`, then
`⟪πᵢⱼ, πₖₗ⟫_{L²} = d⁻¹ δⱼₗ δᵢₖ`.

This is the convention check for `schur_orthogonality_self`: Kronecker deltas are real, so the
coordinate-free conjugation becomes invisible here, while the order of all four indices remains
explicit. -/
theorem schur_orthogonality_basis (hunitary : IsUnitary π)
    (hirr : Representation.IsIrreducible π.toRepresentation)
    {d : ℕ} (e : OrthonormalBasis (Fin d) 𝕜 V) (i j k l : Fin d) :
    ⟪matrixCoeffLp π hπ (e j) (e i), matrixCoeffLp π hπ (e l) (e k)⟫_𝕜 =
      (d : 𝕜)⁻¹ *
        ((if j = l then (1 : 𝕜) else 0) * (if i = k then (1 : 𝕜) else 0)) := by
  rw [schur_orthogonality_self π hπ hunitary hirr]
  rw [Module.finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  simp only [orthonormal_iff_ite.mp e.orthonormal]
  split_ifs <;> simp_all

end CompactGroup

end ContRepresentation

end TauCeti
