/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Continuous.Unitary
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Matrix coefficients of continuous representations

This file defines the matrix coefficient
`g ↦ ⟪π g v, w⟫` of a representation whose operator-valued action is continuous, and proves the
uniform bound for unitary representations.

Mathlib's `ContRepresentation` bundles continuous linear action operators but does not require
continuity of the map from the acting topological monoid to those operators. The continuity
hypothesis is therefore explicit in `matrixCoeff` and its API.

The uniform bound is part of the Layer 1 unitarity-predicate milestone in the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap). The mathematical
development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

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
@[simp]
theorem matrixCoeff_apply_one (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (v w : V) :
    matrixCoeff π hπ v w 1 = ⟪v, w⟫_𝕜 := by
  simp

end Coefficients

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

end ContRepresentation

end TauCeti
