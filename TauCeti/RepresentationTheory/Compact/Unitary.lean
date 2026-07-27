/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Unitary continuous representations

This file defines when a continuous representation preserves a complex inner product. It
characterizes unitarity through norm preservation, isometries, and Mathlib's `unitary` submonoid of
continuous linear operators, and records the basic inner-product identities and coefficient bound.

The definition and its API implement the unitarity-predicate milestone in Layer 1 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
The operator characterizations reuse Mathlib's adjoint and unitary-operator theory.

The mathematical development follows Daniel Bump, *Lie Groups*, second edition, Chapters 2–4.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

namespace ContRepresentation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

/-- Applying a continuous group representation at an element and then at its inverse cancels. -/
@[simp]
theorem self_inv_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π g (π g⁻¹ v) = v :=
  Representation.self_inv_apply π.toRepresentation g v

end ContRepresentation

section Monoid

variable {G V : Type*} [Monoid G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A continuous representation is unitary when every action operator preserves the inner
product. -/
def IsUnitary (π : ContRepresentation ℂ G V) : Prop :=
  ∀ g v w, ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ

/-- A representation is unitary exactly when every action map preserves norms. -/
theorem isUnitary_iff_norm_map (π : ContRepresentation ℂ G V) :
    IsUnitary π ↔ ∀ g v, ‖π g v‖ = ‖v‖ := by
  constructor
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mpr (hπ g)
  · intro hπ g
    exact (LinearMap.norm_map_iff_inner_map_map (π g)).mp (hπ g)

/-- A representation is unitary exactly when every action map is an isometry. -/
theorem isUnitary_iff_isometry (π : ContRepresentation ℂ G V) :
    IsUnitary π ↔ ∀ g, Isometry (π g) := by
  rw [isUnitary_iff_norm_map]
  exact forall_congr' fun g ↦ (AddMonoidHomClass.isometry_iff_norm (π g)).symm

namespace IsUnitary

variable {π : ContRepresentation ℂ G V}

/-- A unitary representation preserves the inner product. -/
@[simp]
theorem inner_map_map (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, π g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  hπ g v w

/-- Every action map of a unitary representation preserves norms. -/
@[simp]
theorem norm_map (hπ : IsUnitary π) (g : G) (v : V) :
    ‖π g v‖ = ‖v‖ :=
  (isUnitary_iff_norm_map π).mp hπ g v

/-- Every action map of a unitary representation is an isometry. -/
theorem isometry (hπ : IsUnitary π) (g : G) : Isometry (π g) :=
  (isUnitary_iff_isometry π).mp hπ g

/-- Every action map of a unitary representation is injective. -/
theorem injective (hπ : IsUnitary π) (g : G) : Function.Injective (π g) :=
  (hπ.isometry g).injective

/-- Restriction along a monoid homomorphism preserves unitarity. -/
theorem restrict {H : Type*} [Monoid H] (hπ : IsUnitary π) (φ : H →* G) :
    IsUnitary (π.restrict φ) :=
  fun h ↦ hπ (φ h)

/-- A matrix coefficient of a unitary representation is bounded by the product of the vector
norms. -/
theorem norm_inner_map_le (hπ : IsUnitary π) (g : G) (v w : V) :
    ‖⟪π g v, w⟫_ℂ‖ ≤ ‖v‖ * ‖w‖ := by
  calc
    ‖⟪π g v, w⟫_ℂ‖ ≤ ‖π g v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = ‖v‖ * ‖w‖ := by rw [hπ.norm_map]

end IsUnitary

/-- The trivial continuous representation is unitary. -/
theorem isUnitary_trivial :
    IsUnitary (ContRepresentation.trivial ℂ G V) := by
  intro g v w
  simp

end Monoid

section Group

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {π : ContRepresentation ℂ G V}

/-- For a group representation, inner-product preservation is equivalent to every action operator
belonging to Mathlib's unitary submonoid. -/
theorem isUnitary_iff_mem_unitary (π : ContRepresentation ℂ G V) :
    IsUnitary π ↔ ∀ g, π g ∈ unitary (V →L[ℂ] V) := by
  constructor
  · intro hπ g
    apply ((Group.isUnit g).map π.toMonoidHom).mem_unitary_of_star_mul_self
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)
  · intro hπ g v w
    exact (π g).inner_map_map_of_mem_unitary (hπ g) v w

namespace IsUnitary

/-- Every action operator of a unitary group representation belongs to Mathlib's `unitary`
submonoid. -/
theorem mem_unitary (hπ : IsUnitary π) (g : G) :
    π g ∈ unitary (V →L[ℂ] V) :=
  (isUnitary_iff_mem_unitary π).mp hπ g

/-- The adjoint of a unitary action operator is a left inverse. -/
theorem adjoint_comp_self (hπ : IsUnitary π) (g : G) :
    (ContinuousLinearMap.adjoint (π g)).comp (π g) = 1 :=
  (π g).inner_map_map_iff_adjoint_comp_self.mp (hπ g)

/-- The adjoint of a unitary action operator is a right inverse. -/
theorem self_comp_adjoint (hπ : IsUnitary π) (g : G) :
    (π g).comp (ContinuousLinearMap.adjoint (π g)) = 1 := by
  rw [← ContinuousLinearMap.mul_def]
  simpa only [ContinuousLinearMap.star_eq_adjoint] using
    Unitary.mul_star_self_of_mem (hπ.mem_unitary g)

omit [CompleteSpace V] in
/-- Moving a unitary action from the first inner-product argument to the second replaces the group
element by its inverse. -/
theorem inner_map_left (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g v (π g⁻¹ w)

omit [CompleteSpace V] in
/-- Moving a unitary action from the second inner-product argument to the first replaces the group
element by its inverse. -/
theorem inner_map_right (hπ : IsUnitary π) (g : G) (v w : V) :
    ⟪v, π g w⟫_ℂ = ⟪π g⁻¹ v, w⟫_ℂ := by
  simpa only [ContRepresentation.self_inv_apply] using hπ.inner_map_map g (π g⁻¹ v) w

/-- The adjoint of a unitary action operator is the action of the inverse group element. -/
@[simp]
theorem adjoint_eq_inv (hπ : IsUnitary π) (g : G) :
    ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simpa using hπ.inner_map_left g⁻¹ v w

end IsUnitary

end Group

end TauCeti
