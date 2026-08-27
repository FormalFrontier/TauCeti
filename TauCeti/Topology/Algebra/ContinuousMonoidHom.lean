/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Subgroup inclusion, quotient projection and conjugation, as continuous homomorphisms

Mathlib's `Subgroup.subtype`, `QuotientGroup.mk'` and `MulAut.conjNormal` are bare `MonoidHom`s
and `MulEquiv`s, and its coercion `ContinuousMonoidHom.toContinuousMonoidHom` applies only to
bundled types that already carry a `ContinuousMapClass` instance, so none of them is available as
a `ContinuousMonoidHom`. This file packages the three, for a topological group and the subspace
and quotient topologies.
-/

public section

namespace TauCeti

namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]

-- Both definitions below are exposed: downstream, `TopRep.res` objects taken along them have to
-- be definitionally the ones taken along the bare `Subgroup.subtype` and `QuotientGroup.mk'`.
/-- The inclusion of a subgroup, carrying the subspace topology, as a continuous homomorphism. -/
@[expose] def subgroupSubtype (S : Subgroup G) : S →ₜ* G where
  __ := S.subtype
  continuous_toFun := continuous_subtype_val

@[simp]
theorem coe_subgroupSubtype (S : Subgroup G) : (subgroupSubtype S : S →* G) = S.subtype :=
  (rfl)

/-- The projection onto the quotient by a normal subgroup, carrying the quotient topology, as a
continuous homomorphism. -/
@[expose] def quotientMk (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  __ := QuotientGroup.mk' N
  continuous_toFun := continuous_quot_mk

@[simp]
theorem coe_quotientMk (N : Subgroup G) [N.Normal] :
    (quotientMk N : G →* G ⧸ N) = QuotientGroup.mk' N :=
  (rfl)

section Conjugation

variable [ContinuousMul G] (N : Subgroup G) [N.Normal]

/-- Conjugation `n ↦ g * n * g⁻¹` of a normal subgroup by an element of the ambient group, as a
continuous homomorphism. The underlying monoid homomorphism is Mathlib's `MulAut.conjNormal g`;
what is added here is its continuity. -/
def conjNormal (g : G) : N →ₜ* N where
  __ := (MulAut.conjNormal g : N ≃* N).toMonoidHom
  continuous_toFun := continuous_induced_rng.2 <|
    (continuous_const.mul continuous_subtype_val).mul continuous_const

@[simp]
theorem coe_conjNormal_apply (g : G) (n : N) : (conjNormal N g n : G) = g * n * g⁻¹ :=
  MulAut.conjNormal_apply g n

@[simp]
theorem conjNormal_one : conjNormal N (1 : G) = ContinuousMonoidHom.id N := by
  ext n
  simp

/-- Conjugation is an action: conjugating by `g * g'` is conjugating by `g'` and then by `g`. -/
@[simp]
theorem conjNormal_mul (g g' : G) :
    conjNormal N (g * g') = (conjNormal N g).comp (conjNormal N g') := by
  ext n
  simp [mul_assoc]

end Conjugation

end ContinuousMonoidHom

end TauCeti
