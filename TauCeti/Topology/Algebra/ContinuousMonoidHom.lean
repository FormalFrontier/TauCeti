/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The inclusion of a subgroup and the projection to a quotient, as continuous homomorphisms

Mathlib has `Subgroup.subtype` and `QuotientGroup.mk'` as bare `MonoidHom`s, and both are
continuous for the subspace and quotient topologies. This file bundles them as
`ContinuousMonoidHom`s, in the same way that `Submodule.subtypeL` bundles `Submodule.subtype` as a
continuous linear map.

The bundled forms are what an API indexed by continuous homomorphisms — such as the
compatible-pair functoriality of continuous group cohomology — takes as its group argument.
-/

@[expose] public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The inclusion of a subgroup of a topological group, as a continuous homomorphism. This is the
continuous-homomorphism form of `Subgroup.subtype`. -/
def _root_.Subgroup.subtypeₜ (S : Subgroup G) : S →ₜ* G where
  __ := S.subtype
  continuous_toFun := continuous_subtype_val

@[simp]
lemma _root_.Subgroup.coe_subtypeₜ (S : Subgroup G) : ⇑S.subtypeₜ = Subtype.val := rfl

@[simp]
lemma _root_.Subgroup.subtypeₜ_toMonoidHom (S : Subgroup G) :
    (S.subtypeₜ : S →* G) = S.subtype := rfl

/-- The projection onto the quotient by a normal subgroup, as a continuous homomorphism. This is
the continuous-homomorphism form of `QuotientGroup.mk'`. -/
def _root_.QuotientGroup.mk'ₜ (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  __ := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

@[simp]
lemma _root_.QuotientGroup.coe_mk'ₜ (N : Subgroup G) [N.Normal] :
    ⇑(QuotientGroup.mk'ₜ N) = QuotientGroup.mk := rfl

@[simp]
lemma _root_.QuotientGroup.mk'ₜ_toMonoidHom (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk'ₜ N : G →* G ⧸ N) = QuotientGroup.mk' N := rfl

end TauCeti
