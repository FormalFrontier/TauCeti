/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The inclusion of a subgroup and the projection onto a quotient, as continuous homomorphisms

Mathlib's `Subgroup.subtype` and `QuotientGroup.mk'` are bare `MonoidHom`s, and its coercion
`ContinuousMonoidHom.toContinuousMonoidHom` applies only to bundled types that already carry a
`ContinuousMapClass` instance, so neither map is available as a `ContinuousMonoidHom`. This file
packages the two, for a topological group and the subspace and quotient topologies.
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

@[simp]
theorem subgroupSubtype_apply (S : Subgroup G) (s : S) : subgroupSubtype S s = (s : G) :=
  (rfl)

/-- The inverse conjugation homomorphism of a normal subgroup, with the subspace topology. -/
def inverseConjugationHom [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (g : G) : N →ₜ* N where
  toMonoidHom := (MulAut.conjNormal g⁻¹ : MulAut N).toMonoidHom
  continuous_toFun := by
    have hf : Continuous (fun n : N =>
        (⟨g⁻¹ * (n : G) * g, by
          simpa only [inv_inv] using
            (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩ : N)) := by
      -- Conjugation by a fixed element is already a Mathlib continuity theorem.
      exact (((IsTopologicalGroup.continuous_conj (G := G) g⁻¹).comp
        continuous_subtype_val).subtype_mk (fun n => by
          simpa only [Function.comp_apply, inv_inv] using
            (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹)).congr fun n => by
          apply Subtype.ext
          simp
    exact hf.congr fun n => by
      -- The bundled automorphism and the displayed inverse-conjugation formula are definitionally
      -- the same map after taking underlying values.
      apply Subtype.ext
      simp

@[simp]
theorem inverseConjugationHom_apply [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (g : G)
    (n : N) :
    inverseConjugationHom N g n =
      ⟨g⁻¹ * (n : G) * g, by
        simpa only [inv_inv] using
          (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩ := by
  -- `MulAut.conjNormal` is bundled, while the right-hand side exposes its subtype value.
  apply Subtype.ext
  change ((MulAut.conjNormal g⁻¹ : MulAut N) n : G) = _
  simp

@[simp]
theorem inverseConjugationHom_one [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    inverseConjugationHom N 1 = ContinuousMonoidHom.id N := by
  ext n
  simp [inverseConjugationHom_apply]

@[simp]
theorem inverseConjugationHom_mul [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (g h : G) :
    inverseConjugationHom N (g * h) =
      (inverseConjugationHom N h).comp (inverseConjugationHom N g) := by
  ext n
  simp [inverseConjugationHom_apply, mul_assoc]

/-- The projection onto the quotient by a normal subgroup, carrying the quotient topology, as a
continuous homomorphism. -/
@[expose] def quotientMk (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  __ := QuotientGroup.mk' N
  continuous_toFun := continuous_quot_mk

@[simp]
theorem coe_quotientMk (N : Subgroup G) [N.Normal] :
    (quotientMk N : G →* G ⧸ N) = QuotientGroup.mk' N :=
  (rfl)

@[simp]
theorem quotientMk_apply (N : Subgroup G) [N.Normal] (g : G) : quotientMk N g = (g : G ⧸ N) :=
  (rfl)

end ContinuousMonoidHom

end TauCeti
