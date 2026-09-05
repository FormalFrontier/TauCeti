/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Conjugation on explicit first continuous cohomology

If `N` is a normal subgroup of a topological group `G`, conjugation by `g` on `N`, together
with the action of `g` on coefficients, is a compatible pair.  This file packages the resulting
map on the explicit quotient `H¹(N, M)`.  The map is written with the inverse conjugation
`h ↦ g⁻¹ h g`, so that its coefficient component is the left action `m ↦ g • m`.

The construction is functorial in `g`, hence gives the expected `G`-action.  When `g` belongs to
`N`, the induced map is the identity: the difference of a cocycle and its conjugate is the
principal cocycle attached to `c g`.  This is the degree-one part of the conjugation step in
Layer 2 of `TauCetiRoadmap/ProfiniteCohomology/README.md`; the degree-two chain homotopy remains
for the later completion of that step.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

section

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The inverse conjugation homomorphism of a normal subgroup. -/
@[expose] def conjugationHom (N : Subgroup G) [N.Normal] (g : G) : N →ₜ* N where
  toFun n :=
    ⟨g⁻¹ * (n : G) * g, by
      simpa only [inv_inv] using
        (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩
  map_one' := by simp
  map_mul' a b := by simp [mul_assoc]
  continuous_toFun := by
    exact ((continuous_mul_const g).comp
      ((continuous_const_mul g⁻¹).comp continuous_subtype_val)).subtype_mk _

@[simp]
theorem conjugationHom_apply (N : Subgroup G) [N.Normal] (g : G) (n : N) :
    conjugationHom N g n =
      ⟨g⁻¹ * (n : G) * g, by
        simpa only [inv_inv] using
          (inferInstance : N.Normal).conj_mem (n : G) n.property g⁻¹⟩ :=
  rfl

omit [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- The conjugation compatible-pair identity on coefficients. -/
theorem conjugationHom_smul (N : Subgroup G) [N.Normal] (g : G) (n : N) (m : M) :
    (DistribSMul.toAddMonoidHom M g) (conjugationHom N g n • m) =
      n • (DistribSMul.toAddMonoidHom M g) m := by
  -- Unfold the subgroup action so the compatible-pair identity is an identity for the ambient
  -- `G`-action, where `mul_smul` applies directly.
  change g • ((g⁻¹ * (n : G) * g) • m) = (n : G) • (g • m)
  simp [smul_smul, mul_assoc]

omit [IsTopologicalGroup G] [IsTopologicalAddGroup M] in
theorem continuous_smulAddMonoidHom (g : G) :
    Continuous (DistribSMul.toAddMonoidHom M g) := by
  -- The bundled additive hom has the same function as the fixed-scalar action map.
  change Continuous (fun m : M => g • m)
  exact continuous_const_smul g

/-- Conjugation by `g`, with the coefficient action of `g`, on explicit `H¹`. -/
noncomputable def explicitConj1 (N : Subgroup G) [N.Normal] (g : G) : H1 N M →+ H1 N M :=
  explicitMap1 N M N M (conjugationHom N g) (DistribSMul.toAddMonoidHom M g)
    (continuous_smulAddMonoidHom g) (conjugationHom_smul N g)

/-- The representative formula for `explicitConj1`. -/
@[simp]
theorem explicitConj1_mk (N : Subgroup G) [N.Normal] (g : G) (c : Z1 N M) :
    explicitConj1 N g (c : H1 N M) =
      (cocyclesMap1 N M N M (conjugationHom N g)
        (DistribSMul.toAddMonoidHom M g) (continuous_smulAddMonoidHom g)
        (conjugationHom_smul N g) c : H1 N M) :=
  explicitMap1_mk N M N M _ _ _ _ c

/-- Conjugation by the identity gives the identity map on explicit `H¹`. -/
@[simp]
theorem explicitConj1_one (N : Subgroup G) [N.Normal] :
    explicitConj1 (M := M) N 1 = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitConj1_mk, AddMonoidHom.id_apply]
      apply congrArg (fun z : Z1 N M => (z : H1 N M))
      ext n
      simp [cocyclesMap1_apply]

/-- Successive conjugations compose in the order dictated by the left `G`-action. -/
theorem explicitConj1_mul (N : Subgroup G) [N.Normal] (g h : G) :
    explicitConj1 (M := M) N (g * h) =
      (explicitConj1 (M := M) N g).comp (explicitConj1 (M := M) N h) := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitConj1_mk, AddMonoidHom.comp_apply, explicitConj1_mk, explicitConj1_mk]
      apply congrArg (fun z : Z1 N M => (z : H1 N M))
      ext n
      simp only [cocyclesMap1_coe, cochainsMap1_apply, MonoidHom.coe_coe, conjugationHom_apply,
        mul_inv_rev, DistribSMul.toAddMonoidHom_apply]
      convert mul_smul g h ((c : N → M) (conjugationHom N (g * h) n)) using 1 <;>
        simp [conjugationHom_apply, mul_assoc]

noncomputable instance (N : Subgroup G) [N.Normal] : SMul G (H1 N M) where
  smul g := explicitConj1 (M := M) N g

noncomputable instance (N : Subgroup G) [N.Normal] : MulAction G (H1 N M) where
  one_smul x := by
    -- The `SMul` instance is defined by the explicit map, so this is its identity law.
    change explicitConj1 (M := M) N 1 x = x
    rw [explicitConj1_one]
    rfl
  mul_smul g h x := by
    -- Likewise, the action law is the composition law for the compatible pairs.
    change explicitConj1 (M := M) N (g * h) x =
      explicitConj1 (M := M) N g (explicitConj1 (M := M) N h x)
    rw [explicitConj1_mul]
    rfl

/-- An element of the subgroup acts trivially on its explicit first cohomology. -/
theorem explicitConj1_eq_id_of_mem (N : Subgroup G) [N.Normal] (g : N) :
    explicitConj1 (M := M) N (g : G) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
      rw [explicitConj1_mk, AddMonoidHom.id_apply, H1pi_eq_iff]
      refine mem_B1_iff.2 ⟨(c : N → M) g, ?_⟩
      intro n
      simp only [Pi.sub_apply]
      rw [cocyclesMap1_apply]
      -- Put the pointwise difference in the ambient `G`-action before using the cocycle laws.
      change (n : G) • (c : N → M) g - (c : N → M) g =
        (g : G) • (c : N → M) ((g : N)⁻¹ * n * g) - (c : N → M) n
      have h₂ := (mem_Z1_iff.1 c.property).2 ((g : N)⁻¹ * n) (g : N)
      have h₃ := (mem_Z1_iff.1 c.property).2 (g : N)⁻¹ n
      have hi := map_inv_of_mem_Z1 c.property (g : N)
      simp only [Subgroup.smul_def] at h₂ h₃ hi ⊢
      rw [h₂, h₃]
      simp only [smul_add, sub_eq_add_neg, add_assoc]
      rw [← mul_smul, ← mul_smul]
      simp [hi]

end

end TauCeti.ContCohomology
