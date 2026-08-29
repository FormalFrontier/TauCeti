/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Induction.Conjugate
public import TauCeti.Algebra.Group.Subgroup.Character
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Joint eigenspaces for normal subgroups

If `N` is a normal subgroup of `G`, conjugation by `g : G` permutes the characters of `N`.
For a representation `ρ` of `G`, the operator `ρ g` carries the joint `N`-eigenspace of a
character `χ` onto the joint eigenspace of the conjugated character
`n ↦ χ (g⁻¹ * n * g)`.

This is the representation-theoretic bridge used in the Lie--Kolchin argument. The derived
subgroup supplies finitely many character weight spaces; normality makes the ambient group
permute those spaces, and connectedness can then force that permutation to be trivial.

## Main declarations

* `MonoidHom.conjNormalEquiv`: conjugation by an ambient element as an equivalence of the
  character set of a normal subgroup.
* `map_iInf_eigenspace_unitHom_eq_conjNormal`: an ambient representation operator maps a
  normal subgroup's `χ`-weight space onto the conjugated-character weight space.
* `iInf_eigenspace_unitHom_conjNormal_ne_bot_iff`: conjugation preserves which character
  weight spaces are nonzero.
* `nonzeroJointWeightAction`: the resulting permutation action of the ambient group on the
  nonzero character weight spaces.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. E. Humphreys, *Linear Algebraic Groups*, §17.6.
-/

public section

noncomputable section

namespace TauCeti

variable {G K V : Type*} [Group G] [CommRing K] [AddCommGroup V] [Module K V]

private theorem map_iInf_eigenspace_unitHom_le_conjNormal (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace (χ n)).map (ρ g) ≤
      ⨅ n : N, (ρ n).eigenspace (MonoidHom.conjNormal g χ n) := by
  rintro _ ⟨v, hv, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
  have hvn := (Submodule.mem_iInf _).mp hv
  rw [Module.End.mem_eigenspace_iff]
  calc
    ρ n (ρ g v) = ρ g (ρ (MulAut.conjNormal g⁻¹ n) v) :=
      (Representation.apply_conjNormal_inv ρ g n v).symm
    _ = ρ g ((χ (MulAut.conjNormal g⁻¹ n) : K) • v) := by
      rw [Module.End.mem_eigenspace_iff.mp (hvn (MulAut.conjNormal g⁻¹ n))]
    _ = (χ (MulAut.conjNormal g⁻¹ n) : K) • ρ g v := by rw [map_smul]
    _ = (MonoidHom.conjNormal g χ n : K) • ρ g v := by
      rw [MulAut.conjNormal_inv]
      rw [MonoidHom.conjNormal_apply]

/-- Let `N` be a normal subgroup of `G`. For a representation `ρ` of `G`, the operator `ρ g`
maps the joint `N`-eigenspace of `χ` exactly onto the joint eigenspace of the conjugated
character `n ↦ χ (g⁻¹ * n * g)`.

No field, finite-dimensionality, commutativity of `N`, or semisimplicity hypothesis is needed. -/
theorem map_iInf_eigenspace_unitHom_eq_conjNormal (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace (χ n)).map (ρ g) =
      ⨅ n : N, (ρ n).eigenspace (MonoidHom.conjNormal g χ n) := by
  apply le_antisymm (map_iInf_eigenspace_unitHom_le_conjNormal N ρ g χ)
  intro v hv
  have hpreimage : ρ g⁻¹ v ∈ ⨅ n : N, (ρ n).eigenspace (χ n) := by
    have h := map_iInf_eigenspace_unitHom_le_conjNormal N ρ g⁻¹
      (MonoidHom.conjNormal g χ)
    have hmapped := h ⟨v, hv, rfl⟩
    simpa using hmapped
  refine ⟨ρ g⁻¹ v, hpreimage, ?_⟩
  simp [← Module.End.mul_apply, ← map_mul]

/-- Conjugating a character by an ambient group element preserves whether its joint weight
space for the normal subgroup is nonzero. -/
theorem iInf_eigenspace_unitHom_conjNormal_ne_bot_iff (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace (MonoidHom.conjNormal g χ n)) ≠ ⊥ ↔
      (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥ := by
  rw [← map_iInf_eigenspace_unitHom_eq_conjNormal N ρ g χ]
  have hinjective : Function.Injective
      (Submodule.map (ρ g) : Submodule K V → Submodule K V) :=
    Submodule.map_injective_of_injective (Representation.apply_bijective ρ g).1
  constructor
  · exact fun hmapped hsource ↦ hmapped (by simp [hsource])
  · intro hsource hmapped
    apply hsource
    apply hinjective
    simpa using hmapped

/-- An ambient group element permutes the characters whose joint weight space for the normal
subgroup is nonzero. The underlying permutation sends `χ` to `n ↦ χ (g⁻¹ * n * g)`. -/
def nonzeroJointWeightEquiv (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) :
    {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} ≃
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} :=
  (MonoidHom.conjNormalEquiv N Kˣ g).subtypeEquiv fun χ ↦ by
    simpa only [MonoidHom.conjNormalEquiv_apply] using
      (iInf_eigenspace_unitHom_conjNormal_ne_bot_iff N ρ g χ).symm

@[simp]
theorem nonzeroJointWeightEquiv_apply_coe (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    ((nonzeroJointWeightEquiv N ρ g χ :
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) : N →* Kˣ) =
        MonoidHom.conjNormal g χ := by
  simp only [nonzeroJointWeightEquiv, Equiv.subtypeEquiv_apply,
    MonoidHom.conjNormalEquiv_apply]

/-- The ambient group acts by permutations on the nonzero joint character weight spaces of a
normal subgroup. This is the abstract group action underlying the finite permutation
representation in the Lie--Kolchin argument. -/
def nonzeroJointWeightAction (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) :
    G →* Equiv.Perm {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} where
  toFun := nonzeroJointWeightEquiv N ρ
  map_one' := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    simpa only [Equiv.Perm.one_apply, nonzeroJointWeightEquiv_apply_coe] using
      MonoidHom.conjNormal_one (χ : N →* Kˣ)
  map_mul' g₁ g₂ := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    simpa only [Equiv.Perm.mul_apply, nonzeroJointWeightEquiv_apply_coe] using
      MonoidHom.conjNormal_mul g₁ g₂ (χ : N →* Kˣ)

theorem nonzeroJointWeightAction_apply (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    nonzeroJointWeightAction N ρ g χ = nonzeroJointWeightEquiv N ρ g χ := by
  -- Package the monoid-hom constructor's definitional projection as a stable application rule.
  change nonzeroJointWeightEquiv N ρ g χ = nonzeroJointWeightEquiv N ρ g χ
  rfl

@[simp]
theorem nonzeroJointWeightAction_apply_coe (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    (((nonzeroJointWeightAction N ρ g) χ :
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) : N →* Kˣ) =
        MonoidHom.conjNormal g χ := by
  rw [nonzeroJointWeightAction_apply]
  exact nonzeroJointWeightEquiv_apply_coe N ρ g χ

end TauCeti

end
