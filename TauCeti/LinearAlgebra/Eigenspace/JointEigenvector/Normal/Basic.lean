/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RepresentationTheory.Induction.Conjugate
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

/-!
# Joint eigenspaces for normal subgroups

If `N` is a normal subgroup of `G`, conjugation by `g : G` permutes the characters of `N`.
For a representation `ρ` of `G`, the operator `ρ g` carries the joint `N`-eigenspace of a
character `χ` onto the joint eigenspace of the conjugated character
`n ↦ χ (g⁻¹ * n * g)`.

This is the representation-theoretic bridge used in the Lie--Kolchin argument. The derived
subgroup supplies characters with nonzero joint weight spaces; normality makes the ambient group
permute those characters while transporting their corresponding spaces, and connectedness can then
force that permutation to be trivial.

## Main declarations

* `map_iInf_eigenspace_unitHom_eq_conjNormal`: an ambient representation operator maps a
  normal subgroup's `χ`-weight space onto the conjugated-character weight space.
* `iInf_eigenspace_unitHom_conjNormal_ne_bot_iff`: conjugation preserves which character
  weight spaces are nonzero.
* `nonzeroJointWeightAction`: the resulting permutation action of the ambient group on the
  characters having nonzero joint weight space.
* `map_iInf_eigenspace_unitHom_eq_self_of_nonzeroJointWeightAction_eq`: a character fixed by the
  permutation action has an ambient-invariant joint weight space.
* `map_iInf_eigenspace_unitHom_eq_self_of_mem_ker_nonzeroJointWeightAction`: the kernel of that
  action preserves every nonzero joint weight space.

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
      ⨅ n : N, (ρ n).eigenspace
        ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ n) := by
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
    _ = ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ n : K) • ρ g v := by
      rw [MulEquiv.monoidHomCongrLeftEquiv_apply, MonoidHom.comp_apply]
      rw [map_inv (MulAut.conjNormal (H := N)) g, MulAut.inv_def]
      simp only [MulEquiv.coe_toMonoidHom]

/-- Let `N` be a normal subgroup of `G`. For a representation `ρ` of `G`, the operator `ρ g`
maps the joint `N`-eigenspace of `χ` exactly onto the joint eigenspace of the conjugated
character `n ↦ χ (g⁻¹ * n * g)`.

No field, finite-dimensionality, commutativity of `N`, or semisimplicity hypothesis is needed. -/
@[simp]
theorem map_iInf_eigenspace_unitHom_eq_conjNormal (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace (χ n)).map (ρ g) =
      ⨅ n : N, (ρ n).eigenspace
        ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ n) := by
  apply le_antisymm (map_iInf_eigenspace_unitHom_le_conjNormal N ρ g χ)
  intro v hv
  have hpreimage : ρ g⁻¹ v ∈ ⨅ n : N, (ρ n).eigenspace (χ n) := by
    have h := map_iInf_eigenspace_unitHom_le_conjNormal N ρ g⁻¹
      ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ)
    have hmapped := h ⟨v, hv, rfl⟩
    have hcharacter :
        (MulAut.conjNormal g⁻¹).monoidHomCongrLeftEquiv
          ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ) = χ := by
      rw [map_inv (MulAut.conjNormal (H := N)) g, MulAut.inv_def,
        ← MulEquiv.symm_monoidHomCongrLeftEquiv]
      exact Equiv.symm_apply_apply _ χ
    rw [hcharacter] at hmapped
    exact hmapped
  refine ⟨ρ g⁻¹ v, hpreimage, ?_⟩
  simp [← Module.End.mul_apply, ← map_mul]

/-- Conjugating a character by an ambient group element preserves whether its joint weight
space for the normal subgroup is nonzero. -/
theorem iInf_eigenspace_unitHom_conjNormal_ne_bot_iff (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace
      ((MulAut.conjNormal g).monoidHomCongrLeftEquiv χ n)) ≠ ⊥ ↔
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

/-- The permutation induced by an ambient group element on the characters whose joint weight space
for the normal subgroup is nonzero. This is the pointwise construction underlying
`nonzeroJointWeightAction`. -/
private def nonzeroJointWeightEquiv (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) :
    {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} ≃
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} :=
  Equiv.Perm.subtypePerm
    ((MulAut.conjNormal g).monoidHomCongrLeftEquiv : Equiv.Perm (N →* Kˣ))
      fun χ ↦ iInf_eigenspace_unitHom_conjNormal_ne_bot_iff N ρ g χ

/-- The ambient group acts by permutations on the characters having nonzero joint weight space for
a normal subgroup. This is the abstract permutation action used in the Lie--Kolchin argument. -/
def nonzeroJointWeightAction (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) :
    G →* Equiv.Perm {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} where
  toFun := nonzeroJointWeightEquiv N ρ
  map_one' := by
    simpa only [nonzeroJointWeightEquiv, map_one, MulAut.one_def,
      MulEquiv.monoidHomCongrLeftEquiv_refl, Equiv.Perm.one_def] using
        Equiv.Perm.subtypePerm_one
          (fun χ : N →* Kˣ ↦ (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥)
  map_mul' g₁ g₂ := by
    simpa only [nonzeroJointWeightEquiv, map_mul, MulAut.mul_def,
      MulEquiv.monoidHomCongrLeftEquiv_trans, Equiv.Perm.mul_def] using
        (Equiv.Perm.subtypePerm_mul
          ((MulAut.conjNormal g₁).monoidHomCongrLeftEquiv : Equiv.Perm (N →* Kˣ))
          ((MulAut.conjNormal g₂).monoidHomCongrLeftEquiv : Equiv.Perm (N →* Kˣ))
          (fun χ ↦ iInf_eigenspace_unitHom_conjNormal_ne_bot_iff N ρ g₁ χ)
          (fun χ ↦ iInf_eigenspace_unitHom_conjNormal_ne_bot_iff N ρ g₂ χ)).symm

/-- The underlying character of the permutation action is obtained by conjugating with `g`. -/
@[simp]
theorem nonzeroJointWeightAction_apply_coe (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    (((nonzeroJointWeightAction N ρ g) χ :
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) : N →* Kˣ) =
        (MulAut.conjNormal g).monoidHomCongrLeftEquiv χ := by
  rfl

/-- If an ambient group element fixes a nonzero normal-subgroup weight, its representation
operator maps the corresponding joint weight space onto itself. -/
theorem map_iInf_eigenspace_unitHom_eq_self_of_nonzeroJointWeightAction_eq
    (N : Subgroup G) [N.Normal] (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥})
    (hχ : nonzeroJointWeightAction N ρ g χ = χ) :
    (⨅ n : N, (ρ n).eigenspace (χ.1 n)).map (ρ g) =
      ⨅ n : N, (ρ n).eigenspace (χ.1 n) := by
  rw [map_iInf_eigenspace_unitHom_eq_conjNormal]
  exact congrArg (fun ψ : N →* Kˣ ↦ ⨅ n : N, (ρ n).eigenspace (ψ n))
    (congrArg Subtype.val hχ)

/-- Every element in the kernel of the permutation action preserves each nonzero
normal-subgroup joint weight space. -/
theorem map_iInf_eigenspace_unitHom_eq_self_of_mem_ker_nonzeroJointWeightAction
    (N : Subgroup G) [N.Normal] (ρ : G →* Module.End K V) (g : G)
    (hg : g ∈ (nonzeroJointWeightAction N ρ).ker)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    (⨅ n : N, (ρ n).eigenspace (χ.1 n)).map (ρ g) =
      ⨅ n : N, (ρ n).eigenspace (χ.1 n) := by
  apply map_iInf_eigenspace_unitHom_eq_self_of_nonzeroJointWeightAction_eq N ρ g χ
  have h := DFunLike.congr_fun ((MonoidHom.mem_ker).mp hg) χ
  simpa using h

end TauCeti

end
