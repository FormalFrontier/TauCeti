/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

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

namespace MonoidHom

variable {G A : Type*} [Group G] [Monoid A]

/-- Precomposition by inverse conjugation gives the action of an ambient group element on
characters of a normal subgroup. Thus `(conjNormal g χ) n = χ (g⁻¹ * n * g)`.

The inverse in the definition is the convention for which a representation operator `ρ g`
sends the `χ`-weight space to the `conjNormal g χ`-weight space. -/
def conjNormal {N : Subgroup G} [N.Normal] (g : G) (χ : N →* A) : N →* A :=
  χ.comp (MulAut.conjNormal g⁻¹).toMonoidHom

@[simp]
theorem conjNormal_apply {N : Subgroup G} [N.Normal] (g : G) (χ : N →* A) (n : N) :
    conjNormal g χ n = χ ((MulAut.conjNormal g).symm n) := by
  rfl

@[simp]
theorem conjNormal_one {N : Subgroup G} [N.Normal] (χ : N →* A) :
    conjNormal 1 χ = χ := by
  ext n
  simp [conjNormal]

/-- Conjugating characters is a left action: `g₁ * g₂` first acts by `g₂`, then by `g₁`. -/
theorem conjNormal_mul {N : Subgroup G} [N.Normal] (g₁ g₂ : G) (χ : N →* A) :
    conjNormal (g₁ * g₂) χ = conjNormal g₁ (conjNormal g₂ χ) := by
  ext n
  simp only [conjNormal_apply]
  apply congrArg χ
  apply Subtype.ext
  simp only [MulAut.conjNormal_symm_apply]
  group

@[simp]
theorem conjNormal_inv_apply_conjNormal {N : Subgroup G} [N.Normal] (g : G) (χ : N →* A) :
    conjNormal g⁻¹ (conjNormal g χ) = χ := by
  simp only [← conjNormal_mul, inv_mul_cancel, conjNormal_one]

@[simp]
theorem conjNormal_apply_inv_conjNormal {N : Subgroup G} [N.Normal] (g : G) (χ : N →* A) :
    conjNormal g (conjNormal g⁻¹ χ) = χ := by
  simp only [← conjNormal_mul, mul_inv_cancel, conjNormal_one]

/-- Conjugation by `g` is an equivalence of the character set of a normal subgroup, with
inverse given by conjugation by `g⁻¹`. -/
def conjNormalEquiv (N : Subgroup G) [N.Normal] (A : Type*) [Monoid A] (g : G) :
    (N →* A) ≃ (N →* A) where
  toFun := conjNormal g
  invFun := conjNormal g⁻¹
  left_inv := conjNormal_inv_apply_conjNormal g
  right_inv := conjNormal_apply_inv_conjNormal g

@[simp]
theorem conjNormalEquiv_apply {N : Subgroup G} [N.Normal] (g : G) (χ : N →* A) :
    conjNormalEquiv N A g χ = conjNormal g χ :=
  by simp [conjNormalEquiv]

@[simp]
theorem conjNormalEquiv_symm {N : Subgroup G} [N.Normal] (g : G) :
    (conjNormalEquiv N A g).symm = conjNormalEquiv N A g⁻¹ := by
  ext χ n
  simp [conjNormalEquiv]

end MonoidHom

variable {G K V : Type*} [Group G] [CommRing K] [AddCommGroup V] [Module K V]

private theorem map_iInf_eigenspace_unitHom_le_conjNormal (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G) (χ : N →* Kˣ) :
    (⨅ n : N, (ρ n).eigenspace (χ n)).map (ρ g) ≤
      ⨅ n : N, (ρ n).eigenspace (MonoidHom.conjNormal g χ n) := by
  rintro _ ⟨v, hv, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
  have hvn := (Submodule.mem_iInf _).mp hv
  let m : N := (MulAut.conjNormal g).symm n
  rw [Module.End.mem_eigenspace_iff]
  calc
    ρ n (ρ g v) = ρ (n * g) v := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * m) v := by
      congr 2
      simp [m, mul_assoc]
    _ = ρ g (ρ m v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g ((χ m : K) • v) := by
      rw [Module.End.mem_eigenspace_iff.mp (hvn m)]
    _ = (χ m : K) • ρ g v := by rw [map_smul]
    _ = (MonoidHom.conjNormal g χ n : K) • ρ g v := by
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
  (MonoidHom.conjNormalEquiv N Kˣ g).subtypeEquiv fun χ ↦
    (iInf_eigenspace_unitHom_conjNormal_ne_bot_iff N ρ g χ).symm

@[simp]
theorem nonzeroJointWeightEquiv_apply_coe (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    ((nonzeroJointWeightEquiv N ρ g χ :
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) : N →* Kˣ) =
        MonoidHom.conjNormal g χ := by
  rfl

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
    change MonoidHom.conjNormal 1 (χ : N →* Kˣ) = χ
    exact MonoidHom.conjNormal_one (χ : N →* Kˣ)
  map_mul' g₁ g₂ := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    change MonoidHom.conjNormal (g₁ * g₂) (χ : N →* Kˣ) =
      MonoidHom.conjNormal g₁ (MonoidHom.conjNormal g₂ χ)
    exact MonoidHom.conjNormal_mul g₁ g₂ (χ : N →* Kˣ)

@[simp]
theorem nonzeroJointWeightAction_apply_coe (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) (g : G)
    (χ : {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) :
    (((nonzeroJointWeightAction N ρ g) χ :
      {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥}) : N →* Kˣ) =
        MonoidHom.conjNormal g χ := by
  rfl

end TauCeti

end
