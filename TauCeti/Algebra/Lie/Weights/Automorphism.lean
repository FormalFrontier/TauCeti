/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Automorphisms normalising a Cartan subalgebra

Let `σ` be an automorphism of a Lie algebra `L` which normalises a nilpotent subalgebra `H`, in
the sense that `H.map σ = H`. Then `σ` restricts to an automorphism `σ|H` of `H`, and it carries
the root space of `χ : H → R` onto the root space of `χ ∘ (σ|H)⁻¹`: the defining condition
`⁅y, z⁆ = χ y • z` is transported by rewriting `y` as `σ (σ⁻¹ y)`. So `σ` permutes the weights,
and in the Killing setting it also transports the `sl₂` data attached to a root, sending the
coroot of `α` to the coroot of the permuted root.

This is the input the diagram automorphisms of a split semisimple Lie algebra need. A graph
symmetry of the Dynkin diagram is realised on the Serre presentation as an automorphism permuting
the Chevalley generators, hence normalising the Cartan subalgebra they span, and the
Chevalley--Demazure construction has to know what it does to the remaining root vectors.

The Weyl automorphism `TauCeti.weylAut` of an `sl₂` triple also permutes root spaces, by
`TauCeti.weylAut_map_rootSpace`, but that statement is proved from the exponential formula rather
than from a normalisation hypothesis and is not an instance of what is proved here.

## Main definitions

* `TauCeti.restrictAut`: the automorphism of `H` obtained by restricting a normalising
  automorphism of `L`.
* `TauCeti.weightPerm`: the induced permutation of the weights of `H` acting on `L`.

## Main results

* `TauCeti.map_mem_rootSpace` and `TauCeti.map_rootSpace_eq`: a normalising automorphism carries
  the root space of `χ` onto the root space of `χ ∘ (σ|H)⁻¹`.
* `TauCeti.weightPerm_neg`: the induced permutation commutes with negation of weights.
* `TauCeti.isSl2Triple_map`: an `sl₂` triple is carried to an `sl₂` triple.
* `TauCeti.map_coroot_weightPerm`: a normalising automorphism sends the coroot of a root to the
  coroot of the permuted root.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §16.5.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.

This supplies part of the pinning data for the explicit Chevalley--Demazure construction in Layer
9 of `TauCetiRoadmap/ReductiveGroups/README.md`, which is consumed by milestones L0 and L1 of the
`CFSGStatement` roadmap.
-/

public section

namespace TauCeti

open LieAlgebra LieModule

universe u v

section Restrict

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L}

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

namespace LieSubalgebra

/-- An automorphism normalising `H` maps `H` into itself. -/
theorem apply_mem_of_map_eq_self {y : L} (hy : y ∈ H) : σ y ∈ H := by
  rw [← hσ, LieSubalgebra.mem_map]
  exact ⟨y, hy, rfl⟩

/-- If a normalising automorphism moves `y` into `H`, then `y` was already in `H`. -/
theorem mem_of_apply_mem_of_map_eq_self {y : L} (hy : σ y ∈ H) : y ∈ H := by
  rw [← hσ, LieSubalgebra.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  exact σ.injective hzy ▸ hz

/-- The inverse of a normalising automorphism maps `H` into itself. -/
theorem symm_apply_mem_of_map_eq_self {y : L} (hy : y ∈ H) : σ.symm y ∈ H :=
  mem_of_apply_mem_of_map_eq_self σ hσ (by simpa using hy)

end LieSubalgebra

/-- The restriction to `H` of an automorphism of `L` normalising `H`. -/
def restrictAut : H ≃ₗ⁅R⁆ H where
  toFun y := ⟨σ y, LieSubalgebra.apply_mem_of_map_eq_self σ hσ y.2⟩
  invFun y := ⟨σ.symm y, LieSubalgebra.symm_apply_mem_of_map_eq_self σ hσ y.2⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' := by intro x y; ext; exact σ.map_lie x y
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
theorem coe_restrictAut_apply (y : H) : (restrictAut σ hσ y : L) = σ y := (rfl)

@[simp]
theorem coe_restrictAut_symm_apply (y : H) :
    ((restrictAut σ hσ).symm y : L) = σ.symm y := (rfl)

namespace LieSubalgebra

/-- The inverse of a normalising automorphism normalises `H` as well. -/
theorem map_symm_eq_self_of_map_eq_self : H.map (σ.symm : L →ₗ⁅R⁆ L) = H := by
  ext y
  rw [LieSubalgebra.mem_map]
  refine ⟨?_, fun hy => ⟨σ y, apply_mem_of_map_eq_self σ hσ hy, by simp⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact symm_apply_mem_of_map_eq_self σ hσ hz

end LieSubalgebra

/-- The restriction of the inverse automorphism is the inverse of the restriction. -/
theorem restrictAut_symm_symm_apply (y : H) :
    (restrictAut σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ)).symm y =
      restrictAut σ hσ y := by
  ext
  simp

end Restrict

section RootSpace

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} [LieRing.IsNilpotent H]

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

omit [LieRing.IsNilpotent H] in
/-- A normalising automorphism intertwines the two `H`-endomorphisms cutting out the root spaces of
`χ` and of `χ ∘ (σ|H)⁻¹`. -/
private theorem map_sub_smul_one_apply (χ : H → R) (y : H) (z : L) :
    (toEnd R H L y - (χ ∘ (restrictAut σ hσ).symm) y • (1 : Module.End R L)) (σ z) =
      σ ((toEnd R H L ((restrictAut σ hσ).symm y) - χ ((restrictAut σ hσ).symm y) •
        (1 : Module.End R L)) z) := by
  have hy : ⁅y, σ z⁆ = σ ⁅(restrictAut σ hσ).symm y, z⁆ := by
    rw [LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket_of_module, σ.map_lie,
      coe_restrictAut_symm_apply, LieEquiv.apply_symm_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
    map_smul, toEnd_apply_apply, Function.comp_apply, hy]

/-- A normalising automorphism carries the root space of `χ` into the root space of the weight
`χ ∘ (σ|H)⁻¹` obtained by precomposing with the inverse of its restriction. -/
theorem map_mem_rootSpace {χ : H → R} {z : L} (hz : z ∈ rootSpace H χ) :
    σ z ∈ rootSpace H (χ ∘ (restrictAut σ hσ).symm) := by
  rw [rootSpace, mem_genWeightSpace] at hz ⊢
  intro y
  obtain ⟨k, hk⟩ := hz ((restrictAut σ hσ).symm y)
  refine ⟨k, ?_⟩
  suffices h : ∀ (n : ℕ) (w : L),
      ((toEnd R H L y - (χ ∘ (restrictAut σ hσ).symm) y • (1 : Module.End R L)) ^ n) (σ w) =
        σ (((toEnd R H L ((restrictAut σ hσ).symm y) -
          χ ((restrictAut σ hσ).symm y) • (1 : Module.End R L)) ^ n) w) by
    rw [h k z, hk, map_zero]
  intro n
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
      map_sub_smul_one_apply σ hσ χ y w, ih]

/-- A normalising automorphism carries the root space of `χ` **onto** the root space of
`χ ∘ (σ|H)⁻¹`: the inverse automorphism normalises `H` too, and transports the second root space
back into the first. -/
theorem map_rootSpace_eq (χ : H → R) :
    (rootSpace H χ).toSubmodule.map (σ.toLinearEquiv : L →ₗ[R] L) =
      (rootSpace H (χ ∘ (restrictAut σ hσ).symm)).toSubmodule := by
  ext w
  simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule]
  refine ⟨?_, fun hw => ⟨σ.symm w, ?_, by simp⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact map_mem_rootSpace σ hσ hz
  · have hcomp : (χ ∘ (restrictAut σ hσ).symm) ∘
        (restrictAut σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ)).symm = χ := by
      funext y
      simp [restrictAut_symm_symm_apply σ hσ y]
    have h := map_mem_rootSpace σ.symm
      (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ) hw
    rwa [hcomp] at h

/-- The root space of `χ ∘ (σ|H)⁻¹` is nonzero whenever the root space of `χ` is. -/
private theorem genWeightSpace_comp_restrictAut_symm_ne_bot (χ : Weight R H L) :
    genWeightSpace L ((χ : H → R) ∘ (restrictAut σ hσ).symm) ≠ ⊥ := by
  obtain ⟨z, hz, hz₀⟩ := χ.exists_ne_zero
  intro hbot
  have hmem : σ z ∈ genWeightSpace L ((χ : H → R) ∘ (restrictAut σ hσ).symm) :=
    map_mem_rootSpace σ hσ hz
  rw [hbot, LieSubmodule.mem_bot] at hmem
  exact hz₀ (by simpa using congrArg σ.symm hmem)

/-- The weight of `H` acting on `L` obtained from `χ` by precomposing with the inverse of the
restriction of a normalising automorphism. -/
private def weightMap (χ : Weight R H L) : Weight R H L :=
  ⟨(χ : H → R) ∘ (restrictAut σ hσ).symm, genWeightSpace_comp_restrictAut_symm_ne_bot σ hσ χ⟩

@[simp]
private theorem coe_weightMap (χ : Weight R H L) :
    (weightMap σ hσ χ : H → R) = (χ : H → R) ∘ (restrictAut σ hσ).symm := rfl

end RootSpace

section WeightPerm

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} [LieRing.IsNilpotent H]

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

/-- The permutation of the weights of `H` acting on `L` induced by an automorphism of `L`
normalising `H`. -/
def weightPerm : Equiv.Perm (Weight R H L) where
  toFun := weightMap σ hσ
  invFun := weightMap σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ)
  left_inv χ := by
    ext y
    simp [weightMap, restrictAut_symm_symm_apply σ hσ y]
  right_inv χ := by
    ext y
    simp [weightMap, restrictAut_symm_symm_apply σ hσ]

@[simp]
theorem coe_weightPerm (χ : Weight R H L) :
    (weightPerm σ hσ χ : H → R) = (χ : H → R) ∘ (restrictAut σ hσ).symm := (rfl)

@[simp]
theorem weightPerm_apply_apply (χ : Weight R H L) (y : H) :
    weightPerm σ hσ χ y = χ ((restrictAut σ hσ).symm y) := (rfl)

/-- A normalising automorphism carries the root space of a weight into the root space of its
image under the induced permutation. -/
theorem map_mem_rootSpace_weightPerm {χ : Weight R H L} {z : L} (hz : z ∈ rootSpace H χ) :
    σ z ∈ rootSpace H (weightPerm σ hσ χ) :=
  map_mem_rootSpace σ hσ hz

/-- A weight is zero exactly when its image under the induced permutation is. -/
@[simp]
theorem weightPerm_isZero_iff {χ : Weight R H L} :
    (weightPerm σ hσ χ).IsZero ↔ χ.IsZero := by
  simp only [← Weight.coe_eq_zero_iff, coe_weightPerm]
  constructor
  · intro h
    funext y
    simpa using congrFun h (restrictAut σ hσ y)
  · intro h
    funext y
    simpa using congrFun h ((restrictAut σ hσ).symm y)

/-- The induced permutation of the weights carries roots to roots. -/
theorem weightPerm_isNonZero {χ : Weight R H L} (hχ : χ.IsNonZero) :
    (weightPerm σ hσ χ).IsNonZero := fun h => hχ ((weightPerm_isZero_iff σ hσ).mp h)

end WeightPerm

section Sl2Triple

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- An `sl₂` triple is carried to an `sl₂` triple by an automorphism. -/
theorem isSl2Triple_map {h e f : L} (σ : L ≃ₗ⁅R⁆ L) (t : IsSl2Triple h e f) :
    IsSl2Triple (σ h) (σ e) (σ f) where
  h_ne_zero := by simpa using t.h_ne_zero
  lie_e_f := by rw [← LieEquiv.map_lie, t.lie_e_f]
  lie_h_e_nsmul := by rw [← LieEquiv.map_lie, t.lie_h_e_nsmul, map_nsmul]
  lie_h_f_nsmul := by rw [← LieEquiv.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

end Sl2Triple

section Killing

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

variable (σ : L ≃ₗ⁅K⁆ L) (hσ : H.map (σ : L →ₗ⁅K⁆ L) = H)

include hσ

omit [CharZero K] in
/-- The induced permutation of the weights commutes with negation, since precomposition with the
restricted automorphism is linear in the weight. -/
@[simp]
theorem weightPerm_neg (α : Weight K H L) :
    weightPerm σ hσ (-α) = -weightPerm σ hσ α := by
  ext y
  simp

omit [CharZero K] in
/-- The inverse of the induced permutation of the weights also commutes with negation. -/
@[simp]
theorem weightPerm_symm_neg (α : Weight K H L) :
    (weightPerm σ hσ).symm (-α) = -((weightPerm σ hσ).symm α) :=
  (weightPerm σ hσ).injective <| by
    rw [Equiv.apply_symm_apply, weightPerm_neg, Equiv.apply_symm_apply]

/-- A normalising automorphism sends the coroot of a root to the coroot of the permuted root. -/
theorem map_coroot_weightPerm {α : Weight K H L} (hα : α.IsNonZero) :
    σ (LieAlgebra.IsKilling.coroot α : L) =
      (LieAlgebra.IsKilling.coroot (weightPerm σ hσ α) : L) := by
  obtain ⟨h, e, f, t, he, hf⟩ := LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  have hh : h = (LieAlgebra.IsKilling.coroot α : L) := t.h_eq_coroot hα he hf
  have he' : σ e ∈ rootSpace H (weightPerm σ hσ α) := map_mem_rootSpace_weightPerm σ hσ he
  have hf' : σ f ∈ rootSpace H (-weightPerm σ hσ α : Weight K H L) := by
    rw [← weightPerm_neg σ hσ α]
    exact map_mem_rootSpace_weightPerm σ hσ hf
  rw [← hh]
  exact (isSl2Triple_map σ t).h_eq_coroot (weightPerm_isNonZero σ hσ hα) he' hf'

end Killing

end TauCeti
