/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Geometry.Hodge.Dual
public import TauCeti.Geometry.Hodge.TensorProduct

/-!
# Internal Homs of pure Hodge structures

For finite-dimensional complex vector spaces, the internal Hom is the tensor product
`W₁^* ⊗ W₂`.  We use Mathlib's canonical equivalence between this tensor product and the space of
complex-linear maps, and transport the Hodge structure on the tensor product.  Thus the
construction has weight `n₂ - n₁`, as expected.

The conjugation on a linear map is the twisted conjugate
`f ↦ ω₂ ∘ f ∘ ω₁`.  The theorem `hom_piece` identifies each Hodge component of the internal Hom
with the preimage of the corresponding component of `W₁^* ⊗ W₂` under the tensor--Hom equivalence,
and `smulRight_mem_hom` records that a rank-one map built from homogeneous factors is homogeneous
of the summed degree.

This is the `Hom` companion in Layer L0 of `TauCetiRoadmap/HodgeStructures/README.md`.  The
only the source `W₁` must be finite-dimensional (as required by the tensor--Hom equivalence); no
lattice or further finiteness is imposed, and the target `W₂` is arbitrary.

## Main declarations

* `TauCeti.Hodge.Conjugation.hom`: the conjugation on a linear-map space induced by two
  conjugations.
* `TauCeti.Hodge.HodgeStructureOn.hom`: the internal Hom pure Hodge structure, transported from
  the dual tensor product.
* `TauCeti.Hodge.HodgeStructureOn.hom_piece`: the internal-Hom piece as a tensor--Hom preimage.
* `TauCeti.Hodge.HodgeStructureOn.hom_piece_apply_mem`: a homogeneous map sends each source
  component to the target component with the expected degree shift.
* `TauCeti.Hodge.HodgeStructureOn.dualTensorHomEquiv_tmul_mem_hom`: images of homogeneous pure
  tensors give homogeneous maps.
* `TauCeti.Hodge.HodgeStructureOn.smulRight_mem_hom`: rank-one maps from homogeneous factors give
  homogeneous maps.

The construction follows Peters--Steenbrink, *Mixed Hodge Structures*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W₁ : Type u} {W₂ : Type v} [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂]
variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

section Finite

variable [FiniteDimensional ℂ W₁]

private theorem dualTensorHomEquiv_conj (x : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHomEquiv ℂ W₁ W₂
        ((ω₁.dual.tensorProduct ω₂).toEquiv x) =
      (ω₁.hom ω₂).toEquiv (dualTensorHomEquiv ℂ W₁ W₂ x) := by
  refine TensorProduct.induction_on x (by simp) ?_ (by
    intro x y hx hy
    simp only [map_add, hx, hy])
  intro φ y
  ext x
  simp only [dualTensorHomEquiv, Conjugation.tensorProduct_toEquiv_tmul,
    LinearEquiv.ofBijective_apply, dualTensorHom_apply,
    Conjugation.dual_toEquiv_apply, Complex.star_def, Conjugation.hom_toEquiv_apply]
  exact (map_smulₛₗ ω₂.toEquiv _ y).symm

/-! ### The transported Hodge structure -/

private noncomputable def homAux (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.hom ω₂) (-n₁ + n₂) :=
  (hs₁.dual.tensorProduct hs₂).comap
    (dualTensorHomEquiv ℂ W₁ W₂).symm
    (fun y ↦ (show Function.Semiconj (dualTensorHomEquiv ℂ W₁ W₂)
        (ω₁.dual.tensorProduct ω₂).toEquiv (ω₁.hom ω₂).toEquiv from
      dualTensorHomEquiv_conj (ω₁ := ω₁) (ω₂ := ω₂)).inverse_left
      (dualTensorHomEquiv ℂ W₁ W₂).symm_apply_apply
      (dualTensorHomEquiv ℂ W₁ W₂).apply_symm_apply y)

/-- The internal Hom of two pure Hodge structures, of weight `n₂ - n₁` (that is, `-n₁ + n₂`).

The source is assumed finite-dimensional so that the canonical tensor--Hom map is an equivalence.
The filtration is transported from the tensor product of the dual of the source with the target. -/
noncomputable def hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.hom ω₂) (n₂ - n₁) := by
  have h : n₂ - n₁ = -n₁ + n₂ := by omega
  exact h.symm ▸ homAux hs₁ hs₂

private theorem homAux_piece (m : ℤ) (h : m = -n₁ + n₂)
    (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (h.symm ▸ homAux hs₁ hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  cases h
  exact HodgeStructureOn.comap_piece (dualTensorHomEquiv ℂ W₁ W₂).symm
    (fun y ↦ (show Function.Semiconj (dualTensorHomEquiv ℂ W₁ W₂)
        (ω₁.dual.tensorProduct ω₂).toEquiv (ω₁.hom ω₂).toEquiv from
      dualTensorHomEquiv_conj (ω₁ := ω₁) (ω₂ := ω₂)).inverse_left
      (dualTensorHomEquiv ℂ W₁ W₂).symm_apply_apply
      (dualTensorHomEquiv ℂ W₁ W₂).apply_symm_apply y)
    (hs₁.dual.tensorProduct hs₂) p

/-- The internal-Hom piece is the comap of the corresponding dual-tensor-product piece under the
inverse tensor--Hom equivalence. -/
theorem hom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    (p : ℤ) :
    (hs₁.hom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  unfold hom
  exact homAux_piece (n₂ - n₁) (by omega) hs₁ hs₂ p

end Finite

/-- The tensor--Hom equivalence sends a pure tensor to the corresponding rank-one map. -/
@[simp]
theorem dualTensorHomEquiv_tmul (φ : Module.Dual ℂ W₁) (y : W₂) :
    dualTensorHom ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) = φ.smulRight y := by
  ext x
  simp only [dualTensorHom_apply, LinearMap.smulRight_apply]

section Finite

variable [FiniteDimensional ℂ W₁]

/-- A map in the degree-`p` internal-Hom piece sends the degree-`a` source component into the
degree-`a + p` target component. -/
theorem hom_piece_apply_mem (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p a : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.hom hs₂).piece p) {x : W₁} (hx : x ∈ hs₁.piece a) :
    f x ∈ hs₂.piece (a + p) := by
  rw [hom_piece, Submodule.mem_comap] at hf
  rw [tensorProduct_piece_eq_iSup] at hf
  let eval : (Module.Dual ℂ W₁ ⊗[ℂ] W₂) →ₗ[ℂ] W₂ :=
    (LinearMap.applyₗ (R := ℂ) x).comp (dualTensorHomEquiv ℂ W₁ W₂).toLinearMap
  have hmem (r : ℤ) :
      Submodule.map₂ (TensorProduct.mk ℂ (Module.Dual ℂ W₁) W₂)
          (hs₁.dual.piece r) (hs₂.piece (p - r)) ≤
        (hs₂.piece (a + p)).comap eval := by
    refine Submodule.map₂_le.mpr ?_
    intro φ hφ y hy
    rw [Submodule.mem_comap]
    simp only [eval, LinearMap.comp_apply, TensorProduct.mk_apply,
      LinearMap.applyₗ_apply_apply]
    -- Expose the equivalence coercion so its pure-tensor application lemma can be used.
    change (dualTensorHomEquiv ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y)) x ∈ hs₂.piece (a + p)
    simp only [dualTensorHomEquiv, LinearEquiv.ofBijective_apply, dualTensorHom_apply]
    by_cases har : a = -r
    · have hdeg : p - r = a + p := by omega
      exact (hs₂.piece (a + p)).smul_mem (φ x) (hdeg ▸ hy)
    · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ har, zero_smul]
      exact (hs₂.piece (a + p)).zero_mem
  have ht : eval ((dualTensorHomEquiv ℂ W₁ W₂).symm f) ∈ hs₂.piece (a + p) := by
    refine Submodule.iSup_induction _ (motive := fun t ↦ eval t ∈ hs₂.piece (a + p)) hf
      (fun r t ht ↦ hmem r ht) (by simp [eval]) ?_
    intro t₁ t₂ ht₁ ht₂
    simpa only [map_add] using (hs₂.piece (a + p)).add_mem ht₁ ht₂
  simpa only [eval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.applyₗ_apply_apply] using ht

/-- The image of a pure tensor of homogeneous factors is a homogeneous map in the internal Hom. -/
theorem dualTensorHomEquiv_tmul_mem_hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    {a b : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece a) (hy : y ∈ hs₂.piece b) :
    dualTensorHomEquiv ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) ∈ (hs₁.hom hs₂).piece (a + b) := by
  rw [hom_piece, Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact hs₁.dual.tmul_mem_tensorProduct hs₂ hφ hy

/-- If `φ` lies in the degree-`a` component of the dual and `y` in the degree-`b` component of
`hs₂`, then the rank-one map `φ.smulRight y` lies in degree `a + b` of the internal Hom. -/
theorem smulRight_mem_hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {a b : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece a) (hy : y ∈ hs₂.piece b) :
    φ.smulRight y ∈ (hs₁.hom hs₂).piece (a + b) := by
  rw [← dualTensorHomEquiv_tmul]
  exact hs₁.dualTensorHomEquiv_tmul_mem_hom hs₂ hφ hy

end Finite

end HodgeStructureOn

end TauCeti.Hodge
