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
with the preimage of the corresponding component of `W₁^* ⊗ W₂` under the inverse tensor--Hom
equivalence,
and `smulRight_mem_hom` records that a rank-one map built from homogeneous factors is homogeneous
of the summed degree.

This is the `Hom` companion in Layer L0 of `TauCetiRoadmap/HodgeStructures/README.md`.  Only the
source `W₁` must be finite-dimensional (as required by the tensor--Hom equivalence); no
lattice or further finiteness is imposed, and the target `W₂` is arbitrary.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.hom`: the internal Hom pure Hodge structure, transported from
  the dual tensor product.
* `TauCeti.Hodge.HodgeStructureOn.hom_F`, `…hom_conjF`, `…hom_piece`: the internal-Hom filtration,
  conjugate filtration, and pieces as comaps under the inverse tensor--Hom equivalence.
* `TauCeti.Hodge.HodgeStructureOn.hom_piece_apply_mem`: a homogeneous map sends each source
  component to the target component with the expected degree shift.
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

private theorem coe_dualTensorHomEquiv :
    ⇑(dualTensorHomEquiv ℂ W₁ W₂) = dualTensorHom ℂ W₁ W₂ := rfl

private theorem dualTensorHomEquiv_conj :
    Function.Semiconj (dualTensorHomEquiv ℂ W₁ W₂)
      (ω₁.dual.tensorProduct ω₂).toEquiv (ω₁.hom ω₂).toEquiv := by
  intro x
  refine TensorProduct.induction_on x (by simp) ?_ (by
    intro x y hx hy
    simp only [map_add, hx, hy])
  intro φ y
  ext x
  simp only [coe_dualTensorHomEquiv, Conjugation.tensorProduct_toEquiv_tmul,
    dualTensorHom_apply,
    Conjugation.dual_toEquiv_apply, Complex.star_def, Conjugation.hom_toEquiv_apply]
  exact (map_smulₛₗ ω₂.toEquiv _ y).symm

private theorem dualTensorHomEquiv_symm_conj (y : W₁ →ₗ[ℂ] W₂) :
    (dualTensorHomEquiv ℂ W₁ W₂).symm ((ω₁.hom ω₂).toEquiv y) =
      (ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm y) :=
  dualTensorHomEquiv_conj.inverse_left
    (dualTensorHomEquiv ℂ W₁ W₂).symm_apply_apply
    (dualTensorHomEquiv ℂ W₁ W₂).apply_symm_apply y

/-! ### The transported Hodge structure -/

private noncomputable def homAux (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.hom ω₂) (-n₁ + n₂) :=
  (hs₁.dual.tensorProduct hs₂).comap
    (dualTensorHomEquiv ℂ W₁ W₂).symm
    (dualTensorHomEquiv_symm_conj (ω₁ := ω₁) (ω₂ := ω₂))

/-- The internal Hom of two pure Hodge structures, of weight `n₂ - n₁` (that is, `-n₁ + n₂`).

The source is assumed finite-dimensional so that the canonical tensor--Hom map is an equivalence.
The filtration is transported from the tensor product of the dual of the source with the target. -/
noncomputable def hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.hom ω₂) (n₂ - n₁) :=
  { homAux hs₁ hs₂ with
    opposed := fun p ↦ by
      simpa only [show n₂ - n₁ + 1 - p = -n₁ + n₂ + 1 - p by ring] using
        (homAux hs₁ hs₂).opposed p }

/-- The internal-Hom filtration is the comap of the dual-tensor-product filtration under the
inverse tensor--Hom equivalence. -/
@[simp]
theorem hom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.hom hs₂).F p =
      ((hs₁.dual.tensorProduct hs₂).F p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  /- The `F` field of `hom` projects to `homAux.F` by definitional equality,
     since `hom` is defined via a structure update on `homAux`. -/
  change (homAux hs₁ hs₂).F p = _
  exact HodgeStructureOn.comap_F (dualTensorHomEquiv ℂ W₁ W₂).symm
    (dualTensorHomEquiv_symm_conj (ω₁ := ω₁) (ω₂ := ω₂))
    (hs₁.dual.tensorProduct hs₂) p

/-- The internal-Hom conjugate filtration is the comap of the dual-tensor-product conjugate
filtration under the inverse tensor--Hom equivalence. -/
@[simp]
theorem hom_conjF (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.hom hs₂).conjF p =
      ((hs₁.dual.tensorProduct hs₂).conjF p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [conjF_def, hom_F]
  rw [Conjugation.map_comap_eq_comap_map
    (ω₁.hom ω₂) (ω₁.dual.tensorProduct ω₂)
    (dualTensorHomEquiv ℂ W₁ W₂).symm
    (dualTensorHomEquiv_symm_conj (ω₁ := ω₁) (ω₂ := ω₂))]
  rw [← (hs₁.dual.tensorProduct hs₂).conjF_def]

/-- The internal-Hom piece is the comap of the corresponding dual-tensor-product piece under the
inverse tensor--Hom equivalence. -/
@[simp] theorem hom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂)
    (p : ℤ) :
    (hs₁.hom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [piece_def, hom_F, hom_conjF, piece_def,
    show n₂ - n₁ - p = -n₁ + n₂ - p by ring, Submodule.comap_inf]

end Finite

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
    simp only [eval, LinearMap.comp_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
      LinearMap.applyₗ_apply_apply]
    rw [coe_dualTensorHomEquiv, dualTensorHom_apply]
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

/-- If `φ` lies in the degree-`a` component of the dual and `y` in the degree-`b` component of
`hs₂`, then the rank-one map `φ.smulRight y` lies in degree `a + b` of the internal Hom. -/
theorem smulRight_mem_hom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {a b : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece a) (hy : y ∈ hs₂.piece b) :
    φ.smulRight y ∈ (hs₁.hom hs₂).piece (a + b) := by
  have h : dualTensorHomEquiv ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) = φ.smulRight y := by
    rw [coe_dualTensorHomEquiv]
    ext x
    simp only [dualTensorHom_apply, LinearMap.smulRight_apply]
  rw [hom_piece, Submodule.mem_comap]
  rw [← h, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact hs₁.dual.tmul_mem_tensorProduct hs₂ hφ hy

end Finite

end HodgeStructureOn

end TauCeti.Hodge
