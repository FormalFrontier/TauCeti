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
# Internal homs of pure Hodge structures

For finite-dimensional pure Hodge structures `V` and `W`, the complex vector space
`Hom_ℂ(V, W)` carries a pure Hodge structure of weight `weight W - weight V`. Its conjugation
sends a map `f` to `x ↦ conj (f (conj x))`, and a map has Hodge degree `r` when it carries the
degree-`p` component of `V` into the degree-`p+r` component of `W`.

The construction uses Mathlib's canonical finite-dimensional equivalence
`V^* ⊗ W ≃ₗ[ℂ] Hom_ℂ(V, W)`. It transports the tensor product of the dual Hodge structure on
`V^*` and the Hodge structure on `W`, rather than rebuilding their internal direct-sum argument.
The conjugation formula is proved compatible with that equivalence, so the transported structure
has the intrinsic conjugation on linear maps.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.internalHom`: the internal hom Hodge structure, of weight
  `n₂ - n₁`.
* `TauCeti.Hodge.HodgeStructureOn.internalHom_piece_eq_comap_iSup`: its degree-`r` component in
  the tensor presentation `V^* ⊗ W`.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_piece_of_mem_internalHom_piece`: a degree-`r` map sends
  the degree-`p` component into the degree-`p+r` component.
* `TauCeti.Hodge.HodgeStructureOn.map_mem_F_of_mem_internalHom_F`: a map in filtration degree
  at least `r` sends `F^p V` into `F^{p+r} W`.
* `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_piece_iff` and
  `TauCeti.Hodge.HodgeStructureOn.mem_internalHom_F_iff`: these degree-shifting properties
  characterize the internal-hom components and filtration steps.

This is the internal-hom companion to duals and tensor products for pure Hodge structures;
the convention follows Peters--Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

variable {W₁ : Type u} {W₂ : Type v}
variable [AddCommGroup W₁] [Module ℂ W₁]
variable [AddCommGroup W₂] [Module ℂ W₂]

/-- Mathlib records `dualTensorHomEquivOfBasis_apply` for the basis-dependent contraction
equivalence, but states no `apply` lemma for `dualTensorHomEquiv`; its forward map is the
contraction `dualTensorHom` itself. -/
private theorem dualTensorHomEquiv_apply [FiniteDimensional ℂ W₁]
    (z : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHomEquiv ℂ W₁ W₂ z = dualTensorHom ℂ W₁ W₂ z :=
  (rfl)

namespace Conjugation

/-- The contraction `V^* ⊗ W → Hom_ℂ(V, W)` intertwines tensor-product conjugation with the
intrinsic conjugation on the space of linear maps. -/
theorem dualTensorHom_map_tensorProduct_conj (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂)
    (z : Module.Dual ℂ W₁ ⊗[ℂ] W₂) :
    dualTensorHom ℂ W₁ W₂ ((ω₁.dual.tensorProduct ω₂).toEquiv z) =
      (ω₁.internalHom ω₂).toEquiv (dualTensorHom ℂ W₁ W₂ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ y =>
      ext x
      simpa only [Conjugation.tensorProduct_toEquiv_tmul, Conjugation.dual_toEquiv_apply,
        dualTensorHom_apply, Conjugation.internalHom_toEquiv_apply_apply, starRingEnd_apply] using
          (ω₂.toEquiv.map_smulₛₗ (φ (ω₁.toEquiv x)) y).symm
  | add x y hx hy => simp [hx, hy]

/-- The inverse of the finite-dimensional contraction equivalence intertwines internal-hom
conjugation with tensor-product conjugation. -/
theorem dualTensorHomEquiv_symm_map_internalHom_conj [FiniteDimensional ℂ W₁]
    (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) (f : W₁ →ₗ[ℂ] W₂) :
    (dualTensorHomEquiv ℂ W₁ W₂).symm ((ω₁.internalHom ω₂).toEquiv f) =
      (ω₁.dual.tensorProduct ω₂).toEquiv ((dualTensorHomEquiv ℂ W₁ W₂).symm f) := by
  apply (dualTensorHomEquiv ℂ W₁ W₂).injective
  rw [LinearEquiv.apply_symm_apply, dualTensorHomEquiv_apply,
    ω₁.dualTensorHom_map_tensorProduct_conj ω₂, ← dualTensorHomEquiv_apply,
    LinearEquiv.apply_symm_apply]

end Conjugation

namespace HodgeStructureOn

variable [FiniteDimensional ℂ W₁]
variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

/-- The internal hom from a pure Hodge structure of weight `n₁` to one of weight `n₂`, as a pure
Hodge structure of weight `n₂ - n₁` on the space of complex-linear maps.

It is the transport of `hs₁.dual.tensorProduct hs₂` through Mathlib's canonical equivalence
`W₁^* ⊗ W₂ ≃ₗ[ℂ] (W₁ →ₗ[ℂ] W₂)`. -/
noncomputable def internalHom (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ →ₗ[ℂ] W₂) (ω₁.internalHom ω₂) (n₂ - n₁) := by
  let e := dualTensorHomEquiv ℂ W₁ W₂
  let pulled := (hs₁.dual.tensorProduct hs₂).comap e.symm
    (ω₁.dualTensorHomEquiv_symm_map_internalHom_conj ω₂)
  exact
    { F := pulled.F
      F_antitone := pulled.F_antitone
      F_top := pulled.F_top
      opposed := fun p ↦ by
        simpa only [sub_eq_add_neg, add_comm] using pulled.opposed p }

/-- The internal-hom filtration is the pullback of the tensor-product filtration on
`V^* ⊗ W`. -/
@[simp]
theorem internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).F p =
      ((hs₁.dual.tensorProduct hs₂).F p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [internalHom, comap_F]

/-- The conjugate internal-hom filtration is the pullback of the conjugate tensor-product
filtration. -/
@[simp]
theorem internalHom_conjF (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).conjF p =
      ((hs₁.dual.tensorProduct hs₂).conjF p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [conjF_def, internalHom_F, Conjugation.map_comap_eq_comap_map
    (ω₁.internalHom ω₂) (ω₁.dual.tensorProduct ω₂) (dualTensorHomEquiv ℂ W₁ W₂).symm
    (ω₁.dualTensorHomEquiv_symm_map_internalHom_conj ω₂), ← conjF_def]

/-- An internal-hom component is the pullback of the corresponding tensor-product component
under `Hom_ℂ(V, W) ≃ₗ V^* ⊗ W`. -/
@[simp]
theorem internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).piece p =
      ((hs₁.dual.tensorProduct hs₂).piece p).comap
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  have hindex : n₂ - n₁ - p = -n₁ + n₂ - p := by ring
  rw [piece_def, internalHom_F, internalHom_conjF, piece_def, Submodule.comap_inf, hindex]

/-- The degree-`p` internal-hom component, presented as the pullback of the sum of
`(V^*)^r ⊗ W^{p-r}`. -/
theorem internalHom_piece_eq_comap_iSup (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.internalHom hs₂).piece p =
      (⨆ r : ℤ, Submodule.map₂ (TensorProduct.mk ℂ (Module.Dual ℂ W₁) W₂)
        ((hs₁.dual).piece r) (hs₂.piece (p - r))).comap
          (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  rw [internalHom_piece, tensorProduct_piece_eq_iSup]

/-- A rank-one map made from a dual vector of degree `p` and a target vector of degree `q` has
internal-hom degree `p + q`. -/
theorem dualTensorHom_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {φ : Module.Dual ℂ W₁} {y : W₂}
    (hφ : φ ∈ (hs₁.dual).piece p) (hy : y ∈ hs₂.piece q) :
    dualTensorHom ℂ W₁ W₂ (φ ⊗ₜ[ℂ] y) ∈ (hs₁.internalHom hs₂).piece (p + q) := by
  rw [internalHom_piece, Submodule.mem_comap, LinearEquiv.coe_coe, ← dualTensorHomEquiv_apply,
    LinearEquiv.symm_apply_apply]
  exact hs₁.dual.tmul_mem_tensorProduct hs₂ hφ hy

/-- A map of internal-hom Hodge degree `p` carries the source component of degree `a` into the
target component of degree `a + p`. -/
theorem map_mem_piece_of_mem_internalHom_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p a : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).piece p) {x : W₁} (hx : x ∈ hs₁.piece a) :
    f x ∈ hs₂.piece (a + p) := by
  let e := dualTensorHomEquiv ℂ W₁ W₂
  have hz : e.symm f ∈ (hs₁.dual.tensorProduct hs₂).piece p := by
    rw [internalHom_piece, Submodule.mem_comap] at hf
    exact hf
  have hle : (hs₁.dual.tensorProduct hs₂).piece p ≤
      (hs₂.piece (a + p)).comap
        ((LinearMap.applyₗ (R := ℂ) x) ∘ₗ dualTensorHom ℂ W₁ W₂) := by
    rw [tensorProduct_piece_eq_iSup]
    refine iSup_le fun r ↦ Submodule.map₂_le.mpr fun φ hφ y hy ↦ ?_
    simp only [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      dualTensorHom_apply, TensorProduct.mk_apply]
    by_cases har : a = -r
    · have hindex : p - r = a + p := by omega
      rw [← hindex]
      exact Submodule.smul_mem _ _ hy
    · rw [hs₁.apply_eq_zero_of_mem_piece_of_ne hx hφ har, zero_smul]
      exact Submodule.zero_mem _
  have he : dualTensorHom ℂ W₁ W₂ (e.symm f) = f := by
    exact e.apply_symm_apply f
  rw [← he]
  exact hle hz

/-- The degree-`r` internal-hom component of a map, evaluated at a vector of Hodge degree `a`,
is the degree-`a + r` component of the value. -/
theorem internalHom_proj_apply_apply (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {r a : ℤ} (f : W₁ →ₗ[ℂ] W₂) {x : W₁}
    (hx : x ∈ hs₁.piece a) :
    (hs₁.internalHom hs₂).proj r f x = hs₂.proj (a + r) (f x) := by
  have hext : LinearMap.applyₗ (R := ℂ) x ∘ₗ (hs₁.internalHom hs₂).proj r =
      hs₂.proj (a + r) ∘ₗ LinearMap.applyₗ (R := ℂ) x := by
    refine (hs₁.internalHom hs₂).linearMap_ext_of_piece fun s g hg ↦ ?_
    have hgx : g x ∈ hs₂.piece (a + s) := hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hx
    rcases eq_or_ne s r with rfl | hsr
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_of_mem hg, hs₂.proj_apply_of_mem hgx]
    · simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        (hs₁.internalHom hs₂).proj_apply_eq_zero_of_mem_of_ne hg hsr, LinearMap.zero_apply,
        hs₂.proj_apply_eq_zero_of_mem_of_ne hgx (by omega : a + s ≠ a + r)]
  exact congrArg (fun L ↦ L f) hext

/-- A map lies in the degree-`p` internal-hom component exactly when it carries every source
component of degree `a` into the target component of degree `a + p`. -/
@[simp]
theorem mem_internalHom_piece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).piece p ↔ ∀ a, ∀ x ∈ hs₁.piece a, f x ∈ hs₂.piece (a + p) := by
  refine ⟨fun hf a x hx ↦ hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hf hx, fun hf ↦ ?_⟩
  refine (hs₁.internalHom hs₂).mem_of_proj_mem fun r ↦ ?_
  rcases eq_or_ne r p with rfl | hrp
  · exact (hs₁.internalHom hs₂).proj_mem r f
  · have hzero : (hs₁.internalHom hs₂).proj r f = 0 :=
      hs₁.linearMap_ext_of_piece fun a x hx ↦ by
        rw [hs₁.internalHom_proj_apply_apply hs₂ f hx,
          hs₂.proj_apply_eq_zero_of_mem_of_ne (hf a x hx) (by omega : a + p ≠ a + r),
          LinearMap.zero_apply]
    rw [hzero]
    exact Submodule.zero_mem _

/-- A map in the `p`-th step of the internal-hom filtration sends the `q`-th step of the source
filtration into the `(p+q)`-th step of the target filtration. -/
theorem map_mem_F_of_mem_internalHom_F (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {f : W₁ →ₗ[ℂ] W₂}
    (hf : f ∈ (hs₁.internalHom hs₂).F p) {x : W₁} (hx : x ∈ hs₁.F q) :
    f x ∈ hs₂.F (p + q) := by
  rw [(hs₁.internalHom hs₂).F_eq_iSup_piece p] at hf
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hf
    (fun r g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  refine Submodule.iSup_induction (motive := fun g ↦ g x ∈ hs₂.F (p + q)) _ hg
    (fun hr g hg ↦ ?_) (by simp) (fun g h hg hh ↦ by simpa using Submodule.add_mem _ hg hh)
  rw [hs₁.F_eq_iSup_piece q] at hx
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hx
    (fun a y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  refine Submodule.iSup_induction (motive := fun y ↦ g y ∈ hs₂.F (p + q)) _ hy
    (fun ha y hy ↦ ?_) (by simp) (fun y z hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
  exact ((hs₂.piece_le_F (a + r)).trans (hs₂.F_antitone (by omega)))
    (hs₁.map_mem_piece_of_mem_internalHom_piece hs₂ hg hy)

/-- A map lies in the `p`-th step of the internal-hom filtration exactly when it sends every
step `F^q` of the source filtration into the step `F^{p+q}` of the target filtration. -/
@[simp]
theorem mem_internalHom_F_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} (f : W₁ →ₗ[ℂ] W₂) :
    f ∈ (hs₁.internalHom hs₂).F p ↔ ∀ q, ∀ x ∈ hs₁.F q, f x ∈ hs₂.F (p + q) := by
  refine ⟨fun hf q x hx ↦ hs₁.map_mem_F_of_mem_internalHom_F hs₂ hf hx, fun hf ↦ ?_⟩
  refine (hs₁.internalHom hs₂).mem_of_proj_mem fun r ↦ ?_
  rcases lt_or_ge r p with hrp | hpr
  · have hzero : (hs₁.internalHom hs₂).proj r f = 0 :=
      hs₁.linearMap_ext_of_piece fun a x hx ↦ by
        rw [hs₁.internalHom_proj_apply_apply hs₂ f hx,
          hs₂.proj_eq_zero_of_mem_F_of_lt (hf a x (hs₁.piece_le_F a hx)) (by omega),
          LinearMap.zero_apply]
    rw [hzero]
    exact Submodule.zero_mem _
  · exact ((hs₁.internalHom hs₂).piece_le_F r).trans ((hs₁.internalHom hs₂).F_antitone hpr)
      ((hs₁.internalHom hs₂).proj_mem r f)

end HodgeStructureOn

end TauCeti.Hodge
