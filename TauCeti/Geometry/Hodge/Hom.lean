/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Basis
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

Only the source `W₁` must be finite-dimensional (as required by the tensor--Hom equivalence); no
lattice or further finiteness is imposed, and the target `W₂` is arbitrary.

## Main declarations

* `TauCeti.Hodge.HodgeStructureOn.hom`: the internal Hom pure Hodge structure, transported from
  the dual tensor product.
* `TauCeti.Hodge.HodgeStructureOn.hom_F`, `…hom_conjF`, `…hom_piece`: the internal-Hom filtration,
  conjugate filtration, and pieces as comaps under the inverse tensor--Hom equivalence.
* `TauCeti.Hodge.HodgeStructureOn.hom_piece_apply_mem`: a homogeneous map sends each source
  component to the target component with the expected degree shift.
* `TauCeti.Hodge.HodgeStructureOn.mem_hom_piece_iff`: membership in an internal-Hom piece is
  exactly the degree-shifting property on all Hodge components.
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

/-- A linear map lies in the degree-`p` internal-Hom piece if and only if it sends each
source component of degree `a` into the target component of degree `a + p`. -/
private theorem projCoord_mem_dual_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (a : ℤ) (k : Fin (Module.finrank ℂ ↥(hs₁.piece a))) :
    ((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
      (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) ∈ (hs₁.dual).piece (-a) := by
  rw [hs₁.dual_piece, Submodule.mem_dualAnnihilator]
  intro x hx
  have hFker : hs₁.F (1 - -a) ≤ LinearMap.ker
      (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
        (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
          hs₁.decomposition.toLinearMap)) := by
    rw [hs₁.F_eq_iSup_piece]
    refine iSup_le fun q => iSup_le fun hq => ?_
    intro y hy
    rw [LinearMap.mem_ker]
    have hqa : q ≠ a := by omega
    have hproj0 := hs₁.proj_apply_eq_zero_of_mem_of_ne (p := a) (q := q) hy hqa
    have hcoe : ((((DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) y : ↥(hs₁.piece a))) : W₁) =
        hs₁.proj a y := by
      rw [hs₁.proj_apply]
      rfl
    have h0 : (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) y = 0 :=
      Submodule.coe_eq_zero.mp (hcoe.trans hproj0)
    simp [LinearMap.comp_apply, h0]
  have hCker : hs₁.conjF (n₁ + 1 + -a) ≤ LinearMap.ker
      (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
        (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
          hs₁.decomposition.toLinearMap)) := by
    rw [hs₁.conjF_eq_iSup_piece]
    refine iSup_le fun q => iSup_le fun hq => ?_
    intro y hy
    rw [LinearMap.mem_ker]
    have hqa : q ≠ a := by omega
    have hproj0 := hs₁.proj_apply_eq_zero_of_mem_of_ne (p := a) (q := q) hy hqa
    have hcoe : ((((DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) y : ↥(hs₁.piece a))) : W₁) =
        hs₁.proj a y := by
      rw [hs₁.proj_apply]
      rfl
    have h0 : (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) y = 0 :=
      Submodule.coe_eq_zero.mp (hcoe.trans hproj0)
    simp [LinearMap.comp_apply, h0]
  have hle : hs₁.F (1 - -a) ⊔ hs₁.conjF (n₁ + 1 + -a) ≤ LinearMap.ker
      (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
        (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
          hs₁.decomposition.toLinearMap)) :=
    sup_le hFker hCker
  have hxker : x ∈ LinearMap.ker
      (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
        (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
          hs₁.decomposition.toLinearMap)) := hle hx
  rwa [LinearMap.mem_ker] at hxker

/-- A projected map expands along the Hodge-adapted basis of the source component as a sum of
rank-one maps built from the coordinate functionals. -/
private theorem compProj_expand (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (f : W₁ →ₗ[ℂ] W₂) (a : ℤ) :
    f ∘ₗ hs₁.proj a =
      ∑ k, (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k).comp
        (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
          hs₁.decomposition.toLinearMap)).smulRight
        (f ((((Module.finBasis ℂ ↥(hs₁.piece a)) k : ↥(hs₁.piece a))) : W₁)) := by
  classical
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hlink : (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
      hs₁.decomposition.toLinearMap) x = hs₁.decomposition x a := rfl
  have hsr := (Module.finBasis ℂ ↥(hs₁.piece a)).sum_repr
      ((DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
        hs₁.decomposition.toLinearMap) x)
  have hsum : (DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
      hs₁.decomposition.toLinearMap) x = ∑ k,
        (((Module.finBasis ℂ ↥(hs₁.piece a)).dualBasis k)
          ((DirectSum.component ℂ ℤ (fun q => ↥(hs₁.piece q)) a ∘ₗ
            hs₁.decomposition.toLinearMap) x)) •
        (Module.finBasis ℂ ↥(hs₁.piece a)) k := by
    conv_lhs => rw [← hsr]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Module.Basis.dualBasis_apply]
  rw [hs₁.proj_apply, ← hlink, hsum, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, Submodule.coe_smul, map_smul]

omit [FiniteDimensional ℂ W₁] in
/-- A linear map is the finite sum of its compositions with the source Hodge projections. -/
private theorem sum_compProj (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (f : W₁ →ₗ[ℂ] W₂) :
    f = ∑ a ∈ hs₁.finite_setOf_piece_ne_bot.toFinset, f ∘ₗ hs₁.proj a := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  have hbase : x = ∑ j ∈ (hs₁.decomposition x).support, hs₁.proj j x := by
    conv_lhs => rw [← hs₁.decomposition.symm_apply_apply x,
      hs₁.decomposition_symm_apply, DirectSum.coeLinearMap_eq_dfinsuppSum,
      DFinsupp.sum]
    simp only [hs₁.proj_apply]
  have hsupp : (hs₁.decomposition x).support ⊆ hs₁.finite_setOf_piece_ne_bot.toFinset := by
    intro j hj
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro hbot
    let : Subsingleton ↥(hs₁.piece j) := by rw [hbot]; infer_instance
    have hj0 : hs₁.decomposition x j = 0 := Subsingleton.elim _ _
    exact (DFinsupp.mem_support_iff.mp hj) hj0
  have hx : x = ∑ a ∈ hs₁.finite_setOf_piece_ne_bot.toFinset, hs₁.proj a x := by
    conv_lhs => rw [hbase]
    refine Finset.sum_subset hsupp ?_
    intro j _ hnj
    have hj0 : hs₁.decomposition x j = 0 := DFinsupp.notMem_support_iff.mp hnj
    simp [hs₁.proj_apply, hj0]
  conv_lhs => rw [hx, map_sum]

/-- A linear map lies in the degree-`p` internal-Hom piece if and only if it sends each
source component of degree `a` into the target component of degree `a + p`. -/
@[simp] theorem mem_hom_piece_iff (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p : ℤ} {f : W₁ →ₗ[ℂ] W₂} :
    f ∈ (hs₁.hom hs₂).piece p ↔
      ∀ (a : ℤ) (x : W₁), x ∈ hs₁.piece a → f x ∈ hs₂.piece (a + p) := by
  constructor
  · intro hf a x hx
    exact hs₁.hom_piece_apply_mem hs₂ hf hx
  · intro h
    classical
    have hmem_each : ∀ a ∈ hs₁.finite_setOf_piece_ne_bot.toFinset,
        f ∘ₗ hs₁.proj a ∈ (hs₁.hom hs₂).piece p := by
      intro a _
      rw [hs₁.compProj_expand f a]
      refine Submodule.sum_mem _ fun k _ => ?_
      have hdeg : -a + (a + p) = p := by ring
      rw [← hdeg]
      refine hs₁.smulRight_mem_hom hs₂ (hs₁.projCoord_mem_dual_piece a k) ?_
      exact h a _ ((Module.finBasis ℂ ↥(hs₁.piece a)) k).2
    rw [hs₁.sum_compProj f]
    exact Submodule.sum_mem _ fun a ha => hmem_each a ha

end Finite

end HodgeStructureOn

end TauCeti.Hodge
