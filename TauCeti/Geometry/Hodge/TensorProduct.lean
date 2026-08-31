/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.TensorProduct
public import TauCeti.Geometry.Hodge.Decomposition

/-!
# Tensor products of pure Hodge structures

The tensor product of pure Hodge structures is graded by adding bidegrees.  We construct its
conjugation from the tensor product of the two conjugate-linear involutions and use the internal
Hodge decompositions to package the total grading as a pure Hodge structure.

## Main declarations

* `TauCeti.Hodge.Conjugation.tensorProduct`: the tensor product conjugation.
* `TauCeti.Hodge.HodgeStructureOn.tensorProduct`: the tensor product pure Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.tmul_mem_tensorProduct_piece`: pure tensors have the expected
  total Hodge degree.

The construction supplies the tensor-product companion requested in Layer 0 of the
`HodgeStructures` roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

namespace Conjugation

variable {W₁ : Type u} {W₂ : Type v} [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂]

private def tensorMap (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) :
    W₁ ⊗[ℂ] W₂ →ₛₗ[starRingEnd ℂ] W₁ ⊗[ℂ] W₂ :=
  TensorProduct.map ω₁.toEquiv ω₂.toEquiv

private theorem tensorMap_involutive (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) :
    Function.Involutive (tensorMap ω₁ ω₂) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp [tensorMap]
  | tmul x y =>
      simp only [tensorMap, TensorProduct.map_tmul]
      exact congrArg₂ (fun a b ↦ a ⊗ₜ[ℂ] b) (ω₁.apply_apply x) (ω₂.apply_apply y)
  | add x y hx hy => simp [hx, hy]

/-- The tensor product of two conjugate-linear involutions. -/
def tensorProduct (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂) :
    Conjugation (W₁ ⊗[ℂ] W₂) where
  toEquiv :=
    { toFun := tensorMap ω₁ ω₂
      invFun := tensorMap ω₁ ω₂
      left_inv := tensorMap_involutive ω₁ ω₂
      right_inv := tensorMap_involutive ω₁ ω₂
      map_add' := by simp [tensorMap]
      map_smul' := by simp [tensorMap] }
  involutive := tensorMap_involutive ω₁ ω₂

@[simp]
theorem tensorProduct_toEquiv_tmul (ω₁ : Conjugation W₁) (ω₂ : Conjugation W₂)
    (x : W₁) (y : W₂) :
    (ω₁.tensorProduct ω₂).toEquiv (x ⊗ₜ[ℂ] y) = ω₁.toEquiv x ⊗ₜ[ℂ] ω₂.toEquiv y :=
  by
    -- Expose the private map so Mathlib's pure-tensor computation lemma can fire.
    change tensorMap ω₁ ω₂ (x ⊗ₜ[ℂ] y) = _
    simp [tensorMap]

end Conjugation

namespace HodgeStructureOn

variable {W₁ : Type u} {W₂ : Type v} [AddCommGroup W₁] [Module ℂ W₁]
  [AddCommGroup W₂] [Module ℂ W₂]
variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

private noncomputable def pieceGrading (hs : HodgeStructureOn W₁ ω₁ n₁) : InternalGrading ℂ W₁ where
  piece := hs.piece
  isInternal := hs.isInternal_piece

private theorem map_tensorProduct_piece
    (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p q : ℤ) :
    (Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂) (hs₁.piece p) (hs₂.piece q)).map
        (ω₁.tensorProduct ω₂).toEquiv.toLinearMap =
      Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
        (hs₁.piece (n₁ - p)) (hs₂.piece (n₂ - q)) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.map₂_le.mpr fun x hx y hy ↦ ?_
    -- The preimage condition is exactly the image of a pure tensor under the tensor conjugation.
    change (ω₁.tensorProduct ω₂).toEquiv (x ⊗ₜ[ℂ] y) ∈
      Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
        (hs₁.piece (n₁ - p)) (hs₂.piece (n₂ - q))
    rw [Conjugation.tensorProduct_toEquiv_tmul]
    exact Submodule.apply_mem_map₂ (TensorProduct.mk ℂ W₁ W₂)
      (hs₁.conj_mem_piece hx) (hs₂.conj_mem_piece hy)
  · refine Submodule.map₂_le.mpr fun x hx y hy ↦ ?_
    have hx' : x ∈ (hs₁.piece p).map ω₁.toEquiv.toLinearMap := by
      rw [hs₁.conj_piece]
      exact hx
    have hy' : y ∈ (hs₂.piece q).map ω₂.toEquiv.toLinearMap := by
      rw [hs₂.conj_piece]
      exact hy
    obtain ⟨x', hx₀, hxx⟩ := Submodule.mem_map.1 hx'
    obtain ⟨y', hy₀, hyy⟩ := Submodule.mem_map.1 hy'
    refine Submodule.mem_map.2 ⟨x' ⊗ₜ[ℂ] y',
      Submodule.apply_mem_map₂ (TensorProduct.mk ℂ W₁ W₂) hx₀ hy₀, ?_⟩
    -- Rewrite the bundled semilinear map as its action on a pure tensor.
    change (ω₁.tensorProduct ω₂).toEquiv (x' ⊗ₜ[ℂ] y') = x ⊗ₜ[ℂ] y
    rw [Conjugation.tensorProduct_toEquiv_tmul]
    exact congrArg₂ (fun a b ↦ a ⊗ₜ[ℂ] b)
      (show ω₁.toEquiv x' = x from hxx) (show ω₂.toEquiv y' = y from hyy)

private theorem tensorProduct_piece_map_conj
    (hs₁ : HodgeStructureOn W₁ ω₁ n₁) (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (((pieceGrading hs₁).tensorProduct (pieceGrading hs₂)).piece p).map
        (ω₁.tensorProduct ω₂).toEquiv.toLinearMap =
      ((pieceGrading hs₁).tensorProduct (pieceGrading hs₂)).piece (n₁ + n₂ - p) := by
  rw [InternalGrading.tensorProduct_piece_eq_iSup,
    InternalGrading.tensorProduct_piece_eq_iSup, Submodule.map_iSup]
  simp only [pieceGrading]
  -- Unfolding the private wrapper leaves the two total-degree sums in their explicit form.
  change (⨆ q : ℤ, (Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
      (hs₁.piece q) (hs₂.piece (p - q))).map
        (ω₁.tensorProduct ω₂).toEquiv.toLinearMap) =
    ⨆ r : ℤ, Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
      (hs₁.piece r) (hs₂.piece (n₁ + n₂ - p - r))
  refine le_antisymm (iSup_le fun q ↦ ?_) (iSup_le fun r ↦ ?_)
  · rw [map_tensorProduct_piece hs₁ hs₂]
    apply le_iSup_of_le (n₁ - q)
    -- The selected index is the complementary first degree.
    rw [show n₂ - (p - q) = n₁ + n₂ - p - (n₁ - q) by omega]
  · apply le_iSup_of_le (n₁ - r)
    rw [map_tensorProduct_piece hs₁ hs₂]
    -- The selected index is the inverse reindexing of the first branch.
    rw [show n₁ - (n₁ - r) = r by omega,
      show n₂ - (p - (n₁ - r)) = n₁ + n₂ - p - r by omega]

/-- The tensor product pure Hodge structure, whose weight is the sum of the weights. -/
noncomputable def tensorProduct (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) :
    HodgeStructureOn (W₁ ⊗[ℂ] W₂) (ω₁.tensorProduct ω₂) (n₁ + n₂) :=
  ofDecomposition {
    isInternal := (pieceGrading hs₁).tensorProduct (pieceGrading hs₂) |>.isInternal
    map_conj := tensorProduct_piece_map_conj hs₁ hs₂
    exists_forall_lt_eq_bot := by
      obtain ⟨a₁, ha₁⟩ := hs₁.F_top
      obtain ⟨a₂, ha₂⟩ := hs₂.F_top
      refine ⟨a₁ + a₂, fun p hp ↦ ?_⟩
      rw [InternalGrading.tensorProduct_piece_eq_iSup]
      -- Every total degree below `a₁ + a₂` has a vanishing factor in each summand.
      change (⨆ q : ℤ, Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
          (hs₁.piece q) (hs₂.piece (p - q))) = ⊥
      apply bot_unique
      refine iSup_le fun q ↦ ?_
      by_cases hq : q < a₁
      · rw [hs₁.piece_eq_bot_of_F_eq_top ha₁ hq]
        simp
      · have hq' : a₁ ≤ q := le_of_not_gt hq
        have hpq : p - q < a₂ := by omega
        rw [hs₂.piece_eq_bot_of_F_eq_top ha₂ hpq]
        simp }

theorem tensorProduct_piece_eq_iSup (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.tensorProduct hs₂).piece p =
      ⨆ r : ℤ, Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
        (hs₁.piece r) (hs₂.piece (p - r)) := by
  calc
    (hs₁.tensorProduct hs₂).piece p =
        ((pieceGrading hs₁).tensorProduct (pieceGrading hs₂)).piece p :=
      ofDecomposition_piece _ _
    _ = _ := by
      rw [InternalGrading.tensorProduct_piece_eq_iSup]
      rfl

/-- A pure tensor of vectors in Hodge degrees `p` and `q` has degree `p + q`. -/
theorem tmul_mem_tensorProduct_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {x : W₁} {y : W₂}
    (hx : x ∈ hs₁.piece p) (hy : y ∈ hs₂.piece q) :
    x ⊗ₜ[ℂ] y ∈ (hs₁.tensorProduct hs₂).piece (p + q) := by
  rw [tensorProduct_piece_eq_iSup]
  refine Submodule.mem_iSup_of_mem p ?_
  simpa only [add_sub_cancel_left, TensorProduct.mk_apply] using
    Submodule.apply_mem_map₂ (TensorProduct.mk ℂ W₁ W₂) hx hy

end HodgeStructureOn

end TauCeti.Hodge
