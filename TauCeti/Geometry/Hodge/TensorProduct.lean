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

* `TauCeti.Hodge.HodgeStructureOn.tensorProduct`: the tensor product pure Hodge structure.
* `TauCeti.Hodge.HodgeStructureOn.tensorProduct_piece_eq_iSup`: the tensor-product Hodge piece as
  the supremum of products of Hodge pieces of complementary total degree.
* `TauCeti.Hodge.HodgeStructureOn.tensorProduct_F_eq_iSup_piece`: the tensor-product filtration
  as the supremum of products of Hodge pieces.
* `TauCeti.Hodge.HodgeStructureOn.tmul_mem_tensorProduct`: pure tensors have the expected total
  Hodge degree.

The construction supplies the tensor-product companion requested in Layer 0 of the
`HodgeStructures` roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v

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

/-- The tensor-product filtration is the supremum of products of Hodge pieces of total degree at
least `p`. -/
theorem tensorProduct_F_eq_iSup_piece (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.tensorProduct hs₂).F p =
      ⨆ q : ℤ, ⨆ (_ : p ≤ q), ⨆ r : ℤ,
        Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
          (hs₁.piece r) (hs₂.piece (q - r)) := by
  rw [tensorProduct, ofDecomposition_F]
  simp only [InternalGrading.tensorProduct_piece_eq_iSup, pieceGrading]

/-- The tensor-product Hodge piece is the supremum of products of pieces of complementary total
degree. -/
@[simp]
theorem tensorProduct_piece_eq_iSup (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (p : ℤ) :
    (hs₁.tensorProduct hs₂).piece p =
      ⨆ r : ℤ, Submodule.map₂ (TensorProduct.mk ℂ W₁ W₂)
        (hs₁.piece r) (hs₂.piece (p - r)) := by
  rw [tensorProduct, ofDecomposition_piece]
  exact InternalGrading.tensorProduct_piece_eq_iSup (pieceGrading hs₁) (pieceGrading hs₂) p

/-- A pure tensor of vectors in Hodge degrees `p` and `q` has degree `p + q`. -/
theorem tmul_mem_tensorProduct (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) {p q : ℤ} {x : W₁} {y : W₂}
    (hx : x ∈ hs₁.piece p) (hy : y ∈ hs₂.piece q) :
    x ⊗ₜ[ℂ] y ∈ (hs₁.tensorProduct hs₂).piece (p + q) := by
  rw [tensorProduct, ofDecomposition_piece]
  exact InternalGrading.tmul_mem_tensorProduct (pieceGrading hs₁) (pieceGrading hs₂) hx hy

end HodgeStructureOn

end TauCeti.Hodge
