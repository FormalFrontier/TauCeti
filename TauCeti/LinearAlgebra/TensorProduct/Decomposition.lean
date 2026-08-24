/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Flat.Domain

/-!
# Tensor products of internal decompositions

If `M` and `N` are internal direct sums of families of submodules `A i` and `B j`, then
`M ⊗ N` is the internal direct sum of the images `A i ⊗ B j`. Mathlib supplies the external
tensor-product/direct-sum equivalence and the decomposition obtained from one decomposed factor;
this file records the symmetric two-factor consequence for internal decompositions.

## Main result

* `DirectSum.IsInternal.tensorProduct`: the images of the tensor products of the summands form an
  internal decomposition of the ambient tensor product.
-/

public section

open TensorProduct

namespace DirectSum.IsInternal

universe u v w x y

variable {K : Type u} [Field K]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]
variable {ι : Type x} {κ : Type y} [DecidableEq ι] [DecidableEq κ]
variable (A : ι → Submodule K M) (B : κ → Submodule K N)

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free

/-- The tensor product of two submodules is linearly equivalent to its image in the tensor product
of the ambient modules. Over a field the canonical map is injective. -/
private noncomputable def summandEquiv (i : ι) (j : κ) :
    A i ⊗[K] B j ≃ₗ[K] Submodule.map₂ (TensorProduct.mk K M N) (A i) (B j) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict
      (Submodule.map₂ (TensorProduct.mk K M N) (A i) (B j))
      (TensorProduct.mapIncl (A i) (B j)) fun z ↦ by
        rw [← TensorProduct.range_mapIncl]
        exact ⟨z, rfl⟩)
    ⟨fun x y h ↦ Module.Flat.tensorProduct_mapIncl_injective_of_right (A i) (B j)
        (congrArg Subtype.val h), fun z ↦ by
      have hz : (z : M ⊗[K] N) ∈ LinearMap.range (TensorProduct.mapIncl (A i) (B j)) := by
        simpa only [TensorProduct.range_mapIncl] using z.property
      obtain ⟨x, hx⟩ := hz
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx⟩

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] private theorem coe_summandEquiv (i : ι) (j : κ) (x : A i ⊗[K] B j) :
    ((summandEquiv A B i j x :
      Submodule.map₂ (TensorProduct.mk K M N) (A i) (B j)) : M ⊗[K] N) =
      TensorProduct.mapIncl (A i) (B j) x := rfl

/-- **Tensor products of internal decompositions are internal.** If `A` and `B` internally
decompose `M` and `N`, the images of `A i ⊗ B j` under the canonical map internally decompose
`M ⊗ N`.

The summand is written with `Submodule.map₂` because this is the canonical submodule of the
ambient tensor product spanned by pure tensors from the two factors. -/
theorem tensorProduct (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B) :
    DirectSum.IsInternal fun p : ι × κ ↦
      Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2) := by
  classical
  let _ := hA.chooseDecomposition
  let _ := hB.chooseDecomposition
  let E : M ⊗[K] N ≃ₗ[K]
      ⨁ p : ι × κ, Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2) :=
    TensorProduct.congr (DirectSum.decomposeLinearEquiv A) (DirectSum.decomposeLinearEquiv B) ≪≫ₗ
      TensorProduct.directSum K K (fun i ↦ A i) (fun j ↦ B j) ≪≫ₗ
      DirectSum.congrLinearEquiv (fun p ↦ summandEquiv A B p.1 p.2)
  have hE (i : ι) (j : κ) (x : A i ⊗[K] B j) :
      E (((summandEquiv A B i j x :
        Submodule.map₂ (TensorProduct.mk K M N) (A i) (B j)) : M ⊗[K] N)) =
        DirectSum.lof K (ι × κ)
          (fun p ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)) (i, j)
          (summandEquiv A B i j x) := by
    rw [coe_summandEquiv]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, summandEquiv, DirectSum.coe_congrLinearEquiv]
    | add a b ha hb => simp [ha, hb]
  have hcoe :
      DirectSum.coeLinearMap
          (fun p : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)) =
        E.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    rintro ⟨i, j⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := (summandEquiv A B i j).surjective z
    simp only [LinearMap.comp_apply]
    rw [DirectSum.coeLinearMap_lof]
    apply E.injective
    simpa using hE i j x
  change Function.Bijective
    (DirectSum.coeLinearMap
      (fun p : ι × κ ↦ Submodule.map₂ (TensorProduct.mk K M N) (A p.1) (B p.2)))
  rw [hcoe]
  exact E.symm.bijective

end DirectSum.IsInternal
