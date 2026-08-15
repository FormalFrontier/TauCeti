/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.Bialgebra.GroupLike.Map
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Scalar automorphisms on group-like elements of base-changed bialgebras

For a commutative semiring extension `L/K` and a `K`-bialgebra `A`, the scalar-factor action on
`L ⊗[K] A` preserves the counit and comultiplication equations defining group-like elements. It
therefore induces actions on the group-like elements and on their additive form.

## Main declarations

* `TauCeti.ScalarAut.isGroupLikeElem_smul`: scalar automorphisms preserve group-like elements.
* `TauCeti.ScalarAut.map_smul`: scalar extension of a bialgebra map is equivariant.
* `TauCeti.ScalarAut.groupLike_map_smul`: the induced map on group-like elements is equivariant.
* `TauCeti.ScalarAut.instGroupLikeDistribMulAction`: the induced action on group-like elements.
* `TauCeti.ScalarAut.instAdditiveDistribMulAction`: the transported additive action.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti

universe u v w

namespace ScalarAut

variable {K : Type u} {L : Type v} {A : Type w}
variable [CommSemiring K] [CommSemiring L] [Algebra K L]
variable [Semiring A] [Bialgebra K A]

/-- The counit is equivariant for the semilinear scalar action. -/
theorem counit_smul (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    counit (R := L) (σ • x) = σ (counit (R := L) x) := by
  induction x with
  | zero => rw [smul_zero, map_zero, map_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
  | tmul a x => simp

/-- Comultiplication is equivariant for the semilinear scalar action. -/
theorem comul_smul (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    comul (σ • x) =
      TensorProduct.map (semilinearMap (A := A) σ)
        (semilinearMap (A := A) σ) (comul x) := by
  induction x with
  | zero => rw [smul_zero, map_zero, map_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
  | tmul a x =>
      rw [smul_tmul, TensorProduct.comul_tmul, TensorProduct.comul_tmul]
      induction comul (R := K) x with
      | zero => simp only [tmul_zero, map_zero]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul x₁ x₂ =>
          rw [CommSemiring.comul_apply L a, CommSemiring.comul_apply L (σ a)]
          simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            semilinearMap_apply, smul_tmul, map_one]

/-- Applying a scalar automorphism preserves the group-like equations. -/
theorem isGroupLikeElem_smul (σ : L ≃ₐ[K] L) {x : L ⊗[K] A}
    (hx : IsGroupLikeElem L x) : IsGroupLikeElem L (σ • x) where
  counit_eq_one := by rw [counit_smul, hx.counit_eq_one, map_one]
  comul_eq_tmul_self := by
    rw [comul_smul, hx.comul_eq_tmul_self, TensorProduct.map_tmul]
    simp only [semilinearMap_apply]

/-- Scalar extension of a bialgebra morphism commutes with the scalar-factor action. -/
theorem map_smul {B : Type*} [Semiring B] [Bialgebra K B] (f : A →ₐc[K] B)
    (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    Bialgebra.TensorProduct.map (BialgHom.id L L) f (σ • x) =
      σ • Bialgebra.TensorProduct.map (BialgHom.id L L) f x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul a x =>
      rw [smul_tmul, Bialgebra.TensorProduct.map_tmul,
        Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply, BialgHom.id_apply, smul_tmul]

/-- Scalar automorphisms act multiplicatively on group-like elements. -/
noncomputable instance instGroupLikeDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (_root_.GroupLike L (L ⊗[K] A)) where
  smul σ x := ⟨σ • x.val, isGroupLikeElem_smul (A := A) σ x.isGroupLikeElem_val⟩
  -- The action is defined inline, so its laws reduce to the corresponding laws on values.
  one_smul x := by
    apply _root_.GroupLike.val_injective
    change (1 : L ≃ₐ[K] L) • x.val = x.val
    exact one_smul _ x.val
  mul_smul σ τ x := by
    apply _root_.GroupLike.val_injective
    change (σ * τ) • x.val = σ • τ • x.val
    exact mul_smul σ τ x.val
  smul_one σ := by
    apply _root_.GroupLike.val_injective
    change σ • (1 : L ⊗[K] A) = 1
    rw [smul_def, map_one]
  smul_mul σ x y := by
    apply _root_.GroupLike.val_injective
    change σ • (x.val * y.val) = σ • x.val * σ • y.val
    simp only [smul_def, map_mul]

/-- The value of the scalar action on a group-like element is the scalar-factor action. -/
@[simp]
theorem val_smul (σ : L ≃ₐ[K] L) (x : _root_.GroupLike L (L ⊗[K] A)) :
    (σ • x).val = σ • x.val :=
  rfl

/-- The map on group-like elements induced by scalar extension is equivariant for scalar
automorphisms. -/
@[simp]
theorem groupLike_map_smul {B : Type*} [Semiring B] [Bialgebra K B] (f : A →ₐc[K] B)
    (σ : L ≃ₐ[K] L) (x : _root_.GroupLike L (L ⊗[K] A)) :
    GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) f) (σ • x) =
      σ • GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) f) x := by
  apply _root_.GroupLike.val_injective
  simp only [GroupLike.val_map, val_smul]
  exact map_smul f σ x.val

/-- The scalar action transported to the additive form of the group-like monoid. -/
noncomputable instance instAdditiveDistribMulAction :
    DistribMulAction (L ≃ₐ[K] L) (Additive (_root_.GroupLike L (L ⊗[K] A))) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul _ x.toMul)
  mul_smul σ τ x := congrArg Additive.ofMul (mul_smul σ τ x.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ)
  smul_add σ x y := congrArg Additive.ofMul (smul_mul' σ x.toMul y.toMul)

/-- The additive scalar action is transported from the group-like action. -/
@[simp]
theorem smul_ofMul (σ : L ≃ₐ[K] L) (x : _root_.GroupLike L (L ⊗[K] A)) :
    σ • Additive.ofMul x = Additive.ofMul (σ • x) :=
  rfl

/-- Passing back to the multiplicative group-like element commutes with the scalar action. -/
@[simp]
theorem toMul_smul (σ : L ≃ₐ[K] L)
    (x : Additive (_root_.GroupLike L (L ⊗[K] A))) :
    (σ • x).toMul = σ • x.toMul :=
  rfl

end ScalarAut

end TauCeti
