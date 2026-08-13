/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Scalar automorphisms on base-changed bialgebras

For a commutative semiring extension `L/k` and a `k`-bialgebra `A`, an automorphism `σ` of
`L/k` acts on `L ⊗[k] A` through the scalar factor:

```text
σ • (a ⊗ x) = σ(a) ⊗ x.
```

This semilinear ring action preserves the counit and comultiplication equations defining
group-like elements. It therefore induces actions on the group-like elements and on their
additive form.

## Main declarations

* `TauCeti.GaloisScalar.map`: the algebra map applying an automorphism to the scalar factor.
* `TauCeti.GaloisScalar.semilinearMap`: its semilinear-map packaging over `L`.
* `TauCeti.GaloisScalar.isGroupLikeElem_map`: scalar automorphisms preserve group-like elements.
* `TauCeti.GaloisScalar.instScalarMulSemiringAction`: the action on the scalar extension.
* `TauCeti.GaloisScalar.instGroupLikeDistribMulAction`: the induced action on group-like elements.
* `TauCeti.GaloisScalar.instAdditiveDistribMulAction`: the transported additive action.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti

universe u v w

namespace GaloisScalar

variable {k : Type u} {L : Type v} {A : Type w}
variable [CommSemiring k] [CommSemiring L] [Algebra k L]
variable [Semiring A] [Bialgebra k A]

/-- Apply an automorphism of `L/k` to the scalar factor of `L ⊗[k] A`. -/
noncomputable def map (σ : L ≃ₐ[k] L) : L ⊗[k] A →ₐ[k] L ⊗[k] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

/-- The scalar map acts on pure tensors through the first factor. -/
@[simp]
theorem map_tmul (σ : L ≃ₐ[k] L) (a : L) (x : A) :
    map (A := A) σ (a ⊗ₜ[k] x) = σ.toAlgHom a ⊗ₜ[k] x := by
  simp [map]

/-- The identity scalar automorphism acts trivially. -/
@[simp]
theorem map_one_apply (x : L ⊗[k] A) : map (A := A) 1 x = x := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x => simp

/-- Scalar maps compose according to multiplication of scalar automorphisms. -/
theorem map_mul_apply (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    map (A := A) (σ * τ) x = map (A := A) σ (map (A := A) τ x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x => simp

/-- The scalar-factor map is semilinear for the corresponding automorphism of `L`. -/
theorem map_smul (σ : L ≃ₐ[k] L) (a : L) (x : L ⊗[k] A) :
    map (A := A) σ (a • x) = σ.toAlgHom a • map (A := A) σ x := by
  simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]

/-- The scalar action as a semilinear map over `L`. -/
noncomputable def semilinearMap (σ : L ≃ₐ[k] L) :
    L ⊗[k] A →ₛₗ[σ.toRingHom] L ⊗[k] A where
  toFun := map (A := A) σ
  map_add' := map_add (map (A := A) σ)
  map_smul' := map_smul (A := A) σ

/-- The semilinear scalar map agrees pointwise with `map`. -/
@[simp]
theorem semilinearMap_apply (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    semilinearMap (A := A) σ x = map (A := A) σ x :=
  (rfl)

/-- The counit is equivariant for the semilinear scalar action. -/
theorem counit_map (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    counit (R := L) (map (A := A) σ x) = σ.toAlgHom (counit (R := L) x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a x => simp

/-- Comultiplication is equivariant for the semilinear scalar action. -/
theorem comul_map (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    comul (map (A := A) σ x) =
      TensorProduct.map (semilinearMap (A := A) σ)
        (semilinearMap (A := A) σ) (comul x) := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      rw [map_tmul, TensorProduct.comul_tmul, TensorProduct.comul_tmul]
      induction comul (R := k) x with
      | zero => simp only [tmul_zero, map_zero]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul x₁ x₂ =>
          rw [CommSemiring.comul_apply L a, CommSemiring.comul_apply L (σ.toAlgHom a)]
          simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            semilinearMap_apply, map_tmul, map_one]

/-- Applying a scalar automorphism preserves the group-like equations. -/
theorem isGroupLikeElem_map (σ : L ≃ₐ[k] L) {x : L ⊗[k] A}
    (hx : IsGroupLikeElem L x) : IsGroupLikeElem L (map (A := A) σ x) where
  counit_eq_one := by rw [counit_map, hx.counit_eq_one, map_one]
  comul_eq_tmul_self := by
    rw [comul_map, hx.comul_eq_tmul_self, TensorProduct.map_tmul]
    simp only [semilinearMap_apply]

/-- Scalar automorphisms act on a scalar-extended bialgebra by semilinear ring automorphisms. -/
noncomputable instance instScalarMulSemiringAction :
    MulSemiringAction (L ≃ₐ[k] L) (L ⊗[k] A) where
  smul σ x := map (A := A) σ x
  one_smul := map_one_apply (A := A)
  mul_smul := map_mul_apply (A := A)
  smul_zero σ := map_zero (map (A := A) σ)
  smul_add σ := map_add (map (A := A) σ)
  smul_one σ := map_one (map (A := A) σ)
  smul_mul σ := map_mul (map (A := A) σ)

/-- Scalar multiplication on the base change is the scalar-factor map. -/
@[simp]
theorem smul_def (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    σ • x = map (A := A) σ x :=
  (rfl)

/-- Scalar multiplication on a pure tensor acts through the first factor. -/
theorem smul_tmul (σ : L ≃ₐ[k] L) (a : L) (x : A) :
    σ • (a ⊗ₜ[k] x) = σ.toAlgHom a ⊗ₜ[k] x := by
  rw [smul_def, map_tmul]

/-- Scalar automorphisms act multiplicatively on group-like elements. -/
noncomputable instance instGroupLikeDistribMulAction :
    MulDistribMulAction (L ≃ₐ[k] L) (_root_.GroupLike L (L ⊗[k] A)) where
  smul σ x := ⟨map (A := A) σ x.val, isGroupLikeElem_map (A := A) σ x.isGroupLikeElem_val⟩
  one_smul x := _root_.GroupLike.val_injective (map_one_apply (A := A) x.val)
  mul_smul σ τ x := _root_.GroupLike.val_injective (map_mul_apply (A := A) σ τ x.val)
  smul_one σ := _root_.GroupLike.val_injective (map_one (map (A := A) σ))
  smul_mul σ x y := _root_.GroupLike.val_injective (map_mul (map (A := A) σ) x.val y.val)

/-- The value of the scalar action on a group-like element is the scalar-factor map. -/
@[simp]
theorem val_smul (σ : L ≃ₐ[k] L) (x : _root_.GroupLike L (L ⊗[k] A)) :
    (σ • x).val = map (A := A) σ x.val :=
  (rfl)

/-- The scalar action transported to the additive form of the group-like monoid. -/
noncomputable instance instAdditiveDistribMulAction :
    DistribMulAction (L ≃ₐ[k] L) (Additive (_root_.GroupLike L (L ⊗[k] A))) where
  smul σ x := Additive.ofMul (σ • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul _ x.toMul)
  mul_smul σ τ x := congrArg Additive.ofMul (mul_smul σ τ x.toMul)
  smul_zero σ := congrArg Additive.ofMul (smul_one σ)
  smul_add σ x y := congrArg Additive.ofMul (smul_mul' σ x.toMul y.toMul)

/-- The additive scalar action is transported from the group-like action. -/
@[simp]
theorem smul_ofMul (σ : L ≃ₐ[k] L) (x : _root_.GroupLike L (L ⊗[k] A)) :
    σ • Additive.ofMul x = Additive.ofMul (σ • x) :=
  (rfl)

/-- Passing back to the multiplicative group-like element commutes with the scalar action. -/
@[simp]
theorem toMul_smul (σ : L ≃ₐ[k] L)
    (x : Additive (_root_.GroupLike L (L ⊗[k] A))) :
    (σ • x).toMul = σ • x.toMul :=
  (rfl)

end GaloisScalar

end TauCeti
