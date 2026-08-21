/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basic

/-!
# The universal property of the symmetric tensor power

A multilinear map `f : Mⁱ → N` that is unchanged by permuting its arguments factors uniquely
through the symmetric tensor power. This file builds that factorization,
`SymmetricPower.lift`, as the descent of `PiTensorProduct.lift f` through the quotient map
`SymmetricPower.mk`: the defining relation of the quotient identifies a pure tensor with each of
its reorderings, and `f` takes the same value on all of them.

Together with `SymmetricPower.ext`, which says that a linear map out of the symmetric power is
determined by its values on pure symmetric tensors, this says that composing with the pure
symmetric tensor `⨂ₛ` is a bijection from the linear maps `Sym[R] ι M →ₗ[R] N` onto the
permutation-invariant multilinear maps `Mⁱ → N`, for every `N`.

## Main definitions

* `SymmetricPower.lift`: the linear map on the symmetric power induced by a permutation-invariant
  multilinear map.

## Main results

* `SymmetricPower.lift_tprod`: `lift f` agrees with `f` on pure symmetric tensors.
* `SymmetricPower.ext`: linear maps out of a symmetric power agreeing on pure symmetric
  tensors are equal.
-/

public section

open scoped TensorProduct

universe u v w

variable {R ι : Type u} {M : Type v} {N : Type w}

namespace SymmetricPower

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (f : MultilinearMap R (fun _ : ι ↦ M) N)

/-- A permutation-invariant multilinear map takes the same value on a pure tensor and on each of
its reorderings, so it is constant on the classes of the defining relation of the symmetric
power. -/
private theorem lift_rel (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) :
    addConGen (Rel R ι M) ≤ AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
      exact (congrFun (congrArg DFunLike.coe (hf e)) m).symm

/-- **The universal property of the symmetric tensor power**: a multilinear map that is unchanged
by permuting its arguments descends to a linear map on the symmetric power. -/
noncomputable def lift (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) : Sym[R] ι M →ₗ[R] N where
  toFun := (addConGen (Rel R ι M)).lift (PiTensorProduct.lift f).toAddMonoidHom (lift_rel f hf)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul r x

/-- The descent of a multilinear map commutes with the quotient map from the tensor power. -/
@[simp]
theorem lift_mk (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (x : ⨂[R] (_ : ι), M) :
    lift f hf (mk R ι M x) = PiTensorProduct.lift f x :=
  AddCon.lift_mk' (lift_rel f hf) x

/-- The descent of a multilinear map agrees with it on pure symmetric tensors. -/
@[simp]
theorem lift_tprod (hf : ∀ e : Equiv.Perm ι, f.domDomCongr e = f) (m : ι → M) :
    lift f hf (⨂ₛ[R] i, m i) = f m := by
  rw [tprod, LinearMap.compMultilinearMap_apply, lift_mk, PiTensorProduct.lift.tprod]

/-- A linear map out of a symmetric power is determined by its values on pure symmetric
tensors. -/
@[ext]
theorem ext {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  refine LinearMap.ext_on (span_tprod_eq_top R ι M) ?_
  rintro _ ⟨m, rfl⟩
  exact hgh m

end SymmetricPower
