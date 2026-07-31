/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Functoriality of symmetric tensor powers

This file equips Mathlib's symmetric tensor power with the linear map induced by a linear map of
the underlying modules. It proves the expected action on pure tensors, identity law, and composition
law. It also records that a symmetric power indexed by a finite type is finitely generated when its
underlying module is.

## Main definitions

* `SymmetricPower.map` is the map induced on a symmetric tensor power.

## References

The quotient construction of `SymmetricPower`, including `SymmetricPower.mk` and
`SymmetricPower.tprod`, is from Kenny Lau's
`Mathlib.LinearAlgebra.TensorPower.Symmetric`.
-/

public section

open scoped TensorProduct

universe u v

variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

private theorem map_rel {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤
      AddCon.ker ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      apply (AddCon.ker_rel _).2
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        PiTensorProduct.map_tprod, tprod, LinearMap.compMultilinearMap_apply,
        Function.comp_apply] using (tprod_equiv (R := R) e (f ∘ m)).symm

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

/-- The map on symmetric powers commutes with the quotient map from the tensor power. -/
@[simp]
theorem map_mk {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  AddCon.lift_mk' (map_rel f) x

/-- The map induced on symmetric powers sends a pure tensor to the tensor of the images. -/
@[simp]
theorem map_tprod {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (m : ι → M) :
    map f (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) := by
  simp only [tprod, LinearMap.compMultilinearMap_apply, map_mk,
    PiTensorProduct.map_tprod]

/-- The map induced by the identity is the identity on the symmetric power. -/
@[simp]
theorem map_id :
    map (ι := ι) (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  apply LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M))
  rintro _ ⟨m, rfl⟩
  simp

/-- Symmetric powers preserve composition of linear maps. -/
@[simp]
theorem map_comp {N : Type*} {P : Type*}
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  apply LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M))
  rintro _ ⟨m, rfl⟩
  simp

end CommSemiring

section CommRing

variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [Finite ι] [Module.Finite R M]

/-- A symmetric power indexed by a finite type is finitely generated when the underlying module
is finitely generated. -/
noncomputable instance finite : Module.Finite R (Sym[R] ι M) :=
  Module.Finite.of_surjective (mk R ι M)
    (LinearMap.range_eq_top.mp (range_mk R ι M))

end CommRing

end SymmetricPower
