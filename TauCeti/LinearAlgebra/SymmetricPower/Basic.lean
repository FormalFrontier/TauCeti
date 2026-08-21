/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Functoriality of symmetric tensor powers, and the symmetrization back into the tensor power

This file equips Mathlib's symmetric tensor power with the linear map induced by a linear map of
the underlying modules. It proves the expected action on pure tensors, identity law, and composition
law. It also records that a symmetric power indexed by a finite type is finitely generated when its
underlying module is.

It then builds the map back, `SymmetricPower.toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M`,
for a finite index type. The **symmetrization** `∑_σ σ` of the tensor power is constant on the
fibres of the quotient map `SymmetricPower.mk`, because reindexing a pure tensor only permutes the
terms of that sum, so it descends to the symmetric power; `toTensorPower` is that descent. It is
the exact counterpart of Mathlib's `exteriorPower.toTensorPower`, and it takes a pure symmetric
tensor to the sum of the pure tensors over all orderings of its factors.

Composing back the other way multiplies by the order of the permutation group: `mk ∘ toTensorPower`
is `(card ι)!`, because each of the `(card ι)!` reorderings becomes the same symmetric tensor
again. So as soon as `(card ι)!` is a unit -- for instance over a `ℚ`-algebra -- the symmetrization
is injective, and it identifies the symmetric power with the image of the symmetrization operator
inside the tensor power. That is the statement a Young symmetrizer of a one-row shape consumes.

## Main definitions

* `SymmetricPower.map` is the map induced on a symmetric tensor power.
* `SymmetricPower.toTensorPower` is the symmetrization, from the symmetric power back into the
  tensor power.

## Main results

* `SymmetricPower.toTensorPower_tprod`: the symmetrization of a pure symmetric tensor is the sum
  of the pure tensors over all orderings of its factors.
* `SymmetricPower.mk_comp_toTensorPower`: composing the symmetrization with the quotient map is
  multiplication by `(card ι)!`.
* `SymmetricPower.toTensorPower_injective`: the symmetrization is injective once `(card ι)!` is a
  unit.
* `SymmetricPower.range_toTensorPower`: its image is the image of the symmetrization operator on
  the tensor power.
* `SymmetricPower.toTensorPower_comp_map`: the symmetrization is natural in the module.

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
theorem map_mk {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
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
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (ι := ι) (g.comp f) = (map (ι := ι) g).comp (map (ι := ι) f) := by
  apply LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M))
  rintro _ ⟨m, rfl⟩
  simp

end CommSemiring

/-! ### The symmetrization back into the tensor power -/

section Symmetrization

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

variable (R ι M) in
/-- The symmetrization operator `∑_σ σ` on the tensor power, permuting the tensor factors. -/
private noncomputable def symmetrizer : (⨂[R] (_ : ι), M) →ₗ[R] ⨂[R] (_ : ι), M :=
  ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap

private theorem symmetrizer_tprod (m : ι → M) :
    symmetrizer R ι M (⨂ₜ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [symmetrizer, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) _ _ fun σ => ?_
  simp

private theorem symmetrizer_rel :
    addConGen (Rel R ι M) ≤ AddCon.ker (symmetrizer R ι M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, symmetrizer_tprod]
      refine Fintype.sum_bijective (e⁻¹ * ·) (Group.mulLeft_bijective _) _ _ fun σ => ?_
      congr 1
      funext i
      simp

variable (R ι M) in
/-- **The symmetrization**, from the symmetric power back into the tensor power: the descent of
the symmetrization operator `∑_σ σ` through the quotient map `SymmetricPower.mk`.

This is the counterpart of Mathlib's `exteriorPower.toTensorPower`. -/
noncomputable def toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M where
  toFun := (addConGen (Rel R ι M)).lift (symmetrizer R ι M).toAddMonoidHom symmetrizer_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (symmetrizer R ι M).map_smul r x

private theorem toTensorPower_mk' (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) = (symmetrizer R ι M).toAddMonoidHom x :=
  (rfl)

@[simp]
theorem toTensorPower_mk (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) =
      ∑ σ : Equiv.Perm ι, PiTensorProduct.reindex R (fun _ : ι => M) σ x := by
  rw [toTensorPower_mk', LinearMap.toAddMonoidHom_coe, symmetrizer, LinearMap.sum_apply]
  rfl

/-- The symmetrization of a pure symmetric tensor is the sum of the pure tensors over all
orderings of its factors. -/
@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk']
  exact symmetrizer_tprod m

private theorem toTensorPower_comp_mk :
    (toTensorPower R ι M) ∘ₗ mk R ι M =
      ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, toTensorPower_mk, LinearMap.sum_apply]
    simp only [LinearEquiv.coe_coe]

/-- The image of the symmetrization is the image of the symmetrization operator `∑_σ σ` on the
tensor power. -/
theorem range_toTensorPower :
    LinearMap.range (toTensorPower R ι M) =
      LinearMap.range (∑ σ : Equiv.Perm ι,
        ((PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap)) := by
  rw [← toTensorPower_comp_mk, LinearMap.range_comp, range_mk, Submodule.map_top]

/-- Symmetrizing and then projecting back to the symmetric power multiplies by `(card ι)!`: the
`(card ι)!` reorderings of a pure tensor all become the same symmetric tensor. -/
@[simp]
theorem mk_comp_toTensorPower :
    (mk R ι M) ∘ₗ (toTensorPower R ι M) =
      (Fintype.card ι).factorial • LinearMap.id (R := R) (M := Sym[R] ι M) := by
  refine LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M)) ?_
  rintro _ ⟨m, rfl⟩
  have h : ∀ σ : Equiv.Perm ι, mk R ι M (⨂ₜ[R] i, m (σ i)) = ⨂ₛ[R] i, m i :=
    fun σ => tprod_equiv σ m
  rw [LinearMap.coe_comp, Function.comp_apply, toTensorPower_tprod, map_sum,
    Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => h σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, LinearMap.smul_apply, LinearMap.id_apply]

/-- The symmetrization is injective as soon as `(card ι)!` is a unit in the base ring, for
instance over a `ℚ`-algebra. -/
theorem toTensorPower_injective (h : IsUnit ((Fintype.card ι).factorial : R)) :
    Function.Injective (toTensorPower R ι M) := by
  obtain ⟨u, hu⟩ := h
  -- Rescaling the quotient map by `u⁻¹` makes it a left inverse of the symmetrization.
  refine LinearMap.injective_of_comp_eq_id _ (((u⁻¹ : Rˣ) : R) • mk R ι M) ?_
  rw [LinearMap.smul_comp, mk_comp_toTensorPower, ← Nat.cast_smul_eq_nsmul R, smul_smul, ← hu,
    u.inv_mul, one_smul]

/-- The symmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type v} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R ι N) ∘ₗ (map (ι := ι) f) =
      (PiTensorProduct.map fun _ : ι => f) ∘ₗ (toTensorPower R ι M) := by
  refine LinearMap.ext_on (span_tprod_eq_top (R := R) (ι := ι) (M := M)) ?_
  rintro _ ⟨m, rfl⟩
  simp

end Symmetrization

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
