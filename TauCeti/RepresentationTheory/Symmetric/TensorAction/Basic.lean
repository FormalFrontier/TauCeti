/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# Permuting tensor factors

This file defines the symmetric-group action on a power of a module by permuting its tensor
factors. Mathlib's `Representation.asAlgebraHom` then extends the action linearly to the group
algebra, which is the action used by Young symmetrizers.

The construction is the first target in Layer 2 of the
[classical-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
and the first construction in Layer 8 of the
[Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md).
It reuses `PiTensorProduct.reindex`; the convention is
`σ • (⨂ₜ i, m i) = ⨂ₜ i, m (σ⁻¹ i)`.

## Main definitions

* `PiTensorProduct.reindexRepresentation` is the permutation action for an arbitrary index type
  and module.
* `permTensorAction` specializes it to `(Fin n → R)^{⊗d}`.
* `permTensorActionAlgHom` is its `Representation.asAlgebraHom` extension to `R[S_d]`.
-/

public section

open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation group of `ι` on the `ι`-indexed tensor power,
acting by reindexing the tensor factors. -/
noncomputable def reindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) where
  toFun σ := (reindex R (fun _ : ι => M) σ).toLinearMap
  map_one' := by
    simpa only [Equiv.Perm.one_def, Module.End.one_eq_id,
      LinearEquiv.refl_toLinearMap] using
      congrArg LinearEquiv.toLinearMap
        (reindex_refl (R := R) (s := fun _ : ι => M))
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap]
    simpa only [Equiv.Perm.mul_def] using
      (reindex_reindex (R := R) (s := fun _ : ι => M) τ σ x).symm

/-- The permutation representation acts by `PiTensorProduct.reindex`. -/
@[simp]
theorem reindexRepresentation_apply (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ = (reindex R (fun _ : ι => M) σ).toLinearMap :=
  (rfl)

/-- Permuting factors commutes with applying the same linear map in every tensor factor. -/
theorem commute_reindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (reindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, reindexRepresentation_apply,
    LinearEquiv.coe_toLinearMap] using
    (map_reindex (f := fun _ : ι => f) σ x).symm

/-- Every element of the group algebra commutes with applying the same linear map in every
tensor factor. -/
theorem commute_reindexRepresentation_asAlgebraHom_map
    (a : MonoidAlgebra R (Equiv.Perm ι)) (f : M →ₗ[R] M) :
    Commute ((reindexRepresentation R M ι).asAlgebraHom a) (map fun _ : ι => f) := by
  induction a using MonoidAlgebra.induction_on with
  | of σ =>
    simpa only [Representation.asAlgebraHom_of] using commute_reindexRepresentation_map R M ι σ f
  | add a b ha hb => simpa only [map_add] using ha.add_left hb
  | smul r a ha => simpa only [map_smul] using ha.smul_left r

/-- The group-algebra action on a pure tensor is the corresponding finite linear combination
of reindexed pure tensors. -/
theorem reindexRepresentation_asAlgebraHom_apply_tprod
    (a : MonoidAlgebra R (Equiv.Perm ι)) (m : ι → M) :
    (reindexRepresentation R M ι).asAlgebraHom a (tprod R m) =
      a.coeff.sum fun σ r => r • tprod R (fun i => m (σ.symm i)) := by
  classical
  simp [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum,
    LinearMap.sum_apply]

end PiTensorProduct

namespace TauCeti

variable (R : Type u) (n d : ℕ)
variable [CommSemiring R]

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` by permutation of tensor factors. -/
noncomputable def permTensorAction :
    Representation R (Equiv.Perm (Fin d)) (⨂[R] _ : Fin d, Fin n → R) :=
  PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d)

/-- The symmetric-group action on `(Fin n → R)^{⊗d}` is the reindexing representation for the
index type `Fin d`. -/
theorem permTensorAction_def :
    permTensorAction R n d = PiTensorProduct.reindexRepresentation R (Fin n → R) (Fin d) :=
  (rfl)

/-- A permutation acts on `(Fin n → R)^{⊗d}` by `PiTensorProduct.reindex`. -/
@[simp]
theorem permTensorAction_apply (σ : Equiv.Perm (Fin d)) :
    permTensorAction R n d σ =
      (PiTensorProduct.reindex R (fun _ : Fin d => Fin n → R) σ).toLinearMap :=
  (rfl)

/-- The group-algebra action of `R[S_d]` on `(Fin n → R)^{⊗d}` induced by factor
permutations. -/
noncomputable def permTensorActionAlgHom :
    MonoidAlgebra R (Equiv.Perm (Fin d)) →ₐ[R]
      Module.End R (⨂[R] _ : Fin d, Fin n → R) :=
  (permTensorAction R n d).asAlgebraHom

/-- The group-algebra action of `R[S_d]` is the linear extension of `permTensorAction`. -/
theorem permTensorActionAlgHom_def :
    permTensorActionAlgHom R n d = (permTensorAction R n d).asAlgebraHom :=
  (rfl)

/-- A single permutation, viewed in the group algebra, acts by `permTensorAction`. -/
theorem permTensorActionAlgHom_of (σ : Equiv.Perm (Fin d)) :
    permTensorActionAlgHom R n d (MonoidAlgebra.of R (Equiv.Perm (Fin d)) σ) =
      permTensorAction R n d σ := by
  rw [permTensorActionAlgHom_def, Representation.asAlgebraHom_of]

/-- The group-algebra action on a pure tensor of `(Fin n → R)^{⊗d}` is the corresponding finite
linear combination of reindexed pure tensors. -/
@[simp]
theorem permTensorActionAlgHom_apply_tprod (a : MonoidAlgebra R (Equiv.Perm (Fin d)))
    (m : Fin d → (Fin n → R)) :
    permTensorActionAlgHom R n d a (PiTensorProduct.tprod R m) =
      a.coeff.sum fun σ r => r • PiTensorProduct.tprod R fun i => m (σ.symm i) := by
  rw [permTensorActionAlgHom_def, permTensorAction_def]
  exact PiTensorProduct.reindexRepresentation_asAlgebraHom_apply_tprod R (Fin n → R) (Fin d) a m

end TauCeti
