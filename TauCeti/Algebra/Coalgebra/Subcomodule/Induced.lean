/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# The induced comodule on a subcomodule

This file equips a subcomodule with its inherited right-comodule structure.  The definition is
made under the flatness hypothesis on the coalgebra: flatness makes
`N ⊗ C → M ⊗ C` injective for the subtype map of a subcomodule `N ≤ M`, so the ambient
coaction has a unique lift to `N ⊗ C`.

This is Layer 1 infrastructure for the reductive-groups roadmap target "Comodules over a
coalgebra/Hopf algebra": finite-dimensional subcomodules and categorical kernels need
subcomodules to be usable as comodules in their own right.

## Main declarations

* `TauCeti.Subcomodule.inducedCoact`: the coaction on the subtype of a subcomodule.
* `TauCeti.Subcomodule.instComodule`: the induced right-comodule structure.
* `TauCeti.Subcomodule.subtype`: the inclusion as a comodule morphism.

## References

This is the standard inherited comodule structure on a subcomodule; see Sweedler,
*Hopf Algebras*, Chapter 2.  The formalization uses Mathlib's
`LinearMap.codRestrictOfInjective` and flatness preservation of injective maps under tensor
product.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable (N : Subcomodule R C M)

private theorem subtype_rTensor_injective :
    Function.Injective ((SMulMemClass.subtype N).rTensor C) :=
  Module.Flat.rTensor_preserves_injective_linearMap (SMulMemClass.subtype N)
    Subtype.val_injective

omit [Module.Flat R C] in
/-- The ambient coaction of an element of a subcomodule lies in the range of the tensored
inclusion `N ⊗ C → M ⊗ C`. -/
private theorem coact_mem_range (n : N) :
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N)) n ∈
      LinearMap.range ((SMulMemClass.subtype N).rTensor C) := by
  rw [LinearMap.comp_apply, LinearMap.rTensor_def, SMulMemClass.subtype_apply]
  exact N.coact_mem n.2

/-- The coaction induced on the subtype of a subcomodule.

It is the unique lift of the ambient coaction along `N ⊗ C → M ⊗ C`. -/
noncomputable def inducedCoact : N →ₗ[R] N ⊗[R] C :=
  LinearMap.codRestrictOfInjective
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N))
    ((SMulMemClass.subtype N).rTensor C) (subtype_rTensor_injective N) (coact_mem_range N)

/-- The induced coaction, included back into `M ⊗ C`, is the ambient coaction. -/
@[simp]
theorem subtype_rTensor_inducedCoact (n : N) :
    (SMulMemClass.subtype N).rTensor C (N.inducedCoact n) =
      Comodule.coact (R := R) (C := C) (M := M) n :=
  LinearMap.codRestrictOfInjective_comp_apply
    ((Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N))
    ((SMulMemClass.subtype N).rTensor C) (subtype_rTensor_injective N) (coact_mem_range N) n

/-- The induced coaction included into the ambient tensor product, as an equality of linear maps. -/
@[simp]
theorem subtype_rTensor_comp_inducedCoact : (SMulMemClass.subtype N).rTensor C ∘ₗ N.inducedCoact =
      (Comodule.coact (R := R) (C := C) (M := M)).comp (SMulMemClass.subtype N) := by
  ext n
  exact subtype_rTensor_inducedCoact N n

private theorem subtype_rTensor_tensor_injective :
    Function.Injective (((SMulMemClass.subtype N).rTensor C).rTensor C) :=
  Module.Flat.rTensor_preserves_injective_linearMap
    ((SMulMemClass.subtype N).rTensor C) (subtype_rTensor_injective N)

omit [Module.Flat R C] in
private theorem subtype_rTensor_R_injective :
    Function.Injective ((SMulMemClass.subtype N).rTensor R) :=
  Module.Flat.rTensor_preserves_injective_linearMap (SMulMemClass.subtype N)
    Subtype.val_injective

private theorem map_rTensor_inducedCoact (t : N ⊗[R] C) :
    TensorProduct.map ((SMulMemClass.subtype N).rTensor C) (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C) t) =
      TensorProduct.map (Comodule.coact (R := R) (C := C) (M := M))
        (LinearMap.id : C →ₗ[R] C)
        (TensorProduct.map (SMulMemClass.subtype N) (LinearMap.id : C →ₗ[R] C) t) := by
  rw [TensorProduct.map_map, TensorProduct.map_map, subtype_rTensor_comp_inducedCoact]

omit [Module.Flat R C] in
private theorem assoc_symm_tmul_natural (n : N) (z : C ⊗[R] C) :
    (TensorProduct.assoc R M C C).symm (SMulMemClass.subtype N n ⊗ₜ[R] z) =
      ((SMulMemClass.subtype N).rTensor C).rTensor C
        ((TensorProduct.assoc R N C C).symm (n ⊗ₜ[R] z)) := by
  rw [LinearMap.rTensor_def, LinearMap.rTensor_def, TensorProduct.map_map_assoc_symm]
  simp

omit [Module.Flat R C] in
private theorem assoc_symm_lTensor_comul_natural (t : N ⊗[R] C) : (TensorProduct.assoc R M C C).symm
        (Coalgebra.comul.lTensor M ((SMulMemClass.subtype N).rTensor C t)) =
      ((SMulMemClass.subtype N).rTensor C).rTensor C
        ((TensorProduct.assoc R N C C).symm (Coalgebra.comul.lTensor N t)) := by
  induction t with
  | zero => simp
  | tmul n c =>
      simp only [LinearMap.rTensor_def, LinearMap.lTensor_def, TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq]
      exact assoc_symm_tmul_natural N n (Coalgebra.comul (R := R) c)
  | add x y hx hy => simp [hx, hy]

omit [Module.Flat R C] in
private theorem lTensor_counit_natural (t : N ⊗[R] C) :
    (SMulMemClass.subtype N).rTensor R (Coalgebra.counit.lTensor N t) =
      Coalgebra.counit.lTensor M ((SMulMemClass.subtype N).rTensor C t) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
    LinearMap.lTensor_comp_rTensor]

/-- The subtype of a subcomodule carries the inherited right-comodule structure. -/
noncomputable instance instComodule : Comodule R C N where
  coact := N.inducedCoact
  coassoc := by
    ext n
    apply (subtype_rTensor_tensor_injective N).comp
      (TensorProduct.assoc R N C C).symm.injective
    simp only [LinearMap.comp_apply, LinearMap.rTensor_def]
    calc
      ((SMulMemClass.subtype N).rTensor C).rTensor C
          ((TensorProduct.assoc R N C C).symm
            (TensorProduct.assoc R N C C
              (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C)
                (N.inducedCoact n)))) =
          TensorProduct.map ((SMulMemClass.subtype N).rTensor C) (LinearMap.id : C →ₗ[R] C)
            (TensorProduct.map N.inducedCoact (LinearMap.id : C →ₗ[R] C)
              (N.inducedCoact n)) := by
            rw [LinearEquiv.symm_apply_apply, LinearMap.rTensor_def]
      _ =
          (Comodule.coact (R := R) (C := C) (M := M)).rTensor C
            (Comodule.coact (R := R) (C := C) (M := M) n) := by
            rw [map_rTensor_inducedCoact]
            simp only [← LinearMap.rTensor_def, subtype_rTensor_inducedCoact]
      _ =
          (TensorProduct.assoc R M C C).symm
            (Coalgebra.comul.lTensor M
              (Comodule.coact (R := R) (C := C) (M := M) n)) := by
            apply (TensorProduct.assoc R M C C).injective
            simp [Comodule.coassoc_apply (R := R) (C := C) (M := M)]
      _ =
          ((SMulMemClass.subtype N).rTensor C).rTensor C
            ((TensorProduct.assoc R N C C).symm
              (Coalgebra.comul.lTensor N (N.inducedCoact n))) := by
            rw [← assoc_symm_lTensor_comul_natural]
            rw [subtype_rTensor_inducedCoact]
  lTensor_counit_comp_coact := by
    ext n
    apply subtype_rTensor_R_injective N
    simp only [LinearMap.comp_apply]
    calc
      (SMulMemClass.subtype N).rTensor R
          (Coalgebra.counit.lTensor N (N.inducedCoact n)) =
          Coalgebra.counit.lTensor M
            ((SMulMemClass.subtype N).rTensor C (N.inducedCoact n)) := by
            exact lTensor_counit_natural N (N.inducedCoact n)
      _ = (n : M) ⊗ₜ[R] 1 := by
            simp
      _ = (SMulMemClass.subtype N).rTensor R (n ⊗ₜ[R] 1) := by
            rw [LinearMap.rTensor_tmul, SMulMemClass.subtype_apply]

/-- The inherited coaction on a subcomodule is `Subcomodule.inducedCoact`. -/
@[simp]
theorem induced_coact :
    Comodule.coact (R := R) (C := C) (M := N) = N.inducedCoact :=
  (rfl)

/-- The inherited coaction, included back into `M ⊗ C`, is the ambient coaction. -/
theorem subtype_rTensor_coact (n : N) :
    (SMulMemClass.subtype N).rTensor C (Comodule.coact (R := R) (C := C) (M := N) n) =
      Comodule.coact (R := R) (C := C) (M := M) n :=
  subtype_rTensor_inducedCoact N n

/-- The subtype map of a subcomodule as a morphism of right comodules. -/
noncomputable def subtype : Comodule.Hom R C N M where
  toLinearMap := SMulMemClass.subtype N
  map_coact := by
    ext n
    exact subtype_rTensor_coact N n

/-- The underlying linear map of the subcomodule inclusion is the linear inclusion. -/
@[simp]
theorem subtype_toLinearMap : (Subcomodule.subtype N).toLinearMap = SMulMemClass.subtype N :=
  (rfl)

/-- The subcomodule inclusion acts as the underlying subtype coercion. -/
@[simp]
theorem subtype_apply (n : N) : Subcomodule.subtype N n = n :=
  (rfl)

end Subcomodule

end TauCeti
