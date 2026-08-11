/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Duals of finite projective comodules

For a finite projective right comodule `M` over a Hopf algebra `H`, this file constructs the
right-comodule structure on the linear dual `Module.Dual R M`. Its coaction is characterized
basis-freely by

```text
Σ φ₀(m) φ₁ = S(c(φ, m)),
```

where `c(φ, m)` is the matrix coefficient and `S` is the antipode. The canonical equivalence
`dualTensorHomEquiv` turns this equation into a definition without requiring a basis or any
finiteness condition on `H`.

## Main declarations

* `TauCeti.Comodule.dualCoact`: the coaction map on the linear dual.
* `TauCeti.Comodule.dualTensorHom_dualCoact`: its characteristic linear-map equation.
* `TauCeti.Comodule.dual`: the explicit, non-global dual comodule structure.

## References

This is the standard finite-projective dual-comodule construction; see Sweedler,
*Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

noncomputable section

/-- The basis-free coaction map on the linear dual of a finite projective right comodule.

Under `dualTensorHomEquiv`, the tensor `dualCoact φ` corresponds to the linear map
`m ↦ S(c(φ, m))`. -/
def dualCoact : Module.Dual R M →ₗ[R] Module.Dual R M ⊗[R] H :=
  (dualTensorHomEquiv R M H).symm.toLinearMap ∘ₗ
    (LinearMap.compRight R (HopfAlgebra.antipode R (A := H)) ∘ₗ
      matrixCoefficientBilinear (R := R) (C := H) (M := M))

/-- The characteristic equation for the dual coaction, as an equality of linear maps in the
vector argument. -/
@[simp]
theorem dualTensorHom_dualCoact (φ : Module.Dual R M) :
    dualTensorHom R M H (dualCoact (R := R) (H := H) (M := M) φ) =
      (HopfAlgebra.antipode R (A := H)).comp
        (matrixCoefficientBilinear (R := R) (C := H) (M := M) φ) := by
  ext m
  simp [dualCoact]

/-- Pointwise characteristic equation for the dual coaction:
`Σ φ₀(m) φ₁ = S(c(φ, m))`. -/
theorem dualTensorHom_dualCoact_apply (φ : Module.Dual R M) (m : M) :
    dualTensorHom R M H (dualCoact (R := R) (H := H) (M := M) φ) m =
      HopfAlgebra.antipode R
        (matrixCoefficient (R := R) (C := H) φ m) := by
  rw [dualTensorHom_dualCoact]
  simp only [LinearMap.comp_apply, matrixCoefficientBilinear_apply_apply]

/-- Applying the counit to the coefficient leg of the dual coaction recovers the original
functional. -/
theorem dualCoact_counit : (Coalgebra.counit (R := R) (A := H)).lTensor (Module.Dual R M) ∘ₗ
        dualCoact (R := R) (H := H) (M := M) =
      (TensorProduct.mk R (Module.Dual R M) R).flip 1 := by
  ext φ
  apply (dualTensorHom_bijective (R := R) (M := M) (N := R)).1
  ext m
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
  have hcomp := LinearMap.congr_fun
    (dualTensorHom_comp_lTensor (M := M)
      (Coalgebra.counit (R := R) (A := H)))
    (dualCoact (R := R) (H := H) (M := M) φ)
  have hcomp' :
      dualTensorHom R M R
          ((Coalgebra.counit (R := R) (A := H)).lTensor (Module.Dual R M)
            (dualCoact (R := R) (H := H) (M := M) φ)) =
        (Coalgebra.counit (R := R) (A := H)).compRight R
          (dualTensorHom R M H (dualCoact (R := R) (H := H) (M := M) φ)) := by
    simpa only [LinearMap.comp_apply] using hcomp
  rw [hcomp']
  simp only [LinearMap.compRight_apply, LinearMap.comp_apply, dualTensorHom_apply]
  rw [dualTensorHom_dualCoact_apply]
  simp

/-- Contracting after coacting the dual leg can be expressed by coacting the vector leg,
applying the contraction and antipode, and swapping the two Hopf-algebra factors. This is the
basis-free tensor identity underlying coassociativity of `dualCoact`. -/
private theorem dualTensorHom_assoc_dualCoact_rTensor (x : Module.Dual R M ⊗[R] H) (m : M) :
    dualTensorHom R M (H ⊗[R] H)
        (TensorProduct.assoc R (Module.Dual R M) H H
          ((dualCoact (R := R) (H := H) (M := M)).rTensor H x)) m =
      TensorProduct.comm R H H
        (TensorProduct.map (dualTensorHom R M H x) (HopfAlgebra.antipode R)
          (coact (R := R) (C := H) (M := M) m)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
        using congrArg₂ (· + ·) hx hy
  | tmul φ h =>
      have hleft (y : Module.Dual R M ⊗[R] H) :
          dualTensorHom R M (H ⊗[R] H)
              (TensorProduct.assoc R (Module.Dual R M) H H (y ⊗ₜ[R] h)) m =
            dualTensorHom R M H y m ⊗ₜ[R] h := by
        calc
          _ = (rTensorHomEquivHomRTensor R M H H
              (dualTensorHom R M H y ⊗ₜ[R] h)) m := by
            simp [rTensorHomEquivHomRTensor]
          _ = _ := by
            rw [rTensorHomEquivHomRTensor_apply]
            exact TensorProduct.rTensorHomToHomRTensor_apply
              (dualTensorHom R M H y) h m
      rw [LinearMap.rTensor_tmul, hleft, dualTensorHom_dualCoact_apply]
      rw [matrixCoefficient_def]
      generalize coact (R := R) (C := H) (M := M) m = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
          simpa only [map_add, TensorProduct.add_tmul]
            using congrArg₂ (· + ·) hx hy
      | tmul n a =>
          simp [TensorProduct.smul_tmul']

/-- The dual coaction is coassociative. -/
theorem dualCoact_coassoc :
    TensorProduct.assoc R (Module.Dual R M) H H ∘ₗ
        (dualCoact (R := R) (H := H) (M := M)).rTensor H ∘ₗ
          dualCoact (R := R) (H := H) (M := M) =
      (Coalgebra.comul (R := R) (A := H)).lTensor (Module.Dual R M) ∘ₗ
        dualCoact (R := R) (H := H) (M := M) := by
  ext φ
  apply (dualTensorHom_bijective (R := R) (M := M) (N := H ⊗[R] H)).1
  ext m
  simp only [LinearMap.comp_apply]
  calc
    _ = TensorProduct.comm R H H
        (TensorProduct.map
          (dualTensorHom R M H (dualCoact (R := R) (H := H) (M := M) φ))
          (HopfAlgebra.antipode R)
          (coact (R := R) (C := H) (M := M) m)) :=
      dualTensorHom_assoc_dualCoact_rTensor
        (dualCoact (R := R) (H := H) (M := M) φ) m
    _ = _ := by
      have hcomp := LinearMap.congr_fun
        (dualTensorHom_comp_lTensor (M := M)
          (Coalgebra.comul (R := R) (A := H)))
        (dualCoact (R := R) (H := H) (M := M) φ)
      have hcomp' :
          dualTensorHom R M (H ⊗[R] H)
              ((Coalgebra.comul (R := R) (A := H)).lTensor (Module.Dual R M)
                (dualCoact (R := R) (H := H) (M := M) φ)) =
            (Coalgebra.comul (R := R) (A := H)).compRight R
              (dualTensorHom R M H (dualCoact (R := R) (H := H) (M := M) φ)) := by
        simpa only [LinearMap.comp_apply] using hcomp
      rw [hcomp']
      simp only [LinearMap.compRight_apply, LinearMap.comp_apply]
      rw [dualTensorHom_dualCoact]
      simp only [LinearMap.comp_apply, matrixCoefficientBilinear_apply_apply]
      rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply,
        comul_matrixCoefficient]
      rw [TensorProduct.map_comm]
      rw [TensorProduct.map_map]
      rfl

variable (R H M) in
/-- The right-comodule structure on the linear dual of a finite projective right comodule.

This is deliberately not a global instance: a module can carry multiple coactions. Downstream
code should select it explicitly, typically as a local instance. -/
@[instance_reducible]
noncomputable def dual : Comodule R H (Module.Dual R M) where
  coact := dualCoact (R := R) (H := H) (M := M)
  coassoc := dualCoact_coassoc (R := R) (H := H) (M := M)
  lTensor_counit_comp_coact := dualCoact_counit (R := R) (H := H) (M := M)

attribute [local instance] dual

/-- The coaction of the explicit dual-comodule structure is `dualCoact`. -/
@[simp]
theorem dual_coact :
    coact (R := R) (C := H) (M := Module.Dual R M) =
      dualCoact (R := R) (H := H) (M := M) := (rfl)

end

end TauCeti.Comodule
