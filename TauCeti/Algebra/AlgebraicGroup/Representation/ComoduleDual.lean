/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule
public import TauCeti.Algebra.Coalgebra.Comodule.Dual

/-!
# Dual comodules and point actions

For a finite-projective right comodule `M` over a Hopf algebra, this file relates the point
action on its antipode-twisted dual comodule to the original point action. The canonical
`A`-valued pairing between `A ⊗[R] Module.Dual R M` and `A ⊗[R] M` satisfies

```text
⟨g · ξ, z⟩ = ⟨ξ, g⁻¹ · z⟩.
```

Equivalently, acting by the same point on both inputs preserves evaluation. On pure tensors,
both sides are the inverse point evaluated at the existing matrix coefficient, multiplied by
the two scalar factors. The basis-free proof uses the characteristic equation for
`Comodule.dualCoact`; it does not identify the scalar extension of the dual with the full dual
of the scalar extension.

The action-level results first hold for a possibly noncommutative Hopf algebra over a
commutative semiring. Their `PointRepresentation.ofComodule` corollaries use the dictionary's
current commutative-ring and commutative-Hopf-algebra interface.

## Main declarations

* `TauCeti.Comodule.baseChangeEvaluation`: the canonical scalar-extended evaluation map.
* `TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint`: adjointness of the dual point action
  and the inverse original point action.
* `TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant`: same-point invariance of
  evaluation.
* `TauCeti.HopfAlgebra.PointRepresentation.ofComodule_dual_action_evaluation`: the corresponding
  fixed-object dictionary statement.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a) and the contragredient formula on
  p. 471.
* J. E. Humphreys, *Linear Algebraic Groups*, p. 60.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x

section Evaluation

variable {R : Type u} {M : Type w} {A : Type x}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [CommSemiring A] [Algebra R A]

/-- The canonical pairing of scalar extensions, as the map sending a scalar-extended
`R`-linear functional to an `A`-linear functional on the scalar extension of its domain.

This map requires no finiteness hypothesis and is not asserted to be an equivalence. -/
def baseChangeEvaluation :
    A ⊗[R] Module.Dual R M →ₗ[A] Module.Dual A (A ⊗[R] M) :=
  (Module.Dual.baseChange A).liftBaseChange A

/-- On pure tensors, scalar-extended evaluation is
`⟨a ⊗ φ, b ⊗ m⟩ = a * b * algebraMap R A (φ m)`. -/
@[simp]
theorem baseChangeEvaluation_tmul (a b : A) (φ : Module.Dual R M) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A) (a ⊗ₜ[R] φ) (b ⊗ₜ[R] m) =
      a * b * algebraMap R A (φ m) := by
  simp only [baseChangeEvaluation, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, Algebra.smul_def]
  rw [Algebra.algebraMap_self_apply]
  ac_rfl

end Evaluation

section Coalgebra

variable {R : Type u} {H : Type v} {M : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H] [Algebra R H] [Coalgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [CommSemiring A] [Algebra R A]

/-- Pairing a scalar-extended functional with a point acting on a pure tensor evaluates the
point at the corresponding matrix coefficient. -/
theorem baseChangeEvaluation_endOfPoint_tmul (g : H →ₐ[R] A)
    (a b : A) (φ : Module.Dual R M) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A) (a ⊗ₜ[R] φ)
        (endOfPoint M g (b ⊗ₜ[R] m)) =
      a * b * g (matrixCoefficient (R := R) (C := H) φ m) := by
  rw [endOfPoint_tmul, matrixCoefficient_def]
  generalize coact (R := R) (C := H) (M := M) m = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp [hs, ht, mul_add]
  | tmul n h =>
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul,
        map_smul, baseChangeEvaluation_tmul, smul_eq_mul, TensorProduct.map_tmul,
        LinearMap.id_coe, id_eq, TensorProduct.lid_tmul, Algebra.smul_def, map_mul,
        AlgHom.commutes]
      rw [mul_comm (algebraMap R A (φ n)) (g h)]
      ac_rfl

end Coalgebra

section Hopf

variable {R : Type u} {H : Type v} {M : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]
variable [CommSemiring A] [Algebra R A]

noncomputable section

attribute [local instance] dual

omit [Comodule R H M] [Module.Finite R M] [Module.Projective R M] in
private theorem baseChangeEvaluation_comm_lTensor (g : H →ₐ[R] A)
    (t : Module.Dual R M ⊗[R] H) (b : A) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A)
        (TensorProduct.comm R (Module.Dual R M) A
          (LinearMap.lTensor (Module.Dual R M) g.toLinearMap t)) (b ⊗ₜ[R] m) =
      b * g (dualTensorHom R M H t m) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp [hs, ht, mul_add]
  | tmul φ h =>
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul,
        baseChangeEvaluation_tmul, dualTensorHom_apply, Algebra.smul_def, map_mul,
        AlgHom.commutes]
      rw [mul_comm (algebraMap R A (φ m)) (g h)]
      ac_rfl

/-- On pure tensors, acting on the dual leg and then evaluating gives the inverse point applied
to the original matrix coefficient, together with the two scalar factors. -/
theorem baseChangeEvaluation_dual_endOfPoint_tmul (g : WithConv (H →ₐ[R] A))
    (a b : A) (φ : Module.Dual R M) (m : M) :
    baseChangeEvaluation (R := R) (M := M) (A := A)
        (endOfPoint (Module.Dual R M) g.ofConv (a ⊗ₜ[R] φ)) (b ⊗ₜ[R] m) =
      a * b * (g⁻¹).ofConv (matrixCoefficient (R := R) (C := H) φ m) := by
  rw [endOfPoint_tmul]
  rw [dual_coact (R := R) (H := H) (M := M)]
  simp only [map_smul, LinearMap.smul_apply, baseChangeEvaluation_comm_lTensor]
  rw [dualTensorHom_dualCoact_apply, AlgHom.convInv_apply]
  simp only [smul_eq_mul]
  ac_rfl

/-- The point action on the antipode-twisted dual comodule is adjoint, under canonical
scalar-extended evaluation, to the original point action at the inverse point. -/
theorem baseChangeEvaluation_dual_endOfPoint (g : WithConv (H →ₐ[R] A))
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    baseChangeEvaluation (R := R) (M := M) (A := A)
        (endOfPoint (Module.Dual R M) g.ofConv ξ) z =
      baseChangeEvaluation (R := R) (M := M) (A := A) ξ
        (endOfPoint M (g⁻¹).ofConv z) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | add ξ η hξ hη => simp only [map_add, LinearMap.add_apply, hξ, hη]
  | tmul a φ =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul b m =>
          rw [baseChangeEvaluation_dual_endOfPoint_tmul,
            baseChangeEvaluation_endOfPoint_tmul]

/-- Acting by the same point on a finite-projective comodule and its antipode-twisted dual
preserves the canonical scalar-extended evaluation pairing. -/
theorem baseChangeEvaluation_dual_endOfPoint_invariant (g : WithConv (H →ₐ[R] A))
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    baseChangeEvaluation (R := R) (M := M) (A := A)
        (endOfPoint (Module.Dual R M) g.ofConv ξ) (endOfPoint M g.ofConv z) =
      baseChangeEvaluation (R := R) (M := M) (A := A) ξ z := by
  rw [baseChangeEvaluation_dual_endOfPoint]
  congr 1
  have h := LinearMap.congr_fun (endOfPoint_convMul M g⁻¹ g) z
  simpa using h.symm

end

end Hopf

end Comodule

namespace HopfAlgebra.PointRepresentation

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [rho : Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

noncomputable section

attribute [local instance] Comodule.dual

/-- For the point action supplied by the representation--comodule dictionary, evaluation of a
dual-action generator is inverse-point evaluation of the original matrix coefficient. -/
theorem ofComodule_dual_action_evaluation_tmul
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (a b : A) (φ : Module.Dual R M) (m : M) :
    Comodule.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val (a ⊗ₜ[R] φ))
        (b ⊗ₜ[R] m) =
      a * b * (g⁻¹).ofConv (Comodule.matrixCoefficient (R := R) (C := H) φ m) := by
  rw [ofComodule_action_tmul]
  rw [Comodule.dual_coact (R := R) (H := H) (M := M)]
  simpa only [Comodule.endOfPoint_tmul, Comodule.dual_coact, LinearMap.lTensor_def]
    using Comodule.baseChangeEvaluation_dual_endOfPoint_tmul (g := g) a b φ m

/-- In the fixed-object representation--comodule dictionary, the point action induced on the
dual comodule is adjoint under evaluation to the original action at the inverse point. -/
theorem ofComodule_dual_action_evaluation
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    Comodule.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val ξ) z =
      Comodule.baseChangeEvaluation (R := R) (M := M) (A := A) ξ
        (((ofComodule rho).action A g⁻¹).val z) := by
  have hdual :
      ((ofComodule (Comodule.dual R H M)).action A g).val =
        Comodule.endOfPoint (Module.Dual R M) g.ofConv := by
    refine TensorProduct.AlgebraTensorModule.ext fun a φ ↦ ?_
    rw [ofComodule_action_tmul (rho := Comodule.dual R H M),
      Comodule.endOfPoint_tmul, LinearMap.lTensor_def]
  have horiginal :
      ((ofComodule rho).action A g⁻¹).val =
        Comodule.endOfPoint M (g⁻¹).ofConv := by
    refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
    rw [ofComodule_action_tmul (rho := rho), Comodule.endOfPoint_tmul,
      LinearMap.lTensor_def]
  rw [hdual, horiginal]
  exact Comodule.baseChangeEvaluation_dual_endOfPoint g ξ z

/-- In the fixed-object representation--comodule dictionary, applying the same point to a
finite-projective comodule and its dual preserves scalar-extended evaluation. -/
theorem ofComodule_dual_action_evaluation_invariant
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    Comodule.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val ξ)
        (((ofComodule rho).action A g).val z) =
      Comodule.baseChangeEvaluation (R := R) (M := M) (A := A) ξ z := by
  rw [ofComodule_dual_action_evaluation]
  congr 1
  calc
    ((ofComodule rho).action A g⁻¹).val (((ofComodule rho).action A g).val z) =
        (((ofComodule rho).action A g⁻¹) * ((ofComodule rho).action A g)).val z := by
      rw [Units.val_mul, Module.End.mul_apply]
    _ = ((ofComodule rho).action A (g⁻¹ * g)).val z := by
      rw [((ofComodule rho).action A).hom.map_mul]
    _ = z := by simp

end

end HopfAlgebra.PointRepresentation

end TauCeti
