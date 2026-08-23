/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Evaluation and dual point actions

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

The action-level results hold for a possibly noncommutative Hopf algebra over a commutative
semiring.

## Main declarations

* `TauCeti.Comodule.baseChangeEvaluation_endOfPoint_tmul`: evaluation after a point acts on a
  pure tensor.
* `TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint`: adjointness of the dual point action
  and the inverse original point action.
* `TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant`: same-point invariance of
  evaluation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a) and the contragredient formula on
  p. 471.
* J. E. Humphreys, *Linear Algebraic Groups*, p. 60.
-/

public section

open TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

section Coalgebra

variable {R : Type u} {H : Type v} {M : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H] [Algebra R H] [Coalgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]
variable [CommSemiring A] [Algebra R A]

/-- Pairing a scalar-extended functional with a point acting on a pure tensor evaluates the
point at the corresponding matrix coefficient. -/
-- Prefer the characteristic evaluation formula before `endOfPoint_tmul` expands the inner action.
@[simp↓]
theorem baseChangeEvaluation_endOfPoint_tmul (g : H →ₐ[R] A)
    (a b : A) (φ : Module.Dual R M) (m : M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A) (a ⊗ₜ[R] φ)
        (endOfPoint M g (b ⊗ₜ[R] m)) =
      a * b * g (matrixCoefficient (R := R) (C := H) φ m) := by
  rw [endOfPoint_tmul, matrixCoefficient_def]
  generalize coact (R := R) (C := H) (M := M) m = t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp [hs, ht, mul_add]
  | tmul n h =>
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul,
        map_smul, TauCeti.Module.Dual.baseChangeEvaluation_tmul, smul_eq_mul,
        TensorProduct.map_tmul,
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
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (TensorProduct.comm R (Module.Dual R M) A
          (LinearMap.lTensor (Module.Dual R M) g.toLinearMap t)) (b ⊗ₜ[R] m) =
      b * g (dualTensorHom R M H t m) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp [hs, ht, mul_add]
  | tmul φ h =>
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.comm_tmul,
        TauCeti.Module.Dual.baseChangeEvaluation_tmul, dualTensorHom_apply, Algebra.smul_def,
        map_mul,
        AlgHom.commutes]
      rw [mul_comm (algebraMap R A (φ m)) (g h)]
      ac_rfl

/-- On pure tensors, acting on the dual leg and then evaluating gives the inverse point applied
to the original matrix coefficient, together with the two scalar factors. -/
-- Prefer the characteristic evaluation formula before the dual action itself is simplified.
@[simp↓]
theorem baseChangeEvaluation_dual_endOfPoint_tmul (g : WithConv (H →ₐ[R] A))
    (a b : A) (φ : Module.Dual R M) (m : M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
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
@[simp]
theorem baseChangeEvaluation_dual_endOfPoint (g : WithConv (H →ₐ[R] A))
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (endOfPoint (Module.Dual R M) g.ofConv ξ) z =
      TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A) ξ
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
-- Prefer invariance before adjointness simplifies the first action.
@[simp↓]
theorem baseChangeEvaluation_dual_endOfPoint_invariant (g : WithConv (H →ₐ[R] A))
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (endOfPoint (Module.Dual R M) g.ofConv ξ) (endOfPoint M g.ofConv z) =
      TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A) ξ z := by
  rw [baseChangeEvaluation_dual_endOfPoint]
  congr 1
  have h := LinearMap.congr_fun (endOfPoint_convMul M g⁻¹ g) z
  simpa using h.symm

end

end Hopf

end TauCeti.Comodule
