/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Dual comodules and point representations

For a finite-projective right comodule over a commutative Hopf algebra, this file expresses the
evaluation identities for dual comodule point actions through the fixed-object
representation--comodule dictionary. The point action on the dual is adjoint to the original
action at the inverse point, and acting by the same point on both inputs preserves evaluation.

The underlying action-level results hold at semiring generality in
`TauCeti.Algebra.Coalgebra.Comodule.Evaluation`; the corollaries here use the dictionary's current
commutative-ring and commutative-Hopf-algebra interface.

## Main declarations

* `TauCeti.HopfAlgebra.PointRepresentation.ofComodule_dual_action_evaluation_tmul`: evaluation of
  a dual-action generator.
* `TauCeti.HopfAlgebra.PointRepresentation.ofComodule_dual_action_evaluation`: adjointness in the
  fixed-object dictionary.
* `TauCeti.HopfAlgebra.PointRepresentation.ofComodule_dual_action_evaluation_invariant`:
  same-point invariance of evaluation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a) and the contragredient formula on
  p. 471.
* J. E. Humphreys, *Linear Algebraic Groups*, p. 60.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra.PointRepresentation

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [rho : Comodule R H M]
variable [Module.Finite R M] [Module.Projective R M]

noncomputable section

attribute [local instance] Comodule.dual

/-- For the point action supplied by the representation--comodule dictionary, evaluation of a
dual-action generator is inverse-point evaluation of the original matrix coefficient.

This is not a simp lemma because `ofComodule_dual_action_evaluation` and `map_inv` simplify its
left-hand side first, so the simp-normal-form linter rejects the specialized orientation. -/
theorem ofComodule_dual_action_evaluation_tmul
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (a b : A) (φ : Module.Dual R M) (m : M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val (a ⊗ₜ[R] φ))
        (b ⊗ₜ[R] m) =
      a * b * (g⁻¹).ofConv (Comodule.matrixCoefficient (R := R) (C := H) φ m) := by
  rw [ofComodule_action_val_eq_endOfPoint]
  exact Comodule.baseChangeEvaluation_dual_endOfPoint_tmul (g := g) a b φ m

/-- In the fixed-object representation--comodule dictionary, the point action induced on the
dual comodule is adjoint under evaluation to the original action at the inverse point. -/
@[simp↓]
theorem ofComodule_dual_action_evaluation
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val ξ) z =
      TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A) ξ
        (((ofComodule rho).action A g⁻¹).val z) := by
  rw [ofComodule_action_val_eq_endOfPoint, ofComodule_action_val_eq_endOfPoint]
  exact Comodule.baseChangeEvaluation_dual_endOfPoint g ξ z

/-- In the fixed-object representation--comodule dictionary, applying the same point to a
finite-projective comodule and its dual preserves scalar-extended evaluation.

This is not a simp lemma because `ofComodule_dual_action_evaluation` and `map_inv` simplify its
left-hand side first, so the simp-normal-form linter rejects the specialized orientation. -/
theorem ofComodule_dual_action_evaluation_invariant
    (A : CommAlgCat.{max u v w} R) (g : points (H := H) A)
    (ξ : A ⊗[R] Module.Dual R M) (z : A ⊗[R] M) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A)
        (((ofComodule (Comodule.dual R H M)).action A g).val ξ)
        (((ofComodule rho).action A g).val z) =
      TauCeti.Module.Dual.baseChangeEvaluation (R := R) (M := M) (A := A) ξ z := by
  rw [ofComodule_action_val_eq_endOfPoint, ofComodule_action_val_eq_endOfPoint]
  exact Comodule.baseChangeEvaluation_dual_endOfPoint_invariant g ξ z

end

end TauCeti.HopfAlgebra.PointRepresentation
