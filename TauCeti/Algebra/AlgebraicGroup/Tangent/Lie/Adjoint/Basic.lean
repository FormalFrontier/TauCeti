/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic

/-!
# The adjoint action respects the Lie bracket

`Derivation.adDerivation` conjugates a tangent vector by a point of the Hopf algebra.
`Tangent.Adjoint` shows that this is an action by linear automorphisms; this file adds the
one statement that needs the Lie structure of `Tangent.Lie.Basic`, namely that each `Ad g` is
an automorphism of the Lie bracket rather than merely of the module.

It is kept out of `Tangent.Adjoint` so that the non-Lie tangent aggregator does not re-export
the Lie-algebra structure.

## Main results

* `Derivation.adDerivation_lie`: `Ad g ⁅d₁, d₂⁆ = ⁅Ad g d₁, Ad g d₂⁆`.
-/

public section

namespace Derivation

open TauCeti _root_.Coalgebra WithConv TensorProduct

-- Only the coefficient algebra `B` need be a ring: the bracket is a commutator, so the
-- convolution algebra `A →ₗ[R] CounitAlgebra R A B` must admit subtraction, and it inherits that
-- from `B` alone. The base `R` and the Hopf algebra `A` are used only multiplicatively.
variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommRing B] [Algebra R B]

variable (B) in
/-- **The adjoint action is by Lie automorphisms.** `Ad g` is conjugation `g ⋆ · ⋆ g⁻¹` in the
convolution ring, and conjugation by a unit preserves the commutator, so it respects the
bracket of tangent vectors. -/
@[simp]
theorem adDerivation_lie (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d₁ d₂ : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    adDerivation B g ⁅d₁, d₂⁆ = ⁅adDerivation B g d₁, adDerivation B g d₂⁆ := by
  have hinv : toConv ((g⁻¹).ofConv.toLinearMap) * toConv g.ofConv.toLinearMap = 1 := by
    rw [← AlgHom.toLinearMap_convMul, inv_mul_cancel, AlgHom.toLinearMap_convOne]
  have hbr : ∀ e₁ e₂ : Derivation R A (Bialgebra.CounitAlgebra R A B),
      toConv (↑⁅e₁, e₂⁆ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) =
        toConv (↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
            toConv (↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) -
          toConv (↑e₂ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) *
            toConv (↑e₁ : A →ₗ[R] Bialgebra.CounitAlgebra R A B) := by
    intro e₁ e₂
    rw [coe_bracket, toConv_sub, toConv_ofConv, toConv_ofConv]
  refine Derivation.ext fun a => ?_
  have key : toConv (↑(adDerivation B g ⁅d₁, d₂⁆) : A →ₗ[R] Bialgebra.CounitAlgebra R A B) =
      toConv (↑⁅adDerivation B g d₁, adDerivation B g d₂⁆ :
        A →ₗ[R] Bialgebra.CounitAlgebra R A B) := by
    rw [toConv_coe_adDerivation, hbr, hbr, toConv_coe_adDerivation, toConv_coe_adDerivation,
      mul_sub, sub_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (toConv ((g⁻¹).ofConv.toLinearMap)), hinv, one_mul,
      ← mul_assoc (toConv ((g⁻¹).ofConv.toLinearMap)), hinv, one_mul]
  exact DFunLike.congr_fun (congrArg ofConv key) a

end Derivation
