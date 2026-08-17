/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.TransferInstance

/-!
# The cotangent-dual model of the tangent Lie algebra

For a commutative bialgebra `H` over `R`, the tangent space at the identity has two models:
counit-valued derivations of `H`, and the linear dual of the augmentation cotangent space
`ker(ε) / ker(ε)²`. The existing linear equivalence between them transports the convolution
commutator to the cotangent-dual model. This file records the resulting Lie algebra structure and
packages the comparison as a Lie equivalence.

## Main declarations

* `TauCeti.Derivation.cotangentDualLieEquiv`: the cotangent dual is canonically the tangent Lie
  algebra of counit-valued derivations.
* `TauCeti.Derivation.tangentScalarExtensionLieEquiv`: scalar extension of the cotangent-dual
  Lie algebra agrees with coefficient-valued tangent derivations.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and item 10.20.

This identifies the fixed module used by the adjoint representation with `Lie(G)` in Layer 2 of
the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.Derivation

open _root_.Coalgebra TensorProduct WithConv

universe u v

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H]

section Bialgebra

variable [Bialgebra R H]

section Base

/-- The Lie ring structure on the dual augmentation cotangent space, transported from
counit-valued derivations through `cotangentLinearEquiv`. -/
noncomputable instance instLieRingCotangentDual :
    LieRing (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  (cotangentLinearEquiv (R := R) (A := H) (B := R)).toAddEquiv.lieRing

/-- The Lie algebra structure on the dual augmentation cotangent space, transported from
counit-valued derivations through `cotangentLinearEquiv`. -/
noncomputable instance instLieAlgebraCotangentDual :
    LieAlgebra R (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  (cotangentLinearEquiv (R := R) (A := H) (B := R)).lieAlgebra

/-- The canonical Lie equivalence from the dual augmentation cotangent space to the tangent Lie
algebra of counit-valued derivations. -/
noncomputable def cotangentDualLieEquiv :
    LieEquiv R (Module.Dual R (Bialgebra.CotangentSpace R H))
      (Derivation R H (Bialgebra.CounitAlgebra R H R)) :=
  (cotangentLinearEquiv (R := R) (A := H) (B := R)).lieEquiv R

/-- The cotangent-dual Lie equivalence has the existing cotangent linear equivalence as its
underlying map. -/
@[simp]
theorem cotangentDualLieEquiv_apply
    (f : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    cotangentDualLieEquiv (R := R) (H := H) f =
      cotangentLinearEquiv (R := R) (A := H) (B := R) f := by
  exact LinearEquiv.lieEquiv_apply _ f

/-- The inverse cotangent-dual Lie equivalence has the inverse cotangent linear equivalence as
its underlying map. -/
@[simp]
theorem cotangentDualLieEquiv_symm_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    (cotangentDualLieEquiv (R := R) (H := H)).symm d =
      (cotangentLinearEquiv (R := R) (A := H) (B := R)).symm d := by
  exact LinearEquiv.lieEquiv_symm_apply _ d

/-- The bracket on the cotangent dual is characterized by transport to the convolution bracket
on counit-valued derivations. -/
@[simp]
theorem cotangentLinearEquiv_bracket
    (f g : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    cotangentLinearEquiv (R := R) (A := H) (B := R) ⁅f, g⁆ =
      ⁅cotangentLinearEquiv f, cotangentLinearEquiv g⁆ :=
  (cotangentDualLieEquiv (R := R) (H := H)).map_lie f g

end Base

section ScalarExtension

variable {B : Type*} [CommRing B] [Algebra R B]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

private theorem tangentScalarExtensionEquiv_tmul_eq
    (b : B) (f : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (b ⊗ₜ[R] f) =
      b • mapValue (A := H) (Algebra.ofId R B)
        (cotangentLinearEquiv (R := R) (A := H) (B := R) f) := by
  ext h
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H B).injective
  calc
    Bialgebra.CounitAlgebra.algEquivSelf R H B
          (tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (b ⊗ₜ[R] f) h) =
        b * algebraMap R B (f (Bialgebra.cotangentMap R H h)) := by
      rw [tangentScalarExtensionEquiv_tmul_apply]
      exact Bialgebra.CounitAlgebra.algEquivSelf_apply
        (R := R) (A := H) (B := B) _
    _ = b * Bialgebra.CounitAlgebra.algEquivSelf R H B
          (mapValue (A := H) (Algebra.ofId R B)
            (cotangentLinearEquiv (R := R) (A := H) (B := R) f) h) := by
      rw [mapValue_apply, cotangentLinearEquiv_apply_apply]
      simp only [Algebra.ofId_apply]
      exact congrArg (b * ·)
        (Bialgebra.CounitAlgebra.algEquivSelf_apply
          (R := R) (A := H) (B := B)
          (algebraMap R B (f (Bialgebra.cotangentMap R H h)) :
            Bialgebra.CounitAlgebra R H B)).symm
    _ = Bialgebra.CounitAlgebra.algEquivSelf R H B
          ((b • mapValue (A := H) (Algebra.ofId R B)
            (cotangentLinearEquiv (R := R) (A := H) (B := R) f)) h) :=
      by
        rw [Derivation.smul_apply, Bialgebra.CounitAlgebra.algEquivSelf_apply,
          Bialgebra.CounitAlgebra.algEquivSelf_apply]
        rfl

private theorem tangentScalarExtensionEquiv_bracket_tmul
    (b c : B) (f g : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
        ⁅b ⊗ₜ[R] f, c ⊗ₜ[R] g⁆ =
      ⁅tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (b ⊗ₜ[R] f),
        tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (c ⊗ₜ[R] g)⁆ := by
  simp only [LieAlgebra.ExtendScalars.bracket_tmul,
    tangentScalarExtensionEquiv_tmul_eq, tangentScalarExtensionEquiv_tmul_eq,
    tangentScalarExtensionEquiv_tmul_eq, smul_lie, lie_smul, smul_smul]
  rw [mul_comm c b, cotangentLinearEquiv_bracket, mapValue_lie]

/-- The established scalar-extension equivalence preserves the Lie bracket. -/
@[simp]
theorem tangentScalarExtensionEquiv_bracket
    (x y : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := B) ⁅x, y⁆ =
      ⁅tangentScalarExtensionEquiv (R := R) (A := H) (B := B) x,
        tangentScalarExtensionEquiv (R := R) (A := H) (B := B) y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_lie y, map_zero, zero_lie]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [add_lie x₁ x₂ y, map_add, map_add, add_lie, hx₁, hx₂]
  | tmul b f =>
      induction y using TensorProduct.induction_on with
      | zero => rw [lie_zero (b ⊗ₜ[R] f), map_zero, lie_zero]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [lie_add (b ⊗ₜ[R] f) y₁ y₂, map_add, map_add, lie_add, hy₁, hy₂]
      | tmul c g => exact tangentScalarExtensionEquiv_bracket_tmul b c f g

/-- Scalar extension of the cotangent-dual Lie algebra is canonically Lie-equivalent to the
coefficient-valued tangent Lie algebra. -/
noncomputable def tangentScalarExtensionLieEquiv :
    LieEquiv B (B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H))
      (Derivation R H (Bialgebra.CounitAlgebra R H B)) :=
  { tangentScalarExtensionEquiv (R := R) (A := H) (B := B) with
    map_lie' := fun {x y} => tangentScalarExtensionEquiv_bracket x y }

/-- The scalar-extension Lie equivalence has the existing scalar-extension linear equivalence as
its underlying map. -/
@[simp]
theorem tangentScalarExtensionLieEquiv_apply
    (x : B ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionLieEquiv (R := R) (H := H) (B := B) x =
      tangentScalarExtensionEquiv (R := R) (A := H) (B := B) x := by
  -- A bare `rfl` is rejected by the module export checker because it would expose the
  -- implementation of `tangentScalarExtensionLieEquiv`; no generated equation lemma exists.
  change tangentScalarExtensionEquiv (R := R) (A := H) (B := B) x = _
  rfl

/-- The inverse scalar-extension Lie equivalence has the inverse scalar-extension linear
equivalence as its underlying map. -/
@[simp]
theorem tangentScalarExtensionLieEquiv_symm_apply
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    (tangentScalarExtensionLieEquiv (R := R) (H := H) (B := B)).symm d =
      (tangentScalarExtensionEquiv (R := R) (A := H) (B := B)).symm d := by
  apply (tangentScalarExtensionLieEquiv (R := R) (H := H) (B := B)).symm_apply_eq.mpr
  rw [tangentScalarExtensionLieEquiv_apply,
    (tangentScalarExtensionEquiv (R := R) (A := H) (B := B)).apply_symm_apply]

end ScalarExtension

end Bialgebra

end TauCeti.Derivation
