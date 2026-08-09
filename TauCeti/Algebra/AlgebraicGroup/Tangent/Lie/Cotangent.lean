/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.TransferInstance

/-!
# The cotangent-dual model of the tangent Lie algebra

For a commutative bialgebra `H` over `R`, the tangent space at the identity has two models:
counit-valued derivations of `H`, and the linear dual of the augmentation cotangent space
`ker(ε) / ker(ε)²`. The existing linear equivalence between them transports the convolution
commutator to the cotangent-dual model. This file records the resulting Lie algebra structure and
packages the comparison as a Lie equivalence.

For a Hopf algebra with finite projective cotangent space, the adjoint point representation is
already defined on scalar extensions of the cotangent dual. Its action preserves the transported
bracket: after the scalar-extension comparison, this is exactly the fact that convolution
conjugation preserves commutators.

## Main declarations

* `TauCeti.Derivation.cotangentDualLieEquiv`: the cotangent dual is canonically the tangent Lie
  algebra of counit-valued derivations.
* `TauCeti.Derivation.tangentScalarExtensionLieEquiv`: scalar extension of the cotangent-dual
  Lie algebra agrees with coefficient-valued tangent derivations.
* `TauCeti.Derivation.adjointLieEquiv`: every algebra-valued point acts by Lie algebra
  automorphisms on the scalar-extended tangent space.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§14.1–14.3.

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

/-- The explicit derivation Lie ring used to transport the base cotangent-dual bracket. -/
noncomputable local instance :
    LieRing (Derivation R H (Bialgebra.CounitAlgebra R H R)) :=
  Derivation.instLieRing (R := R) (A := H) (B := R)

/-- The explicit derivation Lie algebra used to transport the base cotangent-dual bracket. -/
noncomputable local instance :
    LieAlgebra R (Derivation R H (Bialgebra.CounitAlgebra R H R)) :=
  Derivation.instLieAlgebra (R := R) (A := H) (B := R)

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

omit [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] in
private theorem algEquivSelf_derivation_smul_apply'
    (b : B) (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf R H B ((b • d) h) =
      b * Bialgebra.CounitAlgebra.algEquivSelf R H B (d h) := by
  rw [Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply]
  rfl

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
      (algEquivSelf_derivation_smul_apply' b
        (mapValue (A := H) (Algebra.ofId R B)
          (cotangentLinearEquiv (R := R) (A := H) (B := R) f)) h).symm

omit [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] in
private theorem bracket_smul (b c : B)
    (d e : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    ⁅b • d, c • e⁆ = (b * c) • ⁅d, e⁆ := by
  apply Derivation.ext
  intro h
  have hconv :
      toConv (↑⁅b • d, c • e⁆ : H →ₗ[R] Bialgebra.CounitAlgebra R H B) =
        toConv (↑((b * c) • ⁅d, e⁆) : H →ₗ[R] Bialgebra.CounitAlgebra R H B) := by
    rw [toConv_coe_bracket, Derivation.coe_smul_linearMap, toConv_smul,
      Derivation.coe_smul_linearMap, toConv_smul, Derivation.coe_smul_linearMap,
      toConv_smul, toConv_coe_bracket, LieRing.of_associative_ring_bracket,
      LieRing.of_associative_ring_bracket, smul_mul_assoc, mul_smul_comm,
      smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm c b, smul_sub]
  exact DFunLike.congr_fun (congrArg ofConv hconv) h

private theorem tangentScalarExtensionEquiv_bracket_tmul
    (b c : B) (f g : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
        ⁅b ⊗ₜ[R] f, c ⊗ₜ[R] g⁆ =
      ⁅tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (b ⊗ₜ[R] f),
        tangentScalarExtensionEquiv (R := R) (A := H) (B := B) (c ⊗ₜ[R] g)⁆ := by
  simp only [LieAlgebra.ExtendScalars.bracket_tmul,
    tangentScalarExtensionEquiv_tmul_eq, tangentScalarExtensionEquiv_tmul_eq,
    tangentScalarExtensionEquiv_tmul_eq, bracket_smul]
  rw [cotangentLinearEquiv_bracket, mapValue_lie]

private theorem tangentScalarExtensionEquiv_bracket
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
  change tangentScalarExtensionEquiv (R := R) (A := H) (B := B) x = _
  rfl

end ScalarExtension

end Bialgebra

section Adjoint

variable [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- The adjoint point action preserves the bracket on the scalar-extended tangent space. -/
private theorem adjointAction_bracket_aux
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    ∀ x y : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H),
      (adjointAction A g).val ⁅x, y⁆ =
        ⁅(adjointAction A g).val x, (adjointAction A g).val y⁆ := by
  intro x y
  apply (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).injective
  rw [tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointAction,
    tangentScalarExtensionEquiv_bracket,
    tangentScalarExtensionEquiv_adjointAction,
    tangentScalarExtensionEquiv_adjointAction]
  exact adDerivation_lie A (pointInCounitAlgebra A g) _ _

/-- Every algebra-valued point acts on the scalar-extended tangent space by a Lie algebra
automorphism. -/
noncomputable def adjointLieEquiv
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    LieEquiv A (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H))
      (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  let e := (adjointAction A g).toLinearEquiv
  { e with
    map_lie' := fun {x y} => adjointAction_bracket_aux A g x y }

/-- The adjoint Lie automorphism acts by the existing adjoint point representation. -/
@[simp]
theorem adjointLieEquiv_apply
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    adjointLieEquiv (R := R) (H := H) A g x = (adjointAction A g).val x := (rfl)

/-- The identity point acts as the identity Lie automorphism. -/
@[simp]
theorem adjointLieEquiv_one
    (A : CommAlgCat.{max u v} R) :
    adjointLieEquiv (R := R) (H := H) A 1 = 1 := by
  ext x
  rw [adjointLieEquiv_apply, LieEquiv.one_apply]
  exact congrArg
    (fun e : LinearMap.GeneralLinearGroup A
        (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) => e.val x)
    (map_one (adjointAction A).hom)

/-- The adjoint Lie automorphism of a product is the composite of the two adjoint Lie
automorphisms. -/
theorem adjointLieEquiv_mul
    (A : CommAlgCat.{max u v} R) (g h : HopfAlgebra.points (H := H) A) :
    adjointLieEquiv (R := R) (H := H) A (g * h) =
      (adjointLieEquiv (R := R) (H := H) A h).trans
        (adjointLieEquiv (R := R) (H := H) A g) := by
  ext x
  rw [adjointLieEquiv_apply, LieEquiv.trans_apply,
    adjointLieEquiv_apply, adjointLieEquiv_apply]
  have hmul := congrArg
    (fun e : LinearMap.GeneralLinearGroup A
        (A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) => e.val x)
    (map_mul (adjointAction A).hom g h)
  change (adjointAction A (g * h)).val x =
    (adjointAction A g).val ((adjointAction A h).val x) at hmul
  exact hmul

/-- The adjoint point action preserves the bracket on the scalar-extended tangent space. -/
@[simp]
theorem adjointAction_bracket
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x y : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    (adjointAction A g).val ⁅x, y⁆ =
      ⁅(adjointAction A g).val x, (adjointAction A g).val y⁆ :=
  by exact adjointAction_bracket_aux A g x y

end Adjoint

end TauCeti.Derivation
