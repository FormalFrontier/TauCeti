/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of symmetric algebras

A derivation of `SymmetricAlgebra R M` is determined by its values on the canonical generators.
Conversely, every linear map from `M` to a module over its symmetric algebra extends uniquely to a
derivation. This file packages the extension and the resulting linear equivalence.

The public interface follows Mathlib's analogous `Polynomial.mkDerivation` and
`MvPolynomial.mkDerivation` APIs.

The construction uses the trivial square-zero extension. A prescribed value `f x` is paired with
the generator `SymmetricAlgebra.ι R M x`; the universal property of the symmetric algebra extends
this pair multiplicatively, and projection to the square-zero component gives the derivation.

## Main definitions and results

* `SymmetricAlgebra.mkDerivation`: extend prescribed values on the canonical generators.
* `SymmetricAlgebra.derivation_ext`: symmetric-algebra derivations agree when they agree on the
  canonical generators.
* `SymmetricAlgebra.mkDerivationEquiv`: derivations are linearly equivalent to their restrictions
  to the canonical generators.

## Roadmap

This supplies the derivation input for the PBW action on `SymmetricAlgebra R L`, toward the
Poincare--Birkhoff--Witt target in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.
-/

public section

namespace SymmetricAlgebra

noncomputable section

universe u v w

variable {R : Type u} {M : Type v} {A : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid A] [Module R A] [Module (SymmetricAlgebra R M) A]
variable [IsScalarTower R (SymmetricAlgebra R M) A]

/-- The right-module structure induced by commutativity, used by the square-zero extension. -/
local instance commOppositeModule (S A : Type*) [CommSemiring S] [AddCommMonoid A] [Module S A] :
    Module Sᵐᵒᵖ A :=
  Module.compHom A (RingEquiv.toOpposite S).symm.toRingHom

local instance commCentralScalar (S A : Type*) [CommSemiring S] [AddCommMonoid A] [Module S A] :
    IsCentralScalar S A where
  op_smul_eq_smul _ _ := rfl

private noncomputable def derivationGeneratorLift
    (f : M →ₗ[R] A) :
    M →ₗ[R] TrivSqZeroExt (SymmetricAlgebra R M) A :=
  (TrivSqZeroExt.inlAlgHom R (SymmetricAlgebra R M) A).toLinearMap.comp
      (ι R M) +
    ((TrivSqZeroExt.inrHom (SymmetricAlgebra R M) A).restrictScalars R).comp f

private noncomputable def derivationLift (f : M →ₗ[R] A) :
    SymmetricAlgebra R M →ₐ[R]
      TrivSqZeroExt (SymmetricAlgebra R M) A :=
  lift (derivationGeneratorLift f)

private theorem derivationLift_fst (f : M →ₗ[R] A)
    (a : SymmetricAlgebra R M) :
    (derivationLift f a).fst = a := by
  have h : (TrivSqZeroExt.fstHom R (SymmetricAlgebra R M) A).comp
      (derivationLift f) =
      AlgHom.id R (SymmetricAlgebra R M) := by
    apply algHom_ext
    ext x
    simp [derivationLift, derivationGeneratorLift]
  exact AlgHom.congr_fun h a

private noncomputable def mkDerivationAux (f : M →ₗ[R] A) :
    Derivation R (SymmetricAlgebra R M) A where
  toLinearMap :=
    ((TrivSqZeroExt.sndHom (SymmetricAlgebra R M) A).restrictScalars R).comp
      (derivationLift f).toLinearMap
  map_one_eq_zero' := by
    -- Expose the square-zero component used as the derivation value.
    change (derivationLift f 1).snd = 0
    rw [map_one, TrivSqZeroExt.snd_one]
  leibniz' a b := by
    -- Express Leibniz in the square-zero component before expanding multiplication.
    change (derivationLift f (a * b)).snd =
      a • (derivationLift f b).snd + b • (derivationLift f a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, derivationLift_fst, derivationLift_fst]
    simp only [op_smul_eq_smul]

private theorem mkDerivationAux_ι (f : M →ₗ[R] A) (x : M) :
    mkDerivationAux f (ι R M x) = f x := by
  simp [mkDerivationAux, derivationLift, derivationGeneratorLift]

omit [IsScalarTower R (SymmetricAlgebra R M) A] in
/-- Two derivations of a symmetric algebra are equal if they agree on the canonical generators. -/
@[ext]
theorem derivation_ext
    {D₁ D₂ : Derivation R (SymmetricAlgebra R M) A}
    (h : ∀ x, D₁ (ι R M x) = D₂ (ι R M x)) : D₁ = D₂ := by
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x => exact h x
  | mul a b ha hb => simp only [Derivation.leibniz, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The derivation on `SymmetricAlgebra R M` taking the prescribed value `f x` on each canonical
generator `SymmetricAlgebra.ι R M x`. -/
noncomputable def mkDerivation :
    (M →ₗ[R] A) →ₗ[R] Derivation R (SymmetricAlgebra R M) A where
  toFun := mkDerivationAux
  map_add' f g := derivation_ext fun x => by simp [mkDerivationAux_ι]
  map_smul' r f := derivation_ext fun x => by simp [mkDerivationAux_ι]

/-- `mkDerivation` takes the prescribed value on a canonical symmetric-algebra generator. -/
@[simp]
theorem mkDerivation_ι (f : M →ₗ[R] A) (x : M) :
    mkDerivation f (ι R M x) = f x :=
  mkDerivationAux_ι f x

/-- Restriction to the canonical generators identifies derivations of a symmetric algebra with
linear maps out of its generating module. -/
noncomputable def mkDerivationEquiv :
    (M →ₗ[R] A) ≃ₗ[R] Derivation R (SymmetricAlgebra R M) A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation
      toFun := fun D => D.toLinearMap.comp (ι R M)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _D => derivation_ext fun x => mkDerivation_ι _ x
      right_inv := fun f => LinearMap.ext fun x => mkDerivation_ι f x }

@[simp]
theorem mkDerivationEquiv_apply (f : M →ₗ[R] A) :
    mkDerivationEquiv f = mkDerivation f := by
  rfl

@[simp]
theorem mkDerivationEquiv_symm_apply
    (D : Derivation R (SymmetricAlgebra R M) A) :
    (mkDerivationEquiv.symm D : M →ₗ[R] A) =
      D.toLinearMap.comp (ι R M) := by
  rfl

end

end SymmetricAlgebra
