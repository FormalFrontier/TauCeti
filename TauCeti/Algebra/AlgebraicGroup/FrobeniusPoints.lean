/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Frobenius on the points of an affine group

Let `H` be a Hopf algebra over `ℤ` and let `A` be an algebra over the prime field
`ZMod p`. Post-composition with the `n`-fold Frobenius of `A` sends an `A`-valued point
`f : H →ₐ[ℤ] A` to the point `h ↦ f(h) ^ (p ^ n)`. Functoriality of convolution makes this a
group endomorphism of the points represented by `H`.

This is the field-endomorphism part of the pinned Chevalley--Demazure interface in Layer 9 of the
ReductiveGroups roadmap. Once a pinned group's integral coordinate Hopf algebra is constructed,
`frobeniusPoints p n` supplies the `p ^ n`-power endomorphism on its points over an algebraic
closure. The construction itself needs neither algebraic closedness nor finite type.

## Main definitions and results

* `TauCeti.HopfAlgebra.frobeniusValueAlgHom` is the `n`-fold Frobenius of the value algebra,
  regarded as a `ℤ`-algebra endomorphism.
* `TauCeti.HopfAlgebra.frobeniusPoints` is the induced group endomorphism on convolution points.
* `TauCeti.HopfAlgebra.frobeniusPoints_apply_apply` identifies its action with the
  `p ^ n`-power map.
* `TauCeti.HopfAlgebra.frobeniusPoints_add` gives the iteration law.
* `TauCeti.HopfAlgebra.mapValue_comp_frobeniusPoints` proves naturality in the value algebra.

## References

The construction uses Mathlib's `FiniteField.frobeniusAlgHom` and Tau Ceti's convolution-valued
functor of points. It advances the “points over an algebraically closed field” target in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`; that target explicitly requests the `q`-power
Frobenius as its first field-endomorphism case.
-/

public section

open WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable (p n : ℕ) [Fact p.Prime]
variable {H : Type u} [Semiring H] [_root_.HopfAlgebra ℤ H]
variable {A : Type v} [CommRing A] [Algebra (ZMod p) A]

/-- The `n`-fold Frobenius of a `ZMod p`-algebra, regarded as a `ℤ`-algebra endomorphism.

It sends `a` to `a ^ (p ^ n)`. Restriction of scalars is what makes it act on the `ℤ`-valued
functor of points of an integral affine group scheme. -/
@[expose] noncomputable def frobeniusValueAlgHom : A →ₐ[ℤ] A :=
  ((FiniteField.frobeniusAlgHom (ZMod p) A) ^ n).restrictScalars ℤ

/-- The `n`-fold Frobenius sends `a` to `a ^ (p ^ n)`. -/
@[simp] theorem frobeniusValueAlgHom_apply (a : A) :
    frobeniusValueAlgHom p n a = a ^ (p ^ n) := by
  simp only [frobeniusValueAlgHom, AlgHom.coe_restrictScalars', AlgHom.coe_pow,
    FiniteField.coe_frobeniusAlgHom]
  rw [ZMod.card]
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ, pow_mul]

/-- The zeroth Frobenius iterate is the identity algebra endomorphism. -/
@[simp] theorem frobeniusValueAlgHom_zero :
    frobeniusValueAlgHom p 0 (A := A) = AlgHom.id ℤ A := by
  ext a
  simp

/-- Frobenius iterates add under composition. -/
theorem frobeniusValueAlgHom_add (m : ℕ) :
    frobeniusValueAlgHom p (n + m) (A := A) =
      (frobeniusValueAlgHom p n).comp (frobeniusValueAlgHom p m) := by
  ext a
  simp only [AlgHom.comp_apply, frobeniusValueAlgHom_apply]
  rw [pow_add, ← pow_mul, mul_comm]

/-- The `p ^ n`-power Frobenius endomorphism on the group of `A`-valued points represented by
the integral Hopf algebra `H`. -/
@[expose] noncomputable def frobeniusPoints :
    WithConv (H →ₐ[ℤ] A) →* WithConv (H →ₐ[ℤ] A) :=
  AlgHom.mapValue (frobeniusValueAlgHom p n)

/-- Frobenius on points is post-composition with Frobenius on the value algebra. -/
@[simp] theorem frobeniusPoints_apply (f : WithConv (H →ₐ[ℤ] A)) :
    frobeniusPoints p n f =
      toConv ((frobeniusValueAlgHom p n).comp f.ofConv) :=
  rfl

/-- Pointwise, the `n`-fold Frobenius sends an `A`-valued point `f` to
`h ↦ f(h) ^ (p ^ n)`. -/
@[simp] theorem frobeniusPoints_apply_apply (f : WithConv (H →ₐ[ℤ] A)) (h : H) :
    (frobeniusPoints p n f).ofConv h = f.ofConv h ^ (p ^ n) := by
  rw [frobeniusPoints_apply, ofConv_toConv, AlgHom.comp_apply, frobeniusValueAlgHom_apply]

/-- The zeroth Frobenius iterate is the identity on points. -/
@[simp] theorem frobeniusPoints_zero :
    frobeniusPoints p 0 (H := H) (A := A) = MonoidHom.id _ := by
  rw [frobeniusPoints, frobeniusValueAlgHom_zero, AlgHom.mapValue_id]

/-- Frobenius iterates add under composition on the group of points. -/
theorem frobeniusPoints_add (m : ℕ) :
    frobeniusPoints p (n + m) (H := H) (A := A) =
      (frobeniusPoints p n).comp (frobeniusPoints p m) := by
  simp only [frobeniusPoints]
  rw [frobeniusValueAlgHom_add, AlgHom.mapValue_comp]

variable {B : Type w} [CommRing B] [Algebra (ZMod p) B]

/-- Frobenius commutes with a homomorphism of `ZMod p`-algebras. -/
theorem map_frobeniusValueAlgHom (φ : A →ₐ[ZMod p] B) :
    (frobeniusValueAlgHom p n).comp (φ.restrictScalars ℤ) =
      (φ.restrictScalars ℤ).comp (frobeniusValueAlgHom p n) := by
  ext a
  simp

/-- Naturality of Frobenius on points in the value algebra. Post-composing a point by
`φ : A →ₐ[ZMod p] B` before or after applying the `n`-fold Frobenius gives the same point. -/
theorem mapValue_comp_frobeniusPoints (φ : A →ₐ[ZMod p] B) :
    (AlgHom.mapValue (H := H) (φ.restrictScalars ℤ)).comp
        (frobeniusPoints p n (H := H) (A := A)) =
      (frobeniusPoints p n (H := H) (A := B)).comp
        (AlgHom.mapValue (H := H) (φ.restrictScalars ℤ)) := by
  simp only [frobeniusPoints]
  rw [← AlgHom.mapValue_comp, ← AlgHom.mapValue_comp, map_frobeniusValueAlgHom]

end HopfAlgebra

end TauCeti
