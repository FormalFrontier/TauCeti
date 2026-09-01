/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# Determinant square classes of orthogonal transformations

The determinant of an orthogonal transformation of a finite-dimensional space is a unit. Reducing
that unit modulo squares gives a homomorphism from the orthogonal group to the square-class group.
This construction only uses the orthogonal group and does not require a characteristic assumption.

## Main definitions and results

* `QuadraticMap.orthogonalDetSquareClass`: the determinant modulo squares on `O(Q)`.
* `QuadraticMap.orthogonalDetSquareClass_apply`: its value on an orthogonal
  transformation.
-/

public section

open TauCeti

namespace QuadraticMap

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The determinant of an orthogonal transformation, reduced modulo squares. -/
noncomputable def orthogonalDetSquareClass {N : Type w} [AddCommMonoid N] [Module K N]
    [FiniteDimensional K V]
    (Q : QuadraticMap K V N) :
    TauCeti.QuadraticMap.orthogonalGroup Q →* Multiplicative (SquareClassGroup K) :=
  let _ := Module.finBasis K V
  squareClassHom.comp <|
    LinearEquiv.det.comp (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

/-- The determinant square-class map evaluates by taking the determinant modulo squares. -/
@[simp]
theorem orthogonalDetSquareClass_apply {N : Type w} [AddCommMonoid N] [Module K N]
    [FiniteDimensional K V]
    (Q : QuadraticMap K V N) (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    orthogonalDetSquareClass Q g = squareClassHom (LinearEquiv.det (g : V ≃ₗ[K] V)) := by
  rw [orthogonalDetSquareClass]
  rfl

end QuadraticMap
