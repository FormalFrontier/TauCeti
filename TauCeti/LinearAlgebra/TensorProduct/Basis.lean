/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Naturality of base-changed basis coordinates

An `R`-basis of a module gives a basis after extension of scalars to every commutative
`R`-algebra. This file records that the coordinates in those bases commute with a map of
the scalar-extension algebras.

## Main declaration

* `Module.Basis.map_baseChange_repr`: applying a scalar map to a coordinate in a base-changed
  basis agrees with first mapping the tensor and then taking its coordinate.
-/

public section

open TensorProduct

namespace Module.Basis

universe u v w x

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [CommSemiring S] [Algebra R S]
variable {T : Type w} [CommSemiring T] [Algebra R T]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {ι : Type*}

/-- Coordinates in a base-changed basis are natural in the scalar-extension algebra. -/
theorem map_baseChange_repr (b : Basis ι R M) (φ : S →ₐ[R] T)
    (z : S ⊗[R] M) (i : ι) :
    φ ((b.baseChange S).repr z i) =
      (b.baseChange T).repr
        (TensorProduct.map φ.toLinearMap LinearMap.id z) i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, LinearEquiv.map_add, LinearMap.map_add, Finsupp.add_apply] using
        congrArg₂ (· + ·) hx hy
  | tmul s m => simp

end Module.Basis
