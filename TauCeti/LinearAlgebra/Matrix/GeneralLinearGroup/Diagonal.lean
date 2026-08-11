/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `GL` and `Matrix.GeneralLinearGroup.det` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `MulEquiv.piUnits` identifies the units of a product with the product of the units, and is what
-- makes the diagonal embedding a homomorphism.
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Diagonal elements of the general linear group

A family of units `t : Fin n → kˣ` is the diagonal of an invertible diagonal matrix, and this
assignment is a group homomorphism `TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k`. Its entries,
its determinant and its injectivity are recorded here.

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 1.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} {n : ℕ}

section Semiring

variable [Semiring k]

/-- Coordinatewise units embed in `GL n k` as diagonal matrices. -/
def diagGL : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : Fin n → kˣ) : (diagGL t : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : Fin n → kˣ) (i j : Fin n) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe]
  exact Matrix.diagonal_apply ..

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (n := n)) := by
  intro t s h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simpa using this

end Semiring

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL [CommRing k] (t : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL_coe, Matrix.det_diagonal]

end TauCeti
