/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.Algebra.Group.Pi.Units

/-!
# Diagonal elements of the general linear group

This file embeds coordinatewise units as invertible diagonal matrices and describes their
action in the standard representation. These elements are the concrete points of the diagonal
torus used to compute characters and weight spaces.

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layers 1 and 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Coordinatewise units embed in `GL n k` as diagonal matrices. -/
def diagGL : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : Fin n → kˣ) :
    (diagGL t : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : Fin n → kˣ) (i j : Fin n) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe]
  exact Matrix.diagonal_apply ..

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL (t : Fin n → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL_coe, Matrix.det_diagonal]

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (n := n)) := by
  intro t s h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simpa using this

/-- The standard representation acts at `diagGL t` by coordinatewise multiplication. -/
@[simp↓]
theorem stdRep_diagGL_apply (t : Fin n → kˣ) (v : Fin n → k) (i : Fin n) :
    stdRep k n (diagGL t) v i = (t i : k) * v i := by
  rw [stdRep_apply_apply, diagGL_coe]
  exact Matrix.mulVec_diagonal _ _ _

/-- Every standard basis vector is an eigenvector for a diagonal matrix. -/
@[simp↓]
theorem stdRep_diagGL_apply_basisFun (t : Fin n → kˣ) (i : Fin n) :
    stdRep k n (diagGL t) (Pi.basisFun k (Fin n) i) =
      (t i : k) • Pi.basisFun k (Fin n) i := by
  ext j
  rw [stdRep_diagGL_apply]
  by_cases hji : j = i
  · subst j
    simp
  · simp [Pi.basisFun_apply, hji]

end TauCeti
