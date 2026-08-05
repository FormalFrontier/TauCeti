/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Diagonal elements of the general linear group

This file embeds coordinatewise units as invertible diagonal matrices and describes their
action in the standard representation. These elements are the concrete points of the diagonal
torus used to compute characters and weight spaces.

Two facts about diagonal matrices proper are recorded alongside: invertibility of a diagonal
matrix upgrades its diagonal entries to units, and a matrix commuting with a diagonal matrix
has no entries away from the diagonal wherever that diagonal matrix separates two coordinates.

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.

## Main statements

* `TauCeti.isUnit_apply_of_isDiag`: the diagonal entries of an invertible diagonal matrix are
  units.
* `TauCeti.isDiag_of_commute_diagonal`: a matrix commuting with a diagonal matrix of pairwise
  distinct entries is itself diagonal.

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
theorem diagGL_coe (t : Fin n → kˣ) : (diagGL t : Matrix (Fin n) (Fin n) k) =
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

/-- The diagonal entries of an invertible diagonal matrix are units, because a diagonal matrix
is invertible exactly when its diagonal is invertible coordinatewise. -/
theorem isUnit_apply_of_isDiag {g : GL (Fin n) k}
    (hg : (g : Matrix (Fin n) (Fin n) k).IsDiag) (i : Fin n) :
    IsUnit ((g : Matrix (Fin n) (Fin n) k) i i) := by
  have h : IsUnit (Matrix.diagonal (Matrix.diag (g : Matrix (Fin n) (Fin n) k))) := by
    rw [hg.diagonal_diag]
    exact Units.isUnit g
  exact (Matrix.isUnit_diagonal.mp h).apply i

section NoZeroDivisors

variable [NoZeroDivisors k]

/-- A matrix commuting with a diagonal matrix has vanishing `(i, j)` entry whenever the diagonal
matrix separates the coordinates `i` and `j`.  Comparing the `(i, j)` entries of the two products
gives `tᵢ * gᵢⱼ = gᵢⱼ * tⱼ`, so `gᵢⱼ` is annihilated by `tᵢ - tⱼ`, which is nonzero. -/
theorem apply_eq_zero_of_commute_diagonal {t : Fin n → k} {g : Matrix (Fin n) (Fin n) k}
    (hg : Commute (Matrix.diagonal t) g) {i j : Fin n} (hij : t i ≠ t j) : g i j = 0 := by
  have hentry : (Matrix.diagonal t * g) i j = (g * Matrix.diagonal t) i j := by rw [hg.eq]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hzero : g i j * (t i - t j) = 0 := by
    rw [mul_sub, ← hentry]
    ring
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hij)

/-- **A matrix commuting with a diagonal matrix of pairwise distinct entries is diagonal.** -/
theorem isDiag_of_commute_diagonal {t : Fin n → k} (ht : Function.Injective t)
    {g : Matrix (Fin n) (Fin n) k} (hg : Commute (Matrix.diagonal t) g) : g.IsDiag :=
  fun _ _ hij => apply_eq_zero_of_commute_diagonal hg (ht.ne hij)

end NoZeroDivisors

end TauCeti
