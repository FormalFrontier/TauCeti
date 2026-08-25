/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.laurentFunctions`, the subalgebra restricted into below, and the characters spanning
-- it; this module also re-exports `TauCeti.weightChar`.
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.LaurentFunctions
-- `TauCeti.diagGL`, the diagonal embedding of the torus points, and `TauCeti.det_diagGL`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal
-- `TauCeti.Matrix.GeneralLinearGroup.rationalFunctions`, restricted along `diagGL` below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions

/-!
# Restricting a rational function on `GL n R` to the diagonal torus

A rational function on `GL n R` restricts along the diagonal embedding `TauCeti.diagGL` to a
Laurent function on the torus (`TauCeti.comp_diagGL_mem_laurentFunctions`). The determinant becomes
the product of the coordinates, hence a character, so inverting a power of it stays inside the
algebra; a polynomial in the matrix entries becomes a polynomial in the coordinates, because an
off-diagonal entry of a diagonal matrix vanishes and a diagonal one is a coordinate.

This is the step that lets the weight theory of `GL n k` be run inside the algebra of Laurent
functions built in `TauCeti.LinearAlgebra.Basis.DiagonalTorus.LaurentFunctions`, where distinct
characters are linearly independent and a weight can therefore be read off an expansion.

## Main results

* `TauCeti.eval_diagGL_mem_laurentFunctions`: a polynomial in the matrix entries restricts to a
  Laurent function on the diagonal torus.
* `TauCeti.comp_diagGL_mem_laurentFunctions`: so does a rational function on `GL n R`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, "The maximal torus and weight spaces".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A matrix entry of a diagonal matrix, as a function of the point of the torus, is a Laurent
function: off the diagonal it vanishes, and on the diagonal it is a coordinate. -/
theorem entry_diagGL_mem_laurentFunctions (p : Fin n × Fin n) :
    (fun t : Fin n → Rˣ ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2)
      ∈ laurentFunctions R (Fin n) := by
  by_cases hp : p.1 = p.2
  · have h : (fun t : Fin n → Rˣ ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2)
        = ⇑(weightCharHom R (Pi.single p.1 1)) := by
      funext t
      rw [diagGL_apply, weightCharHom_single]
      simp [hp]
    rw [h]
    exact weightCharHom_mem_laurentFunctions R _
  · have h : (fun t : Fin n → Rˣ ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2) = 0 := by
      funext t
      rw [diagGL_apply]
      simp [hp]
    rw [h]
    exact zero_mem _

/-- A polynomial in the matrix entries restricts along the diagonal embedding to a Laurent
function on the torus. -/
theorem eval_diagGL_mem_laurentFunctions (P : MvPolynomial (Fin n × Fin n) R) :
    (fun t : Fin n → Rˣ ↦
        MvPolynomial.eval (fun p ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2) P)
      ∈ laurentFunctions R (Fin n) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Subalgebra.algebraMap_mem _ a
  | add P Q hP hQ =>
    simp only [map_add]
    exact add_mem hP hQ
  | mul_X P p hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact mul_mem hP (entry_diagGL_mem_laurentFunctions p)

/-- **A rational function on `GL n R` restricts to a Laurent function on the diagonal torus.**
The determinant of a diagonal matrix is the product of its coordinates, so the denominator is an
inverted character and stays inside the algebra, while the numerator is handled by
`TauCeti.eval_diagGL_mem_laurentFunctions`. -/
theorem comp_diagGL_mem_laurentFunctions {f : GL (Fin n) R → R}
    (hf : f ∈ Matrix.GeneralLinearGroup.rationalFunctions R n) :
    (fun t : Fin n → Rˣ ↦ f (diagGL t)) ∈ laurentFunctions R (Fin n) := by
  obtain ⟨P, m, hP⟩ := Matrix.GeneralLinearGroup.mem_rationalFunctions.mp hf
  have hval : ∀ t : Fin n → Rˣ, f (diagGL t)
      = weightCharHom R (fun _ ↦ -(m : ℤ)) t *
        MvPolynomial.eval (fun p ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2) P := by
    intro t
    have hd : ((∏ i, t i : Rˣ) : R) ^ m * f (diagGL t)
        = MvPolynomial.eval (fun p ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2) P := by
      have := hP (diagGL t)
      rwa [← Matrix.GeneralLinearGroup.val_det_apply, det_diagGL] at this
    have hu : (((∏ j, t j : Rˣ) ^ (-(m : ℤ)) : Rˣ) : R) * ((∏ i, t i : Rˣ) : R) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast (∏ i, t i) m, ← zpow_add]
      simp
    rw [← hd, weightCharHom_const, ← mul_assoc, hu, one_mul]
  have hfun : (fun t : Fin n → Rˣ ↦ f (diagGL t))
      = ⇑(weightCharHom R (fun _ : Fin n ↦ -(m : ℤ))) *
        fun t ↦ MvPolynomial.eval (fun p ↦ (diagGL t : Matrix (Fin n) (Fin n) R) p.1 p.2) P := by
    funext t
    rw [Pi.mul_apply, hval t]
  rw [hfun]
  exact mul_mem (weightCharHom_mem_laurentFunctions R _) (eval_diagGL_mem_laurentFunctions P)

end TauCeti
