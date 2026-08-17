/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosSemidef
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Fourier atoms

This file records the spatial Fourier atom used by the positive-definite and Bochner APIs.
It uses Mathlib's `2π` Fourier convention.

## Main declarations

* `TauCeti.fourierAtom`: the spatial atom `v ↦ exp (-2πi⟪v, q⟫)`.
* `TauCeti.posSemidef_fourierAtom`: the subtraction kernel attached to a
  Fourier atom is positive definite.
* `TauCeti.continuous_fourierAtom`: Fourier atoms are continuous in the spatial variable.
* `TauCeti.fourierAtom_zero_left` and `TauCeti.fourierAtom_zero_right`: a Fourier atom is `1`
  when either argument is `0`.
-/

public section

open Complex ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Fourier atom at frequency `q`, using Mathlib's `2π` Fourier convention. -/
public noncomputable def fourierAtom (q : V) (v : V) : ℂ :=
  (Real.fourierChar (-(inner ℝ v q)) : ℂ)

/-- The `Real.fourierChar` form of a Fourier atom. -/
theorem fourierAtom_eq_fourierChar (q : V) (v : V) :
    fourierAtom q v = (Real.fourierChar (-(inner ℝ v q)) : ℂ) :=
  by simp [fourierAtom]

/-- The raw exponential form of a Fourier atom. -/
@[simp]
theorem fourierAtom_apply (q : V) (v : V) :
    fourierAtom q v =
      Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)) := by
  rw [fourierAtom_eq_fourierChar, Real.fourierChar_apply]
  congr 1
  norm_num [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- A Fourier atom at the zero frequency is `1`.

Not a `@[simp]` lemma: `simp` already proves it through `fourierAtom_apply`, and the simpNF
linter reports the tagged form as a duplicate. -/
theorem fourierAtom_zero_left (v : V) : fourierAtom (0 : V) v = 1 := by
  simp [fourierAtom]

/-- A Fourier atom evaluated at the zero point is `1`. Not a `@[simp]` lemma, for the same
reason as `fourierAtom_zero_left`. -/
theorem fourierAtom_zero_right (q : V) : fourierAtom q (0 : V) = 1 := by
  simp [fourierAtom]

/-- Fourier atoms turn spatial subtraction into a rank-one positive-definite kernel. -/
theorem fourierAtom_sub (q v w : V) :
    fourierAtom q (v - w) =
      conj (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ))) *
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ w q : ℝ) : ℂ)) := by
  rw [fourierAtom_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf

/-- The spatial subtraction kernel supplied by a Fourier atom is positive definite. -/
theorem posSemidef_fourierAtom (q : V) :
    Matrix.PosSemidef fun v w : V => fourierAtom q (v - w) := by
  simp_rw [fourierAtom_sub]
  simpa only [RCLike.star_def] using posSemidef_rankOne
    (fun v : V => Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)))

/-- Fourier atoms are continuous in the spatial variable. -/
theorem continuous_fourierAtom (q : V) : Continuous (fourierAtom q) := by
  convert
    (by fun_prop :
      Continuous fun v : V => ((Real.fourierChar (-(inner ℝ v q)) : Circle) : ℂ)) using 1
  ext v
  exact (fourierAtom_eq_fourierChar q v).symm

end TauCeti
