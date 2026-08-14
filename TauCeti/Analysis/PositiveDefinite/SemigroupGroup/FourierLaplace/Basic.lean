/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Product
public import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# Laplace--Fourier atoms for semigroup-group positive-definite functions

This file records the atomic positive-definite functions that appear inside the
Berg--Christensen--Ressel Laplace--Fourier representation. For a nonnegative Laplace parameter
`p : ℝ≥0` and a spatial frequency `q : V`, the separated function

`(t, v) ↦ exp (-t p) * exp (-2πi ⟪v, q⟫)`

is semigroup-group positive definite on `ℝ≥0 × V`, and is continuous when `V` is topological.
The proof is just the rank-one-kernel calculation for each factor, followed by the existing
separated-product constructor.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"): the representing integrand in the target theorem is a finite-measure
mixture of these atoms.

## Main declarations

* `TauCeti.posSemidef_laplaceAtom`: the time kernel
  `(t, u) ↦ exp (-(t + u) p)` is positive definite.
* `TauCeti.isSemigroupGroupPD_laplaceFourierAtom`: the separated BCR atom is positive definite.
* `TauCeti.isSemigroupGroupPD_laplaceFourierAtom_and_continuous`: the same result packaged with
  continuity.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open Complex ComplexConjugate
open scoped ComplexOrder NNReal

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Laplace atom at `p : ℝ≥0`, as a complex-valued function on nonnegative time. -/
public noncomputable def laplaceAtom (p : ℝ≥0) (t : ℝ≥0) : ℂ :=
  (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ)

/-- The definitional exponential form of a Laplace atom. -/
@[simp]
theorem laplaceAtom_def (p : ℝ≥0) (t : ℝ≥0) :
    laplaceAtom p t = (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ) :=
  by simp [laplaceAtom]

/-- The Laplace atom is symmetric in its two nonnegative arguments: the frequency and the time
enter `exp (-t p)` in the same way. -/
theorem laplaceAtom_comm (p t : ℝ≥0) : laplaceAtom p t = laplaceAtom t p := by
  rw [laplaceAtom_def, laplaceAtom_def, neg_mul, neg_mul, mul_comm]

/-- Laplace atoms turn time addition into a rank-one positive-definite kernel. -/
theorem laplaceAtom_add (p t u : ℝ≥0) :
    laplaceAtom p (t + u) = conj (laplaceAtom p t) * laplaceAtom p u := by
  simp only [laplaceAtom_def, Complex.conj_ofReal]
  norm_cast
  rw [← Real.exp_add]
  congr 1
  rw [NNReal.coe_add]
  ring

/-- The time kernel supplied by a Laplace atom is positive definite. -/
theorem posSemidef_laplaceAtom (p : ℝ≥0) :
    Matrix.PosSemidef fun t u : ℝ≥0 => laplaceAtom p (t + u) := by
  simp_rw [laplaceAtom_add]
  simpa only [RCLike.star_def] using
    posSemidef_rankOne (fun t : ℝ≥0 => laplaceAtom p t)

/-- Laplace atoms are continuous in the nonnegative time variable. -/
theorem continuous_laplaceAtom (p : ℝ≥0) : Continuous (laplaceAtom p) := by
  convert
    (by fun_prop :
      Continuous fun t : ℝ≥0 => (Real.exp (-(t : ℝ) * (p : ℝ)) : ℂ)) using 1
  ext t
  exact (laplaceAtom_def p t).symm

/-- The separated Laplace--Fourier atom is semigroup-group positive definite. -/
theorem isSemigroupGroupPD_laplaceFourierAtom (p : ℝ≥0) (q : V) :
    IsSemigroupGroupPD fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2 :=
  isSemigroupGroupPD_mul_time_spatial_of_kernels
    (posSemidef_laplaceAtom p) (posSemidef_fourierAtom q)

/-- The separated Laplace--Fourier atom is semigroup-group positive definite and continuous. -/
theorem isSemigroupGroupPD_laplaceFourierAtom_and_continuous (p : ℝ≥0) (q : V) :
    IsSemigroupGroupPD (fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2) ∧
      Continuous (fun x : ℝ≥0 × V => laplaceAtom p x.1 * fourierAtom q x.2) :=
  isSemigroupGroupPD_mul_time_spatial_of_kernels_and_continuous
    (posSemidef_laplaceAtom p) (posSemidef_fourierAtom q)
    (continuous_laplaceAtom p) (continuous_fourierAtom q)

end TauCeti
