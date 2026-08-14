/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Bounds for positive-definite subtraction kernels

This file specializes the scalar Cauchy--Schwarz estimates from
`TauCeti.Analysis.Matrix.PosSemidef` to subtraction kernels `(a, b) ↦ ψ (a - b)`. It records the
reality and nonnegativity of `ψ 0`, conjugate symmetry under negation, and the uniform norm bound
`‖ψ z‖ ≤ re (ψ 0)`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C ("Positive-definite
functions and Bochner's theorem"), specifically the positive-definite-kernel / GNS-Kolmogorov API
prerequisite. No Mathlib code is vendored; the proof reuses Mathlib's determinant nonnegativity
for positive semidefinite matrices.

## Main declarations

* `TauCeti.map_zero_re_nonneg_of_posSemidef`,
  `TauCeti.map_zero_eq_ofReal_re_of_posSemidef` and
  `TauCeti.norm_apply_le_map_zero_re_of_posSemidef`: for an `RCLike`-valued function
  with positive-definite subtraction kernel, the value at `0` is real with nonnegative real part
  and bounds the function uniformly in norm.
* `TauCeti.map_neg_eq_conj_of_posSemidef`: such a function is conjugate-symmetric
  under negation, `ψ (-v) = conj (ψ v)`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddGroup V] {ψ : V → 𝕜}

/-- The value at `0` of a function with positive-definite subtraction kernel has nonnegative
real part. -/
theorem map_zero_re_nonneg_of_posSemidef
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) :
    0 ≤ RCLike.re (ψ 0) := by
  have h : (0 : 𝕜) ≤ ψ 0 := by
    simpa using hpd.diag_nonneg (i := 0)
  exact (RCLike.nonneg_iff.mp h).1

/-- The value at `0` of a function with positive-definite subtraction kernel is real. -/
theorem map_zero_eq_ofReal_re_of_posSemidef
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) :
    ψ 0 = ((RCLike.re (ψ 0) : ℝ) : 𝕜) := by
  have h : (0 : 𝕜) ≤ ψ 0 := by
    simpa using hpd.diag_nonneg (i := 0)
  simpa [(RCLike.nonneg_iff.mp h).2] using (RCLike.re_add_im (ψ 0)).symm

/-- A function with positive-definite subtraction kernel is conjugate-symmetric under negation:
`ψ (-v) = conj (ψ v)`. This is the Hermitian symmetry of the kernel, read along the diagonal
translate `(v, 0)`. -/
theorem map_neg_eq_conj_of_posSemidef
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) (v : V) :
    ψ (-v) = conj (ψ v) := by
  simpa only [sub_zero, zero_sub, starRingEnd_apply] using
    (hpd.isHermitian.apply 0 v).symm

/-- A function with positive-definite subtraction kernel is uniformly bounded by the real part
of its value at `0`. -/
theorem norm_apply_le_map_zero_re_of_posSemidef
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) (z : V) :
    ‖ψ z‖ ≤ RCLike.re (ψ 0) := by
  have h := hpd.normSq_le z 0
  simp only [sub_zero, sub_self, RCLike.normSq_eq_def'] at h
  refine le_of_sq_le_sq ?_ (map_zero_re_nonneg_of_posSemidef hpd)
  calc ‖ψ z‖ ^ 2 ≤ RCLike.re (ψ 0) * RCLike.re (ψ 0) := h
    _ = RCLike.re (ψ 0) ^ 2 := (sq (RCLike.re (ψ 0))).symm

end TauCeti
