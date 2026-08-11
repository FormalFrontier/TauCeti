/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic

/-!
# Bounds for positive-definite kernels

This file adds the scalar Cauchy--Schwarz estimates for `RCLike`-valued positive-definite
kernels. If `K` is positive definite, then every `2 × 2` Gram submatrix is positive semidefinite,
so its determinant is nonnegative. Equivalently,
`RCLike.normSq (K a b) ≤ RCLike.re (K a a) * RCLike.re (K b b)`.

These estimates are the kernel-level counterpart of
`TauCeti.IsPositiveDefinite.normSq_le` for positive-definite functions. They are also the basic
inequalities used when normalizing kernels and when constructing the Kolmogorov/GNS seminorm from
a positive-definite kernel.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C ("Positive-definite
functions and Bochner's theorem"), specifically the positive-definite-kernel / GNS-Kolmogorov API
prerequisite. No Mathlib code is vendored; the proof reuses Mathlib's determinant nonnegativity
for positive semidefinite matrices.

## Main declarations

* `TauCeti.isPositiveDefiniteKernel_normSq_le`: kernel Cauchy--Schwarz.
* `TauCeti.isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_left` and
  `TauCeti.isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_right`: zero diagonal entries
  force the corresponding row or column to vanish.
* `TauCeti.isPositiveDefiniteKernel_norm_le_one_of_apply_self_eq_one`: normalized diagonal
  entries bound off-diagonal entries by `1`.
* `TauCeti.map_zero_re_nonneg_of_isPositiveDefiniteKernel`,
  `TauCeti.map_zero_eq_ofReal_re_of_isPositiveDefiniteKernel` and
  `TauCeti.norm_apply_le_map_zero_re_of_isPositiveDefiniteKernel`: for an `RCLike`-valued function
  with positive-definite subtraction kernel, the value at `0` is real with nonnegative real part
  and bounds the function uniformly in norm.
* `TauCeti.map_neg_eq_conj_of_isPositiveDefiniteKernel`: such a function is conjugate-symmetric
  under negation, `ψ (-v) = conj (ψ v)`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {α : Type*} {K : α → α → 𝕜}

/-- The `2 × 2` Gram submatrix of a positive-definite kernel is positive semidefinite. -/
private theorem isPositiveDefiniteKernel_finTwo_posSemidef
    (hK : IsPositiveDefiniteKernel K) (a b : α) :
    (Matrix.of fun i j : Fin 2 => K (![a, b] i) (![a, b] j)).PosSemidef := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  simpa [Matrix.submatrix, Function.comp_def] using hK'.submatrix (fun i : Fin 2 => ![a, b] i)

/-- The kernel Cauchy--Schwarz inequality: for an `RCLike`-valued positive-definite kernel, the
squared norm of an off-diagonal entry is bounded by the product of the two diagonal real parts. -/
theorem isPositiveDefiniteKernel_normSq_le (hK : IsPositiveDefiniteKernel K) (a b : α) :
    RCLike.normSq (K a b) ≤ RCLike.re (K a a) * RCLike.re (K b b) := by
  let A : Matrix (Fin 2) (Fin 2) 𝕜 := Matrix.of fun i j => K (![a, b] i) (![a, b] j)
  have hA : A.PosSemidef := isPositiveDefiniteKernel_finTwo_posSemidef hK a b
  have hdet : 0 ≤ A.det := Matrix.PosSemidef.det_nonneg hA
  have hdet_re : 0 ≤ RCLike.re A.det := by
    simpa using (RCLike.le_iff_re_im.mp hdet).1
  have hconj : K b a = conj (K a b) := by
    exact (isPositiveDefiniteKernel_conj_symm hK a b).symm
  have haa_im : RCLike.im (K a a) = 0 := by
    have h := isPositiveDefiniteKernel_conj_symm hK a a
    exact RCLike.conj_eq_iff_im.mp h
  have hbb_im : RCLike.im (K b b) = 0 := by
    have h := isPositiveDefiniteKernel_conj_symm hK b b
    exact RCLike.conj_eq_iff_im.mp h
  have hdet_eval :
      RCLike.re A.det =
        RCLike.re (K a a) * RCLike.re (K b b) - RCLike.normSq (K a b) := by
    simp [A, Matrix.det_fin_two, hconj, RCLike.normSq_apply, haa_im, hbb_im]
  nlinarith

/-- If the left diagonal entry of a positive-definite kernel is zero, then the corresponding
row entry is zero. -/
theorem isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_left
    (hK : IsPositiveDefiniteKernel K) {a b : α} (ha : K a a = 0) : K a b = 0 := by
  have hnorm := isPositiveDefiniteKernel_normSq_le hK a b
  have hdiag : RCLike.re (K a a) * RCLike.re (K b b) = 0 := by simp [ha]
  have hnorm_zero : RCLike.normSq (K a b) = 0 :=
    le_antisymm (by simpa [hdiag] using hnorm) (RCLike.normSq_nonneg _)
  exact RCLike.normSq_eq_zero.mp hnorm_zero

/-- If the right diagonal entry of a positive-definite kernel is zero, then the corresponding
column entry is zero. -/
theorem isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_right
    (hK : IsPositiveDefiniteKernel K) {a b : α} (hb : K b b = 0) : K a b = 0 := by
  have hba := isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_left hK (a := b) (b := a) hb
  have hconj := isPositiveDefiniteKernel_conj_symm hK a b
  rw [hba] at hconj
  have := congrArg conj hconj
  simpa using this

/-- If both diagonal entries are `1`, then the corresponding off-diagonal entry has norm at
most `1`. This is the common normalized-kernel form of the kernel Cauchy--Schwarz inequality. -/
theorem isPositiveDefiniteKernel_norm_le_one_of_apply_self_eq_one
    (hK : IsPositiveDefiniteKernel K) {a b : α} (ha : K a a = 1) (hb : K b b = 1) :
    ‖K a b‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  simpa [RCLike.normSq_eq_def', pow_two, ha, hb] using
    isPositiveDefiniteKernel_normSq_le hK a b

/-! ### Bounds for subtraction kernels -/

section SubtractionKernel

variable {V : Type*} [AddGroup V] {ψ : V → 𝕜}

/-- The value at `0` of a function with positive-definite subtraction kernel has nonnegative
real part. -/
theorem map_zero_re_nonneg_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) :
    0 ≤ RCLike.re (ψ 0) := by
  have h : (0 : 𝕜) ≤ ψ 0 := by
    simpa using isPositiveDefiniteKernel_apply_self_nonneg hpd 0
  exact (RCLike.nonneg_iff.mp h).1

/-- The value at `0` of a function with positive-definite subtraction kernel is real. -/
theorem map_zero_eq_ofReal_re_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) :
    ψ 0 = ((RCLike.re (ψ 0) : ℝ) : 𝕜) := by
  have h : (0 : 𝕜) ≤ ψ 0 := by
    simpa using isPositiveDefiniteKernel_apply_self_nonneg hpd 0
  simpa [(RCLike.nonneg_iff.mp h).2] using (RCLike.re_add_im (ψ 0)).symm

/-- A function with positive-definite subtraction kernel is conjugate-symmetric under negation:
`ψ (-v) = conj (ψ v)`. This is the Hermitian symmetry of the kernel, read along the diagonal
translate `(v, 0)`. -/
theorem map_neg_eq_conj_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) (v : V) :
    ψ (-v) = conj (ψ v) := by
  simpa using (isPositiveDefiniteKernel_conj_symm hpd v 0).symm

/-- A function with positive-definite subtraction kernel is uniformly bounded by the real part
of its value at `0`. -/
theorem norm_apply_le_map_zero_re_of_isPositiveDefiniteKernel
    (hpd : IsPositiveDefiniteKernel fun a b : V => ψ (a - b)) (z : V) :
    ‖ψ z‖ ≤ RCLike.re (ψ 0) := by
  have h := isPositiveDefiniteKernel_normSq_le hpd z 0
  simp only [sub_zero, sub_self, RCLike.normSq_eq_def'] at h
  refine le_of_sq_le_sq ?_ (map_zero_re_nonneg_of_isPositiveDefiniteKernel hpd)
  calc ‖ψ z‖ ^ 2 ≤ RCLike.re (ψ 0) * RCLike.re (ψ 0) := h
    _ = RCLike.re (ψ 0) ^ 2 := (sq (RCLike.re (ψ 0))).symm

end SubtractionKernel

end TauCeti
