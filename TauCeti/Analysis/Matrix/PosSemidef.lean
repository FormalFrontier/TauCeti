/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Analytic bounds for positive-semidefinite matrices

This file supplements the foundational API in `TauCeti.LinearAlgebra.Matrix.PosSemidef` with
scalar Cauchy--Schwarz and vanishing bounds for `RCLike`-valued positive-semidefinite matrices.

The results apply in particular to positive-definite kernels, represented directly as matrices,
but do not depend on Tau Ceti's positive-definite-function theory.

They supply the matrix prerequisites for Part C of the `OneParameterSemigroups` roadmap, including
the positive-definite-function/kernel correspondence and the GNS/Kolmogorov decomposition. No
Mathlib code is vendored.

## Main declarations

* `Matrix.PosSemidef.normSq_le`: scalar Cauchy--Schwarz.
* `Matrix.PosSemidef.eq_zero_of_apply_self_eq_zero_left` and
  `Matrix.PosSemidef.eq_zero_of_apply_self_eq_zero_right`: zero-diagonal vanishing.
* `Matrix.PosSemidef.norm_le_one_of_apply_self_eq_one`: the normalized scalar bound.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace Matrix.PosSemidef

universe u v

variable {α : Type v}

variable {𝕜 : Type u} [RCLike 𝕜]

/-- The `2 × 2` principal submatrix at two indices is positive semidefinite. -/
private theorem finTwo_posSemidef {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a b : α) :
    (Matrix.of fun i j : Fin 2 => K (![a, b] i) (![a, b] j)).PosSemidef := by
  have h := hK.submatrix (fun i : Fin 2 => ![a, b] i)
  have heq : Matrix.submatrix (Matrix.of K) (fun i : Fin 2 => ![a, b] i)
      (fun i : Fin 2 => ![a, b] i) =
      Matrix.of fun i j : Fin 2 => K (![a, b] i) (![a, b] j) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
  exact heq ▸ h

/-- Scalar Cauchy--Schwarz for an `RCLike`-valued positive-semidefinite matrix. -/
theorem normSq_le {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a b : α) :
    RCLike.normSq (K a b) ≤ RCLike.re (K a a) * RCLike.re (K b b) := by
  have hsymm (x y : α) : conj (K x y) = K y x := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply y x
  let A : Matrix (Fin 2) (Fin 2) 𝕜 := Matrix.of fun i j => K (![a, b] i) (![a, b] j)
  have hA : A.PosSemidef := finTwo_posSemidef hK a b
  have hdet : 0 ≤ A.det := Matrix.PosSemidef.det_nonneg hA
  have hdet_re : 0 ≤ RCLike.re A.det := by
    simpa using (RCLike.le_iff_re_im.mp hdet).1
  have hconj : K b a = conj (K a b) := (hsymm a b).symm
  have haa_im : RCLike.im (K a a) = 0 := RCLike.conj_eq_iff_im.mp (hsymm a a)
  have hbb_im : RCLike.im (K b b) = 0 := RCLike.conj_eq_iff_im.mp (hsymm b b)
  have hdet_eval :
      RCLike.re A.det =
        RCLike.re (K a a) * RCLike.re (K b b) - RCLike.normSq (K a b) := by
    simp [A, Matrix.det_fin_two, hconj, RCLike.normSq_apply, haa_im, hbb_im]
  nlinarith

/-- A zero diagonal entry forces the corresponding row entry to vanish. -/
theorem eq_zero_of_apply_self_eq_zero_left {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (ha : K a a = 0) : K a b = 0 := by
  have hnorm := hK.normSq_le a b
  have hdiag : RCLike.re (K a a) * RCLike.re (K b b) = 0 := by simp [ha]
  have hnorm_zero : RCLike.normSq (K a b) = 0 :=
    le_antisymm (by simpa [hdiag] using hnorm) (RCLike.normSq_nonneg _)
  exact RCLike.normSq_eq_zero.mp hnorm_zero

/-- A zero diagonal entry forces the corresponding column entry to vanish. -/
theorem eq_zero_of_apply_self_eq_zero_right {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (hb : K b b = 0) : K a b = 0 := by
  have hba := hK.eq_zero_of_apply_self_eq_zero_left (a := b) (b := a) hb
  have hconj : conj (K a b) = K b a := by
    simpa only [starRingEnd_apply] using hK.isHermitian.apply b a
  rw [hba] at hconj
  have := congrArg conj hconj
  simpa using this

/-- If two diagonal entries are `1`, then the corresponding off-diagonal entry has norm at most
`1`. -/
theorem norm_le_one_of_apply_self_eq_one {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) {a b : α} (ha : K a a = 1) (hb : K b b = 1) :
    ‖K a b‖ ≤ 1 := by
  refine le_of_sq_le_sq ?_ zero_le_one
  simpa [RCLike.normSq_eq_def', pow_two, ha, hb] using hK.normSq_le a b

end Matrix.PosSemidef
