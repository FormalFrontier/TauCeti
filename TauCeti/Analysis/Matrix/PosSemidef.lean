/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Analytic bounds for positive-semidefinite matrices

This file supplements the foundational API in `TauCeti.LinearAlgebra.Matrix.PosSemidef` with
scalar Cauchy--Schwarz and vanishing bounds for `RCLike`-valued positive-semidefinite matrices,
together with the resulting estimate for *Hankel* matrices: a bounded sequence whose Hankel matrix
`(m, n) ↦ a (m + n)` is positive semidefinite cannot increase at the first step.

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
* `TauCeti.sub_nonneg_of_posSemidef_hankel`: a bounded positive-semidefinite Hankel sequence does
  not increase at the first step.

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

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Bounded positive-semidefinite Hankel sequences -/

/-- The numerical core of the Hankel estimate: a bounded sequence of reals whose squares satisfy
the Cauchy--Schwarz inequality `b n ^ 2 ≤ b 0 * b (n + n)` cannot increase at the first step. If it
did, the ratio `r = b 1 / b 0` would exceed `1` and the doubling inequality would push
`b (2 ^ k)` past `b 0 * r ^ (2 ^ k)`, which is unbounded. -/
private theorem apply_one_le_apply_zero_of_sq_le_mul {b : ℕ → ℝ} {D : ℝ} (hb0 : 0 ≤ b 0)
    (hsq : ∀ n, b n ^ 2 ≤ b 0 * b (n + n)) (hbd : ∀ n, b n ≤ D) : b 1 ≤ b 0 := by
  rcases le_or_gt (b 1) (b 0) with hle | hlt
  · exact hle
  exfalso
  have hb0pos : 0 < b 0 := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · have h1 := hsq 1
      rw [← h] at h1
      nlinarith
  set r : ℝ := b 1 / b 0 with hr
  have hr1 : 1 < r := (one_lt_div hb0pos).mpr hlt
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have key : ∀ k : ℕ, b 0 * r ^ 2 ^ k ≤ b (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        have : b 0 * r = b 1 := by
          rw [hr, mul_div_cancel₀ _ hb0pos.ne']
        simpa using this.le
    | succ k ih =>
        have hpow : (0 : ℝ) < r ^ 2 ^ k := pow_pos hrpos _
        have hsplit : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        have hsq' := hsq (2 ^ k)
        have hrw : r ^ 2 ^ (k + 1) = (r ^ 2 ^ k) ^ 2 := by
          rw [hsplit, pow_add, sq]
        rw [hrw, hsplit]
        nlinarith [mul_pos hb0pos hpow]
  obtain ⟨k, hk⟩ := exists_nat_gt ((D / b 0 - 1) / (r - 1))
  have hkr : D / b 0 - 1 < k * (r - 1) := (div_lt_iff₀ (by linarith)).mp hk
  have hD : D < b 0 * (1 + k * (r - 1)) := by
    have h : D / b 0 < 1 + k * (r - 1) := by linarith
    rw [mul_comm]
    exact (div_lt_iff₀ hb0pos).mp h
  have hbern : 1 + k * (r - 1) ≤ r ^ k := by
    simpa using one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ r - 1) k
  have hmono : r ^ k ≤ r ^ 2 ^ k :=
    pow_le_pow_right₀ hr1.le (Nat.le_of_lt k.lt_two_pow_self)
  have hchain : b 0 * (1 + k * (r - 1)) ≤ D :=
    le_trans (le_trans (mul_le_mul_of_nonneg_left (hbern.trans hmono) hb0pos.le) (key k))
      (hbd _)
  linarith

/-- **A bounded positive-semidefinite Hankel sequence does not increase at the first step.**
If `(m, n) ↦ a (m + n)` is positive semidefinite and `a` is bounded in norm, then `a 1 ≤ a 0`
in the `RCLike` order. Cauchy--Schwarz alone gives `a n ^ 2 ≤ a 0 * a (2 n)`, and boundedness
rules out a ratio `a 1 / a 0` greater than `1`. -/
theorem sub_nonneg_of_posSemidef_hankel {a : ℕ → 𝕜} {D : ℝ}
    (ha : Matrix.PosSemidef fun m n : ℕ => a (m + n)) (hbd : ∀ n, ‖a n‖ ≤ D) :
    0 ≤ a 0 - a 1 := by
  have hreal : ∀ n, (starRingEnd 𝕜) (a n) = a n := by
    intro n
    simpa using ha.isHermitian.apply n 0
  have him : ∀ n, RCLike.im (a n) = 0 := fun n => RCLike.conj_eq_iff_im.mp (hreal n)
  set b : ℕ → ℝ := fun n => RCLike.re (a n) with hbdef
  have hnormSq : ∀ n, RCLike.normSq (a n) = b n ^ 2 := by
    intro n
    rw [RCLike.normSq_apply, him n]
    simp [hbdef, sq]
  have hb0 : 0 ≤ b 0 := by
    have h := ha.diag_nonneg (i := 0)
    simpa [hbdef] using (RCLike.nonneg_iff.mp (by simpa using h)).1
  have hsq : ∀ n, b n ^ 2 ≤ b 0 * b (n + n) := by
    intro n
    have h := ha.normSq_le 0 n
    simpa [hnormSq, hbdef] using h
  have hbdb : ∀ n, b n ≤ D := fun n =>
    le_trans (RCLike.re_le_norm (a n)) (hbd n)
  have hmain : b 1 ≤ b 0 := apply_one_le_apply_zero_of_sq_le_mul hb0 hsq hbdb
  rw [RCLike.nonneg_iff]
  constructor
  · simpa [hbdef] using sub_nonneg.mpr hmain
  · simp [him 0, him 1]

end TauCeti
