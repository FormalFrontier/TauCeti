/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.mul_apply` expands a product entry as a sum; it also re-exports
-- `Mathlib.Data.Matrix.Diagonal`, which supplies `Matrix.diagonal_apply_eq`.
public import Mathlib.Data.Matrix.Mul

/-!
# Divisibility of matrix entries under multiplication

A common divisor of the entries of a matrix survives multiplication on either side: every
entry of `P * A * Q` is an `S`-combination of entries of `A`, so anything dividing all of
those divides all of these.

Nothing here needs invertibility, a square shape, or a diagonal target — only that the
products are conformable — so the statements are at `CommSemiring` and rectangular. The
Smith-normal-form theory consumes both, but neither has a Smith-normal-form hypothesis and
neither should require importing that theory to reach.

## Main results

* `Matrix.dvd_mul_mul_apply`: a common divisor of the entries of `A` divides every entry of
  `P * A * Q`.
* `Matrix.dvd_diag_of_dvd_entries`: if `L * A * R` is `Matrix.diagonal d`, then a common
  divisor of the entries of `A` divides every `d k`.
-/

public section

namespace Matrix

variable {l m n o S : Type*} [CommSemiring S]

/-- **A common divisor of the entries survives two-sided multiplication.** If `c` divides
every entry of `A`, then it divides every entry of `P * A * Q`, since each entry of the
product is an `S`-combination of entries of `A`. -/
theorem dvd_mul_mul_apply [Fintype m] [Fintype n] {A : Matrix m n S} {c : S}
    (hc : ∀ i j, c ∣ A i j) (P : Matrix l m S) (Q : Matrix n o S) (i : l) (j : o) :
    c ∣ (P * A * Q) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ ↦ ?_
  rw [Matrix.mul_apply]
  exact Dvd.dvd.mul_right (Finset.dvd_sum fun p _ ↦ (hc p k).mul_left _) _

/-- **Every common divisor of the entries divides every diagonal entry.** Each `d k` is the
`(k, k)` entry of `L * A * R`, hence an `S`-combination of the entries of `A`. -/
theorem dvd_diag_of_dvd_entries [Fintype m] [Fintype n] [DecidableEq o] (A : Matrix m n S)
    (c : S) (d : o → S) (L : Matrix o m S) (R : Matrix n o S)
    (h : L * A * R = Matrix.diagonal d) (hc : ∀ i j, c ∣ A i j) (k : o) : c ∣ d k := by
  have hkk := congr_fun₂ h k k
  rw [Matrix.diagonal_apply_eq] at hkk
  exact hkk ▸ dvd_mul_mul_apply hc L R k k

end Matrix
