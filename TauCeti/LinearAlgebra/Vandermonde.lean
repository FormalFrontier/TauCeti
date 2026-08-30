/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Pi.Interval
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Summing Vandermonde determinants over a box of nested integer intervals

Let `x₀ ≤ x₁ ≤ ⋯ ≤ xₙ` be integers and let `y` range over the box of integer vectors with
`xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`, one interval for each consecutive pair.  Then

`n ! · ∑ y, det (vandermonde y) = det (vandermonde x)`,

which is `TauCeti.factorial_mul_sum_det_vandermonde`.  Unwinding the determinants, the product
`∏_{i < j} (yⱼ - yᵢ)` of the differences of an `n`-tuple, summed over the box, is `1 / n !` times
the corresponding product for the `(n + 1)`-tuple that bounds it.

The identity drives the branching recursion for the Weyl dimension formula of `GL n`: the
interlacing condition indexing the constituents of an irreducible restricted to `GL (n - 1)` is
exactly such a box, and the two Vandermonde products are the two Weyl dimension numerators.

## The proof

Three moves; only the last uses the ordering hypothesis.

*The falling-factorial basis.*  The falling factorials `descPochhammer ℤ j` are monic of degree
`j`, so Mathlib's `Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde` rewrites
`det (vandermonde y)` as the determinant of the matrix `(descPochhammer ℤ j).eval (yᵢ)`.  The
point of the change of basis is that falling factorials, unlike powers, have a closed-form
discrete antiderivative, `TauCeti.sum_Icc_descPochhammer_eval`.

*Multilinearity.*  A determinant is multilinear in its rows and the box constrains the rows
independently, so the sum of the determinants over the box is the determinant of the matrix of
row sums (`MultilinearMap.map_sum_finset`).  Evaluating those row sums, and clearing the
denominators `1, 2, …, n` by a column scaling, produces the matrix of differences
`(descPochhammer ℤ (j+1)).eval (xᵢ₊₁) - (descPochhammer ℤ (j+1)).eval (xᵢ)`, whose determinant is
`n !` times the sum.

*A row reduction.*  That matrix of differences is what remains of the `(n+1) × (n+1)` matrix
`(descPochhammer ℤ j).eval (xᵢ)` after subtracting each row from its predecessor and deleting the
column `j = 0`, which is constant equal to `1`.  Multiplying on the left by the bidiagonal matrix
performing the subtraction contributes a factor `(-1)^{n+1}` to the determinant, and expanding the
product along its first column — where only the last entry survives — contributes the same sign,
so the two determinants agree.

## Main results

* `TauCeti.sum_Icc_descPochhammer_eval`: the discrete antiderivative of a falling factorial.
* `TauCeti.factorial_mul_sum_det_vandermonde`: **the box-sum identity for Vandermonde
  determinants.**
-/

public section

namespace TauCeti

open Finset Matrix Polynomial

/-! ### The discrete antiderivative of a falling factorial -/

/-- Shifting the argument of a falling factorial by one strips off its trailing linear factor:
the degree `m + 1` falling factorial at `x + 1` is `(x + 1)` times the degree `m` one at `x`. -/
private theorem descPochhammer_succ_eval_add_one (m : ℕ) (x : ℤ) :
    (descPochhammer ℤ (m + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℤ m).eval x := by
  rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one,
    add_sub_cancel_right]

/-- **The discrete derivative of a falling factorial**: the falling factorial of degree `m + 1`
increases by `m + 1` times the falling factorial of degree `m`.  This is the analogue of
`(x^{m+1})' = (m+1) x^m`, and the reason the falling factorials, not the powers, are the basis in
which a Vandermonde determinant can be summed over a range. -/
private theorem descPochhammer_eval_add_one_sub (m : ℕ) (x : ℤ) :
    (descPochhammer ℤ (m + 1)).eval (x + 1) - (descPochhammer ℤ (m + 1)).eval x
      = ((m : ℤ) + 1) * (descPochhammer ℤ m).eval x := by
  rw [descPochhammer_succ_eval_add_one, descPochhammer_succ_eval]
  ring

/-- Telescoping a sum of consecutive differences over an integer interval. -/
private theorem sum_Icc_sub_telescope (f : ℤ → ℤ) (p : ℤ) :
    ∀ q, p - 1 ≤ q → ∑ t ∈ Finset.Icc p q, (f (t + 1) - f t) = f (q + 1) - f p := by
  intro q hq
  induction q, hq using Int.leInduction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    norm_num
  | succ q hq ih =>
    have hins : Finset.Icc p (q + 1) = insert (q + 1) (Finset.Icc p q) := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc, not_and, not_le]; omega), ih]
    ring

/-- **The discrete antiderivative of a falling factorial.**  Summing the degree `m` falling
factorial over the integer range `p ≤ t < q` gives the difference of the degree `m + 1` falling
factorial at the endpoints, divided by `m + 1`; the statement clears that denominator.

The hypothesis `p ≤ q` is what makes the range a range: for `q < p` the sum is empty while the
right-hand side need not vanish. -/
theorem sum_Icc_descPochhammer_eval (m : ℕ) {p q : ℤ} (h : p ≤ q) :
    ((m : ℤ) + 1) * ∑ t ∈ Finset.Icc p (q - 1), (descPochhammer ℤ m).eval t
      = (descPochhammer ℤ (m + 1)).eval q - (descPochhammer ℤ (m + 1)).eval p := by
  have htel :=
    sum_Icc_sub_telescope (fun t => (descPochhammer ℤ (m + 1)).eval t) p (q - 1) (by omega)
  have hq : q - 1 + 1 = q := by omega
  rw [hq] at htel
  rw [Finset.mul_sum, ← htel]
  exact Finset.sum_congr rfl fun t _ => (descPochhammer_eval_add_one_sub m t).symm

/-! ### The box-sum identity -/

/-- The Vandermonde determinant of a node vector, computed in the falling-factorial basis: the
falling factorials are monic of degree `j`, so they give the same determinant as the powers. -/
private theorem det_vandermonde_eq_det_descPochhammer (m : ℕ) (y : Fin m → ℤ) :
    (Matrix.vandermonde y).det
      = (Matrix.of fun i j : Fin m => (descPochhammer ℤ (j : ℕ)).eval (y i)).det :=
  Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde y
    (fun j => descPochhammer ℤ (j : ℕ)) (fun j => descPochhammer_natDegree (R := ℤ) (j : ℕ))
    (fun j => monic_descPochhammer (R := ℤ) (j : ℕ))

/-- The one surviving term of a sum whose summand is supported on the index one step above a
given one. -/
private theorem sum_ite_val_eq_succ {m : ℕ} (i : Fin m) (f : Fin (m + 1) → ℤ) :
    (∑ k : Fin (m + 1), if (k : ℕ) = (i.castSucc : ℕ) + 1 then f k else 0) = f i.succ := by
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro k _ hk
    have hne : ¬ ((k : ℕ) = (i : ℕ) + 1) := fun h => hk (by ext; simpa using h)
    simp only [Fin.val_castSucc, ite_eq_right_iff]
    exact fun h => absurd h hne
  · simp

/-- There is no index one step above the last one, so the corresponding sum is empty. -/
private theorem sum_ite_val_eq_last_succ {m : ℕ} (f : Fin (m + 1) → ℤ) :
    (∑ k : Fin (m + 1), if (k : ℕ) = ((Fin.last m : Fin (m + 1)) : ℕ) + 1 then f k else 0)
      = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := k.isLt
  simp only [Fin.val_last, ite_eq_right_iff]
  intro h
  omega

/-- **The row reduction.**  The `n × n` matrix of differences of falling factorials at the
consecutive nodes `xᵢ`, `xᵢ₊₁` has the same determinant as the `(n+1) × (n+1)` Vandermonde matrix
of the nodes themselves: it is obtained from the falling-factorial form of the latter by
subtracting each row from its predecessor and deleting the constant column `j = 0`. -/
private theorem det_descPochhammer_sub_eq_det_vandermonde {n : ℕ} (x : Fin (n + 1) → ℤ) :
    (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc)).det
      = (Matrix.vandermonde x).det := by
  classical
  -- `N` is the Vandermonde matrix of `x` in the falling-factorial basis, and `E` is the bidiagonal
  -- matrix subtracting each row of `N` from its predecessor.
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
    Matrix.of fun i j => (descPochhammer ℤ (j : ℕ)).eval (x i)
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i k =>
    (if (k : ℕ) = (i : ℕ) + 1 then (1 : ℤ) else 0) - (if k = i then 1 else 0)
  have hN : ∀ i j, N i j = (descPochhammer ℤ (j : ℕ)).eval (x i) := fun _ _ => rfl
  have hE : ∀ i k, E i k
      = (if (k : ℕ) = (i : ℕ) + 1 then (1 : ℤ) else 0) - (if k = i then 1 else 0) :=
    fun _ _ => rfl
  have hEN : ∀ i j : Fin (n + 1),
      (E * N) i j
        = (∑ k : Fin (n + 1), if (k : ℕ) = (i : ℕ) + 1 then N k j else 0) - N i j := by
    intro i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin (n + 1), E i k * N k j
        = (if (k : ℕ) = (i : ℕ) + 1 then N k j else 0) - (if k = i then N k j else 0) := by
      intro k
      rw [hE]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib]
    congr 1
    simp
  have hEupper : E.IsUpperTriangular := by
    intro i k hki
    have hk : (k : ℕ) < (i : ℕ) := hki
    have h1 : ¬ ((k : ℕ) = (i : ℕ) + 1) := by omega
    have h2 : ¬ (k = i) := by rintro rfl; omega
    rw [hE]
    simp [h1, h2]
  have hEdet : E.det = (-1 : ℤ) ^ (n + 1) := by
    rw [Matrix.det_of_isUpperTriangular hEupper]
    have hdiag : ∀ i : Fin (n + 1), E i i = -1 := by
      intro i
      rw [hE]
      simp
    rw [Finset.prod_congr rfl fun i _ => hdiag i]
    simp
  -- The column `j = 0` of `N` is constant equal to `1`, so `E * N` has a single nonzero entry
  -- there, in its last row.
  have hcol : ∀ i : Fin (n + 1), N i 0 = 1 := by
    intro i
    rw [hN]
    simp
  have hcastSucc : ∀ (i : Fin n) (j : Fin (n + 1)),
      (E * N) i.castSucc j = N i.succ j - N i.castSucc j := by
    intro i j
    rw [hEN, sum_ite_val_eq_succ]
  have hlast : (E * N) (Fin.last n) 0 = -1 := by
    rw [hEN, sum_ite_val_eq_last_succ, hcol]
    ring
  have hsubmat : (E * N).submatrix (Fin.last n).succAbove Fin.succ
      = Matrix.of fun i j : Fin n =>
          (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
            - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc) := by
    ext i j
    rw [Matrix.submatrix_apply, Fin.succAbove_last, hcastSucc, hN, hN]
    simp
  have hdetEN : (E * N).det = (-1 : ℤ) ^ (n + 1) *
      (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc)).det := by
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last n)]
    · rw [hlast, hsubmat, Fin.val_last]
      ring
    · intro i _ hi
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      rw [hcastSucc]
      simp only [hcol]
      ring
    · simp
  -- Both readings of `det (E * N)` carry the same sign, which therefore cancels.
  have hdetN : N.det = (Matrix.vandermonde x).det :=
    (det_vandermonde_eq_det_descPochhammer (n + 1) x).symm
  rw [Matrix.det_mul, hEdet, hdetN] at hdetEN
  exact (mul_left_cancel₀ (pow_ne_zero (n + 1) (by norm_num : (-1 : ℤ) ≠ 0)) hdetEN).symm

/-- Clearing the denominators `1, 2, …, n` of the discrete antiderivatives is a column scaling,
whose determinant is `n !`. -/
private theorem prod_fin_add_one_eq_factorial (n : ℕ) :
    (∏ j : Fin n, (((j : ℕ) : ℤ) + 1)) = (Nat.factorial n : ℤ) := by
  have hcast : ∀ k : ℕ, ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by
    intro k
    push_cast
    ring
  rw [Fin.prod_univ_eq_prod_range fun k : ℕ => ((k : ℤ) + 1)]
  simp only [hcast, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

/-- **Summing Vandermonde determinants over a box of nested intervals.**  For integers
`x₀ ≤ x₁ ≤ ⋯ ≤ xₙ`, the Vandermonde determinant of `y`, summed over all integer vectors with
`xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`, is the Vandermonde determinant of `x` divided by `n !`; the statement clears
that denominator, so it is an identity over `ℤ`.

The hypothesis is exactly what makes each interval a range of summation; the nodes are otherwise
arbitrary integers, of either sign. -/
theorem factorial_mul_sum_det_vandermonde {n : ℕ} (x : Fin (n + 1) → ℤ)
    (hx : ∀ i : Fin n, x i.castSucc ≤ x i.succ) :
    (Nat.factorial n : ℤ) *
        ∑ y ∈ Finset.Icc (fun i : Fin n => x i.castSucc) (fun i : Fin n => x i.succ - 1),
          (Matrix.vandermonde y).det
      = (Matrix.vandermonde x).det := by
  classical
  -- Multilinearity of the determinant in the rows, used in every row at once: a term of the
  -- expansion is a choice of one summand in each row, so the terms are indexed by the box.
  have hbox : (Matrix.of fun i j : Fin n =>
        ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1), (descPochhammer ℤ (j : ℕ)).eval t).det
      = ∑ y ∈ Fintype.piFinset fun i : Fin n => Finset.Icc (x i.castSucc) (x i.succ - 1),
          (Matrix.of fun i j : Fin n => (descPochhammer ℤ (j : ℕ)).eval (y i)).det := by
    have key := (Matrix.detRowAlternating (R := ℤ) (n := Fin n)).toMultilinearMap.map_sum_finset
      (A := fun i : Fin n => Finset.Icc (x i.castSucc) (x i.succ - 1))
      (g := fun (_ : Fin n) (t : ℤ) (j : Fin n) => (descPochhammer ℤ (j : ℕ)).eval t)
    have hrow : (fun i : Fin n => ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
          fun j : Fin n => (descPochhammer ℤ (j : ℕ)).eval t)
        = fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1), (descPochhammer ℤ (j : ℕ)).eval t := by
      funext i j
      exact Finset.sum_apply j _ _
    rw [hrow] at key
    exact key
  have hsum : (∑ y ∈ Finset.Icc (fun i : Fin n => x i.castSucc) (fun i : Fin n => x i.succ - 1),
      (Matrix.vandermonde y).det)
      = (Matrix.of fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
            (descPochhammer ℤ (j : ℕ)).eval t).det := by
    rw [hbox]
    exact Finset.sum_congr rfl fun y _ => det_vandermonde_eq_det_descPochhammer n y
  have hscale : (Matrix.of fun i j : Fin n =>
        (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.succ)
          - (descPochhammer ℤ ((j : ℕ) + 1)).eval (x i.castSucc))
      = (Matrix.of fun i j : Fin n =>
          ∑ t ∈ Finset.Icc (x i.castSucc) (x i.succ - 1),
            (descPochhammer ℤ (j : ℕ)).eval t)
        * Matrix.diagonal fun j : Fin n => ((j : ℕ) : ℤ) + 1 := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.of_apply, Matrix.of_apply, mul_comm]
    exact (sum_Icc_descPochhammer_eval (j : ℕ) (hx i)).symm
  have hdet := det_descPochhammer_sub_eq_det_vandermonde x
  rw [hscale, Matrix.det_mul, Matrix.det_diagonal, prod_fin_add_one_eq_factorial] at hdet
  rw [hsum, mul_comm, hdet]

end TauCeti
