/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Self-convolution coefficients of a formal power series

`PowerSeries.coeff_mul` gives the coefficients of a product as a sum over `Finset.antidiagonal`.
For a recursion that reads off one coefficient from strictly earlier ones the equivalent sum over
`Finset.range` is what is wanted, so this file names the two shapes that occur, for a square and
for a cube, and records the translation.

Both are stated for an arbitrary coefficient function `f : ℕ → R` rather than for the
coefficients of a given series: the congruence lemmas compare two such functions, and the
truncation lemmas feed in a modified one.

The load-bearing facts are `PowerSeries.selfConvTwo_congr` and `PowerSeries.selfConvThree_congr`.
When `f 0 = 0` the convolution at index `n` depends only on the values of `f` strictly below `n`,
because the extreme terms of the sum each carry a factor `f 0`. That is what makes a recursion
defined through these convolutions well founded.

## Main definitions

* `PowerSeries.selfConvTwo`, `PowerSeries.selfConvThree`: the `Finset.range`-form convolution
  sums computing the coefficients of a square and of a cube.

## Main results

* `PowerSeries.selfConvTwo_def`, `PowerSeries.selfConvThree_def`: the defining formulas, as
  named lemmas. Rewrite with these rather than unfolding the definitions.
* `PowerSeries.coeff_pow_two_eq_selfConvTwo`,
  `PowerSeries.coeff_pow_three_eq_selfConvThree`: those sums do compute the coefficients of
  `w ^ 2` and `w ^ 3`.
* `PowerSeries.selfConvTwo_congr_le`, `PowerSeries.selfConvThree_congr_le`: the convolution at
  `m` depends only on the values of the function on `[0, m]`. No hypothesis is needed.
* `PowerSeries.selfConvTwo_congr`, `PowerSeries.selfConvThree_congr`: for a function vanishing at
  `0`, that bound sharpens to the values strictly below `n`.
* `PowerSeries.selfConvTwo_truncate`, `PowerSeries.selfConvThree_truncate` and their
  `_of_lt` companions: truncating the function above `n` leaves the convolution unchanged at `n`
  (needing `f 0 = 0`) and at every smaller index (needing nothing).
* `PowerSeries.selfConvTwo_eq_zero`, `PowerSeries.selfConvThree_eq_zero`: a function vanishing
  below `d` has square vanishing below `2 * d` and cube vanishing below `3 * d`.

## Provenance

Adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned
by `TauCetiRoadmap/EllipticCurves/README.md` at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/FormalGroup.lean`, declarations `conv₂` and `conv₃` together with the coefficient
lemmas `coeff_formalW_sq` and `coeff_formalW_cube`.

Changes from the source. The source states its two convolution-coefficient lemmas only for its
`formalW`, although neither proof uses anything about that series; they are stated here for an
arbitrary series. The truncation lemmas likewise assumed `formalW`, and are stated here for any
`f` vanishing at `0`, as consequences of the sharper congruence lemmas. The source works
throughout over a `CommRing`; nothing here needs more than a `Semiring`.
-/

public section

open Finset

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The `n`-th coefficient of the square of the series with coefficients `f`. -/
def selfConvTwo (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), f i * f (n - i)

/-- The defining formula for `selfConvTwo`. -/
theorem selfConvTwo_def (f : ℕ → R) (n : ℕ) :
    selfConvTwo f n = ∑ i ∈ range (n + 1), f i * f (n - i) := (rfl)

/-- The `n`-th coefficient of the cube of the series with coefficients `f`. -/
def selfConvThree (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), f i * f j * f (n - i - j)

/-- The defining formula for `selfConvThree`. -/
theorem selfConvThree_def (f : ℕ → R) (n : ℕ) :
    selfConvThree f n = ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), f i * f j * f (n - i - j) :=
  (rfl)

/-- `selfConvTwo` computes the coefficients of a square. -/
theorem coeff_pow_two_eq_selfConvTwo (w : PowerSeries R) (n : ℕ) :
    coeff n (w ^ 2) = selfConvTwo (fun k => coeff k w) n := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => coeff i w * coeff j w) n]
  rfl

/-- `selfConvThree` computes the coefficients of a cube. -/
theorem coeff_pow_three_eq_selfConvThree (w : PowerSeries R) (n : ℕ) :
    coeff n (w ^ 3) = selfConvThree (fun k => coeff k w) n := by
  rw [pow_succ' w 2, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (M := R) (fun i j => coeff i w * coeff j (w ^ 2)) n]
  simp only [coeff_pow_two_eq_selfConvTwo, selfConvThree, selfConvTwo, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

/-- `selfConvTwo f n` depends only on the values of `f` strictly below `n`, provided `f`
vanishes at `0`: the two extreme terms of the convolution each carry a factor `f 0`. -/
theorem selfConvTwo_congr {f g : ℕ → R} (hf : f 0 = 0) (hg : g 0 = 0) {n : ℕ}
    (h : ∀ m, m < n → f m = g m) : selfConvTwo f n = selfConvTwo g n := by
  simp only [selfConvTwo]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  by_cases hi' : i < n
  · by_cases hk : n - i < n
    · rw [h i hi', h _ hk]
    · have : i = 0 := by omega
      subst this
      simp [hf, hg]
  · have : i = n := by omega
    subst this
    simp [hf, hg]

/-- The cube analogue of `selfConvTwo_congr`. -/
theorem selfConvThree_congr {f g : ℕ → R} (hf : f 0 = 0) (hg : g 0 = 0) {n : ℕ}
    (h : ∀ m, m < n → f m = g m) : selfConvThree f n = selfConvThree g n := by
  simp only [selfConvThree]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  by_cases hi' : i < n
  · by_cases hj' : j < n
    · by_cases hk : n - i - j < n
      · rw [h i hi', h j hj', h _ hk]
      · have : i = 0 := by omega
        subst this
        simp [hf, hg]
    · have : i = 0 := by omega
      subst this
      simp [hf, hg]
  · have : i = n := by omega
    subst this
    simp [hf, hg]

/-- `selfConvTwo f m` depends only on the values of `f` on `[0, m]`. Unlike `selfConvTwo_congr`
this needs no hypothesis on `f`, because every index occurring in the sum is at most `m`; the
vanishing hypothesis there buys the strict bound `< m` instead. -/
theorem selfConvTwo_congr_le {f g : ℕ → R} {m : ℕ} (h : ∀ k, k ≤ m → f k = g k) :
    selfConvTwo f m = selfConvTwo g m := by
  simp only [selfConvTwo]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [h i hi, h _ (by omega)]

/-- The cube analogue of `selfConvTwo_congr_le`. -/
theorem selfConvThree_congr_le {f g : ℕ → R} {m : ℕ} (h : ∀ k, k ≤ m → f k = g k) :
    selfConvThree f m = selfConvThree g m := by
  simp only [selfConvThree]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  rw [h i (by omega), h j (by omega), h _ (by omega)]

/-- Truncating `f` above `n` does not change `selfConvTwo f n`, when `f 0 = 0`. -/
theorem selfConvTwo_truncate (f : ℕ → R) (hf : f 0 = 0) (n : ℕ) :
    selfConvTwo (fun m => if m < n then f m else 0) n = selfConvTwo f n :=
  selfConvTwo_congr (by by_cases h : 0 < n <;> simp [h, hf]) hf fun m hm => by simp [hm]

/-- Below the truncation index no hypothesis on `f` is needed. -/
theorem selfConvTwo_truncate_of_lt (f : ℕ → R) {k n : ℕ} (h : k < n) :
    selfConvTwo (fun m => if m < n then f m else 0) k = selfConvTwo f k :=
  selfConvTwo_congr_le fun j hj => by simp [show j < n by omega]

/-- Truncating `f` above `n` does not change `selfConvThree f n`, when `f 0 = 0`. -/
theorem selfConvThree_truncate (f : ℕ → R) (hf : f 0 = 0) (n : ℕ) :
    selfConvThree (fun m => if m < n then f m else 0) n = selfConvThree f n :=
  selfConvThree_congr (by by_cases h : 0 < n <;> simp [h, hf]) hf fun m hm => by simp [hm]

/-- The cube analogue of `selfConvTwo_truncate_of_lt`. -/
theorem selfConvThree_truncate_of_lt (f : ℕ → R) {k n : ℕ} (h : k < n) :
    selfConvThree (fun m => if m < n then f m else 0) k = selfConvThree f k :=
  selfConvThree_congr_le fun j hj => by simp [show j < n by omega]

/-- A series vanishing below degree `d` has square vanishing below degree `2 * d`: in every term
of the convolution one of the two factors sits at an index below `d`. -/
theorem selfConvTwo_eq_zero {f : ℕ → R} {d : ℕ} (hf : ∀ k, k < d → f k = 0) {n : ℕ}
    (hn : n < 2 * d) : selfConvTwo f n = 0 := by
  simp only [selfConvTwo]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi
  by_cases h : i < d
  · rw [hf i h, zero_mul]
  · rw [hf (n - i) (by omega), mul_zero]

/-- A series vanishing below degree `d` has cube vanishing below degree `3 * d`. -/
theorem selfConvThree_eq_zero {f : ℕ → R} {d : ℕ} (hf : ∀ k, k < d → f k = 0) {n : ℕ}
    (hn : n < 3 * d) : selfConvThree f n = 0 := by
  simp only [selfConvThree]
  refine Finset.sum_eq_zero fun i hi => ?_
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
  by_cases h : i < d
  · rw [hf i h, zero_mul, zero_mul]
  · by_cases h' : j < d
    · rw [hf j h', mul_zero, zero_mul]
    · rw [hf (n - i - j) (by omega), mul_zero]

end PowerSeries
