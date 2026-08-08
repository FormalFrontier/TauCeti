/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Algebra.BigOperators.Fin

/-!
# Block averages of a real-valued process

The empirical mean of a process over a finite selection of coordinates, with its elementary
algebra. Nothing here involves a measure: `blockAverage X k` is a function of `ω`, and the three
lemmas below are the pointwise formula, the scaled-sum normal form, and the value on a constant
block.

It also carries the two standard selections — `prefixAverage X n` over the first `n` coordinates
and `followingAverage X n` over the `n` coordinates after them — with their pointwise formulas.
These are likewise measure-free.

Measure-theoretic facts about all three — square-integrability, conditional expectations, variances
and covariances under contractability — live with the `L²` averaging library in
`Exchangeability/L2/BlockAverages.lean` and `Exchangeability/L2/LongTailAverages.lean`, which import
this module. Keeping the definitions here means a route that only needs the algebra does not import
the `L²` machinery to get them: the Koopman route needs `prefixAverage` to state its Birkhoff
bridge, and has no `L²` content of its own.
-/

public section

noncomputable section

open Finset
open scoped BigOperators

namespace TauCeti

namespace Probability

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- The **block average** of a real-valued process `X` over a finite selection `k : Fin n → ℕ`:
the empirical mean `n⁻¹ • ∑ i, X (k i)` of the block `(X (k i))ᵢ`. -/
def blockAverage (X : ℕ → Ω → ℝ) {n : ℕ} (k : Fin n → ℕ) : Ω → ℝ :=
  𝔼 i, X (k i)

/-- **The pointwise formula for a block average**: at each `ω` it is the normalised finite sum
`n⁻¹ * ∑ i, X (k i) ω`. -/
@[simp]
theorem blockAverage_apply {n : ℕ} (k : Fin n → ℕ) (ω : Ω) :
    blockAverage X k ω = (n : ℝ)⁻¹ * ∑ i, X (k i) ω := by
  rw [blockAverage, Finset.expect_apply, Fintype.expect_eq_sum_div_card]
  simp [div_eq_inv_mul]

/-- A block average as a real-scaled finite sum. -/
theorem blockAverage_eq_sum {n : ℕ} (k : Fin n → ℕ) :
    blockAverage X k = (n : ℝ)⁻¹ • ∑ i, X (k i) := by
  ext ω
  simp

/-- **A block average of a constant block.** If every coordinate of a nonempty block takes the
value `c` at `ω`, then so does the block average: the normalisation `n⁻¹` cancels the `n` terms. -/
theorem blockAverage_apply_of_forall_eq {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ} {ω : Ω} {c : ℝ}
    (h : ∀ i, X (k i) ω = c) : blockAverage X k ω = c := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [blockAverage, Finset.expect_apply, Finset.expect_congr rfl fun i _ => h i,
    Fintype.expect_const]

/-- The average of the first `n` coordinates of a real-valued process. -/
def prefixAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => i

/-- The average of the `n` coordinates immediately following the first `n` coordinates. -/
def followingAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => n + i

/-- A prefix average is the block average over the selection `i ↦ i`. -/
theorem prefixAverage_def (X : ℕ → Ω → ℝ) (n : ℕ) :
    prefixAverage X n = blockAverage X fun i : Fin n => (i : ℕ) := (rfl)

/-- A following-block average is the block average over the selection `i ↦ n + i`. -/
theorem followingAverage_def (X : ℕ → Ω → ℝ) (n : ℕ) :
    followingAverage X n = blockAverage X fun i : Fin n => n + (i : ℕ) := (rfl)

/-- **The pointwise formula for a prefix average.** -/
@[simp]
theorem prefixAverage_apply (n : ℕ) (ω : Ω) :
    prefixAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω := by
  simp [prefixAverage, blockAverage_apply]

/-- **The pointwise formula for a following-block average.** -/
@[simp]
theorem followingAverage_apply (n : ℕ) (ω : Ω) :
    followingAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X (n + i) ω := by
  simp [followingAverage, blockAverage_apply]

/-- **A product of block averages is an average of products.** Purely algebraic: the product of
sums distributes by `Fintype.prod_sum`, and the normalisations multiply. Disjointness of the
selections plays no role here — it matters only for what the individual terms mean. -/
theorem prod_blockAverage_eq_expect {m N : ℕ} (Y : Fin m → ℕ → Ω → ℝ) (k : Fin m → Fin N → ℕ)
    (ω : Ω) :
    (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = 𝔼 js : Fin m → Fin N, ∏ i : Fin m, Y i (k i (js i)) ω := by
  classical
  have hL : (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = ((N : ℝ)⁻¹) ^ m * ∏ i : Fin m, ∑ j : Fin N, Y i (k i j) ω := by
    simp [blockAverage_apply, Finset.prod_mul_distrib]
  rw [hL, Fintype.prod_sum fun i (j : Fin N) => Y i (k i j) ω, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, card_univ, div_eq_inv_mul]
  push_cast
  simp [inv_pow]

/-- **A Birkhoff average is a prefix average of the iterated observable.** For any self-map `T` and
any real observable `F`, `birkhoffAverage ℝ T F n` is the prefix average of `i ↦ F ∘ T^[i]`.

Nothing about the shift or about coordinate observables enters: both sides are the same
normalised sum. -/
theorem birkhoffAverage_eq_prefixAverage {Ω : Type*} (T : Ω → Ω) (F : Ω → ℝ) (n : ℕ) :
    birkhoffAverage ℝ T F n = prefixAverage (fun i (x : Ω) => F (T^[i] x)) n := by
  funext x
  rw [birkhoffAverage, birkhoffSum, prefixAverage_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_range fun i => F (T^[i] x)

end Probability

end TauCeti
