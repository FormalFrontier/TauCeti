/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages

/-!
# Long averages and following tail averages

This file proves the `l2_bound_long_vs_tail` milestone from Layer 3 of the Exchangeability
roadmap.  It specializes the general two-window estimate for a contractable real-valued process
to the two canonical adjacent blocks

```text
{0, ..., n - 1}       and       {n, ..., 2 * n - 1}.
```

The resulting exact identity says that the squared `L²` distance between the prefix average
and the following tail average is `2 * (v - c) / n`, where `v` is the common coordinate
variance and `c` is the common off-diagonal covariance.  In particular this distance tends to
zero as the block length tends to infinity.  This is the long-average versus tail-average input
for the later weighted-sum convergence argument.

The proof uses the preceding Tau Ceti two-window identity
`Contractable.integral_sq_blockAverage_sub_of_disjoint`; the elementary limit is Mathlib's
`tendsto_one_div_add_atTop_nhds_zero_nat`.  The mathematical formulation follows Kallenberg,
*Probabilistic Symmetries and Invariance Principles* (Springer, 2005), Chapter 1, around
Theorem 1.1.  No material from `cameronfreer/exchangeability` is reused.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The average of the first `n` coordinates of a real-valued process. -/
def prefixAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => i

/-- The average of the `n` coordinates immediately following the first `n` coordinates. -/
def followingAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => n + i

omit [MeasurableSpace Ω] in
@[simp]
theorem prefixAverage_apply (n : ℕ) (ω : Ω) :
    prefixAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω := by
  simp [prefixAverage, blockAverage_apply]

omit [MeasurableSpace Ω] in
@[simp]
theorem followingAverage_apply (n : ℕ) (ω : Ω) :
    followingAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X (n + i) ω := by
  simp [followingAverage, blockAverage_apply]

/-- The prefix selection is injective. -/
private theorem prefixSelection_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (i : ℕ)) :=
  Fin.val_injective

/-- The following-block selection is injective. -/
private theorem followingSelection_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => n + (i : ℕ)) := by
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-- The prefix and following-block selections have disjoint ranges. -/
private theorem prefix_ne_following (n : ℕ) (i j : Fin n) :
    (i : ℕ) ≠ n + (j : ℕ) := by
  exact ne_of_lt (lt_of_lt_of_le i.isLt (Nat.le_add_right n j))

/-- A prefix average of `L²` coordinates is itself `L²`. -/
theorem memLp_prefixAverage (n : ℕ) (hX_L2 : ∀ i : Fin n, MemLp (X i) 2 μ) :
    MemLp (prefixAverage X n) 2 μ :=
  memLp_blockAverage (fun i : Fin n => (i : ℕ)) hX_L2

/-- A following tail average of `L²` coordinates is itself `L²`. -/
theorem memLp_followingAverage (n : ℕ) (hX_L2 : ∀ i : Fin n, MemLp (X (n + i)) 2 μ) :
    MemLp (followingAverage X n) 2 μ :=
  memLp_blockAverage (fun i : Fin n => n + (i : ℕ)) hX_L2

/-- **The exact long-average versus tail-average `L²` bound.** For a contractable process,
the squared `L²` distance between the average of the first `n` coordinates and the average of
the following `n` coordinates is `2 * (v - c) / n`. -/
theorem Contractable.integral_sq_prefixAverage_sub_followingAverage [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ) {n : ℕ} (hn : 0 < n) :
    ∫ ω, (prefixAverage X n ω - followingAverage X n ω) ^ 2 ∂μ =
      2 * (Var[X 0; μ] - cov[X 0, X 1; μ]) / n := by
  rw [prefixAverage, followingAverage,
    hX.integral_sq_blockAverage_sub_of_disjoint hX_L2 hn hn
      (prefixSelection_injective n) (followingSelection_injective n) (prefix_ne_following n)]
  ring

/-- The long-average versus tail-average squared `L²` distance tends to zero.  The use of
blocks of length `n + 1` avoids a separate convention for the empty average. -/
theorem Contractable.tendsto_integral_sq_prefixAverage_sub_followingAverage
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ) :
    Tendsto
      (fun n => ∫ ω, (prefixAverage X (n + 1) ω - followingAverage X (n + 1) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hformula : ∀ n : ℕ,
      ∫ ω, (prefixAverage X (n + 1) ω - followingAverage X (n + 1) ω) ^ 2 ∂μ =
        (2 * (Var[X 0; μ] - cov[X 0, X 1; μ])) * (1 / ((n : ℝ) + 1)) := by
    intro n
    rw [hX.integral_sq_prefixAverage_sub_followingAverage hX_L2 (Nat.succ_pos n)]
    push_cast
    ring
  simp_rw [hformula]
  simpa using
    (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

end Probability

end TauCeti
