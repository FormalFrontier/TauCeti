/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Exchangeability.L2.BlockAverages

/-!
# Work in progress
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The moving average of `X` over the `m` coordinates starting at `n`. -/
private def movingAverage (X : ℕ → Ω → ℝ) (n m : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin m => n + i

omit [MeasurableSpace Ω] in
private theorem movingAverage_apply (n m : ℕ) (ω : Ω) :
    movingAverage X n m ω = (m : ℝ)⁻¹ * ∑ i : Fin m, X (n + i) ω := by
  simp [movingAverage]

private theorem injective_movingIndex (n m : ℕ) :
    Function.Injective fun i : Fin m => n + i.val := by
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-- Two moving windows that do not overlap have disjoint index sets. -/
private theorem movingIndex_disjoint {n₁ m₁ n₂ m₂ : ℕ} (h : n₁ + m₁ ≤ n₂) :
    ∀ (i : Fin m₁) (j : Fin m₂), n₁ + i.val ≠ n₂ + j.val := by
  intro i j hij
  omega

private theorem memLp_movingAverage (hX_L2 : ∀ i, MemLp (X i) 2 μ) (n m : ℕ) :
    MemLp (movingAverage X n m) 2 μ :=
  memLp_blockAverage _ fun _ => hX_L2 _

/-- **The L² distance between two non-overlapping moving averages.** For a contractable `L²`
sequence, `∫ (A - A')²` is exactly `C/m₁ + C/m₂` with `C = Var - cov`, so the `L²` distance is
`√(C/m₁ + C/m₂)`. This is the landed disjoint-window identity read as a distance. -/
private theorem dist_toLp_movingAverage_of_le [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ i, MemLp (X i) 2 μ)
    {n₁ m₁ n₂ m₂ : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hsep : n₁ + m₁ ≤ n₂) :
    dist ((memLp_movingAverage hX_L2 n₁ m₁).toLp _)
        ((memLp_movingAverage hX_L2 n₂ m₂).toLp _)
      = (((Var[X 0; μ] - cov[X 0, X 1; μ]) / m₁
          + (Var[X 0; μ] - cov[X 0, X 1; μ]) / m₂) : ℝ) ^ (2 : ℝ)⁻¹ := by
  sorry

end Probability

end TauCeti
