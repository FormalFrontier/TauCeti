/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Divisors of analytic functions

This file relates Mathlib's divisor of an analytic function to its natural analytic order.
-/

public section

namespace TauCeti

namespace MeromorphicOn.AnalyticOnNhd

/-- For a holomorphic function the divisor records the order of vanishing. The identity also holds
at a point of infinite order, where both sides read `0`. -/
lemma divisor_eq_analyticOrderNatAt {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {V : Set 𝕜}
    (hf : AnalyticOnNhd 𝕜 f V) {z : 𝕜} (hz : z ∈ V) :
    MeromorphicOn.divisor f V z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  -- `analyticOrderNatAt` is `(analyticOrderAt · ·).toNat`; this is the one place the proof needs
  -- that definitional equality, so unfold it here rather than in the statements.
  cases h : analyticOrderAt f z with
  | top => simp [analyticOrderNatAt, h]
  | coe n => simp [analyticOrderNatAt, h]

end MeromorphicOn.AnalyticOnNhd

end TauCeti
