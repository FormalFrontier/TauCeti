/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Transport costs on compact spaces

This file records finiteness of the transport cost for a continuous real-valued cost on a compact
product. Compactness bounds the cost by a finite constant, so any feasible pair of finite
marginals has finite primal value.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {c : X × Y → ℝ}

/-- A continuous cost on a product of compact spaces is bounded, so any feasible transport
problem with a finite first marginal has finite value. -/
theorem transportCost_ne_top_of_continuous [IsFiniteMeasure μ]
    (hπ : ∃ π, IsCoupling π μ ν) (hc : Continuous c) :
    transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν ≠ ⊤ := by
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal K * μ univ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)) ?_
  refine (transportCost_mono fun z ↦ ENNReal.ofReal_le_ofReal
    ((le_abs_self _).trans (by simpa using hK z (Set.mem_univ z)))).trans_eq ?_
  exact transportCost_const hπ _

end TauCeti
