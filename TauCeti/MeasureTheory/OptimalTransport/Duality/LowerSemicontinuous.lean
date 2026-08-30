/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Compact
import TauCeti.MeasureTheory.OptimalTransport.Existence

/-!
# Kantorovich duality for lower-semicontinuous costs on compact spaces

This file extends compact Kantorovich duality from continuous finite costs to arbitrary
lower-semicontinuous costs `c : X × Y → ℝ≥0∞`. In particular, the cost may be unbounded or take
the value `∞`, so the common primal and dual value is retained in `ℝ≥0∞`.

The bridge is the monotone bounded-continuous approximation `TauCeti.lscApprox`. On compact
metrizable spaces, minimization over the coupling set commutes with this increasing supremum:

`transportCost c μ ν = ⨆ n, transportCost (lscApprox c n) μ ν`.

For the nontrivial inequality, the sublevel sets of the approximate integral functionals are a
decreasing sequence of nonempty closed subsets of the compact coupling set. A plan in their
intersection has `c`-cost bounded by the supremum of the approximate optimal values. Applying
continuous compact duality at every approximation then identifies the original transport cost
with the supremum of the positive parts of the values of continuous dual-feasible potentials.

## Main statements

* `TauCeti.isLUB_ofReal_kantorovichDualValue_continuous_of_lowerSemicontinuous` — strong
  Kantorovich duality for a lower-semicontinuous extended-nonnegative cost on compact metrizable
  spaces, in a form that permits the value `∞`;
* `TauCeti.transportCost_eq_sSup_ofReal_kantorovichDualValue_continuous_of_lowerSemicontinuous` —
  the same result as an equality with the supremum of the continuous dual values.

## References

* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, 2003,
  Theorem 1.3.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, 2009, Theorem 5.10.

This is the compact lower-semicontinuous regime of Layer 2, item 4 of the optimal-transport
roadmap. Its monotone-approximation theorem is the compact exhaustion step used by the Polish
lower-semicontinuous regime.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
  [TopologicalSpace.MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {c : X × Y → ℝ≥0∞}

/-- **Strong Kantorovich duality for lower-semicontinuous costs on compact metrizable spaces.**
The primal transport cost is the least upper bound, in `ℝ≥0∞`, of the positive parts of the
values of continuous dual-feasible potential pairs.

The extended-nonnegative codomain is essential: an unbounded or infinite-valued cost can have
primal value `∞`, in which case the continuous dual values are unbounded rather than attaining a
real supremum. -/
theorem isLUB_ofReal_kantorovichDualValue_continuous_of_lowerSemicontinuous
    (hc : LowerSemicontinuous c) :
    IsLUB {r : ℝ≥0∞ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧ DualFeasible c φ ψ ∧
      ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} (transportCost c μ ν) := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let : PseudoMetricSpace Y := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
  constructor
  · rintro r ⟨φ, ψ, hφ, hψ, hfeas, rfl⟩
    have hφi : Integrable φ μ := by
      simpa only [integrableOn_univ] using
        hφ.continuousOn.integrableOn_compact' (μ := μ) isCompact_univ MeasurableSet.univ
    have hψi : Integrable ψ ν := by
      simpa only [integrableOn_univ] using
        hψ.continuousOn.integrableOn_compact' (μ := ν) isCompact_univ MeasurableSet.univ
    exact hfeas.ofReal_kantorovichDualValue_le_transportCost hφi hψi
  · intro b hb
    rw [transportCost_eq_iSup_transportCost_lscApprox hc]
    refine iSup_le fun n ↦ ?_
    by_cases hbtop : b = ∞
    · simp only [hbtop, le_top]
    let cn : X × Y → ℝ := lscApproxAux c n
    have hcn_cont : Continuous cn := continuous_lscApproxAux c n
    have hcn_nonneg : ∀ z, 0 ≤ cn z := lscApproxAux_nonneg c n
    have hcn_le : (fun z ↦ ENNReal.ofReal (cn z)) ≤ c := fun z ↦
      ofReal_lscApproxAux_le c n z
    have hleast :
        (transportCost (fun z ↦ ENNReal.ofReal (cn z)) μ ν).toReal ≤ b.toReal :=
      (isLUB_kantorovichDualValue_continuous
        (μ := μ) (ν := ν) hcn_cont hcn_nonneg).2 fun r hr ↦ by
          obtain ⟨φ, ψ, hφ, hψ, hfeas, rfl⟩ := hr
          have hfeas' : DualFeasible c φ ψ :=
            ((dualFeasible_ofReal_iff hcn_nonneg φ ψ).2 hfeas).mono_cost hcn_le
          exact (ENNReal.ofReal_le_iff_le_toReal hbtop).1
            (hb ⟨φ, ψ, hφ, hψ, hfeas', rfl⟩)
    have hcost_ne_top : transportCost (fun z ↦ ENNReal.ofReal (cn z)) μ ν ≠ ∞ :=
      transportCost_ne_top_of_continuous (μ := μ) (ν := ν)
        ⟨_, isCoupling_prod μ ν⟩ hcn_cont
    have hcost_le : transportCost (fun z ↦ ENNReal.ofReal (cn z)) μ ν ≤ b :=
      (ENNReal.toReal_le_toReal hcost_ne_top hbtop).1 hleast
    simpa only [cn, coe_lscApprox_apply] using hcost_le

/-- Strong compact duality for a lower-semicontinuous extended-nonnegative cost, written as an
equality between the primal value and the supremum of the positive parts of all continuous dual
values. This formulation remains meaningful when the common value is `∞`. -/
theorem transportCost_eq_sSup_ofReal_kantorovichDualValue_continuous_of_lowerSemicontinuous
    (hc : LowerSemicontinuous c) :
    transportCost c μ ν = sSup {r : ℝ≥0∞ | ∃ φ ψ, Continuous φ ∧ Continuous ψ ∧
      DualFeasible c φ ψ ∧ ENNReal.ofReal (kantorovichDualValue μ ν φ ψ) = r} :=
  (isLUB_ofReal_kantorovichDualValue_continuous_of_lowerSemicontinuous hc).sSup_eq.symm

end TauCeti
