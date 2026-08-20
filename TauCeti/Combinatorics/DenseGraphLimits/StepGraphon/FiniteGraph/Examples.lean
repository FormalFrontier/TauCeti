/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.FiniteGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Computed examples of finite graph graphons

This file verifies the DenseGraphLimits roadmap's computed-value backstops for finite graph
graphons: `t(K₂, W_{K₄}) = 3/4` and `t(K₃, W_{C₅}) = 0`.

## Main results

* `TauCeti.DenseGraphLimits.homDensity_top_two_finiteGraphGraphon_top_four` — the edge density of
  `K₄`;
* `TauCeti.DenseGraphLimits.homDensity_top_three_finiteGraphGraphon_cycleGraph_five` — `C₅` is
  triangle-free.

## References

* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, *Worked examples (acceptance gates)*.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- **The edge density of `K₄`.** `t(K₂, W_{K₄}) = 3/4`: of the `16` ordered pairs of vertices of
the complete graph on four vertices, the `12` with distinct entries are adjacent.

The roadmap's backstop value at the end of the pipeline: it pins the homomorphism count `12`, the
`homDensityFin` denominator `4 ^ 2`, and the applicability of the compatibility theorem. The
graphon-side integral and the cell volumes are inherited from that theorem. -/
theorem homDensity_top_two_finiteGraphGraphon_top_four :
    homDensity (⊤ : SimpleGraph (Fin 2)) (finiteGraphGraphon (⊤ : SimpleGraph (Fin 4)))
      = 3 / 4 := by
  have hcount : Nat.card ((⊤ : SimpleGraph (Fin 2)) →g (⊤ : SimpleGraph (Fin 4))) = 12 := by
    rw [card_hom_eq_card_adj_preserving_maps, Nat.card_eq_fintype_card]
    decide
  rw [homDensity_finiteGraphGraphon _ (by norm_num), homDensityFin_def, hcount]
  norm_num

/-- **`C₅` is triangle-free.** `t(K₃, W_{C₅}) = 0`: no map `Fin 3 → Fin 5` sends all three edges of
a triangle to edges of the five-cycle, so the density vanishes exactly rather than approximately. -/
theorem homDensity_top_three_finiteGraphGraphon_cycleGraph_five :
    homDensity (⊤ : SimpleGraph (Fin 3)) (finiteGraphGraphon (SimpleGraph.cycleGraph 5)) = 0 := by
  have hcount : Nat.card ((⊤ : SimpleGraph (Fin 3)) →g SimpleGraph.cycleGraph 5) = 0 := by
    rw [card_hom_eq_card_adj_preserving_maps, Nat.card_eq_fintype_card]
    decide
  rw [homDensity_finiteGraphGraphon _ (by norm_num), homDensityFin_def, hcount]
  norm_num

end DenseGraphLimits

end TauCeti
