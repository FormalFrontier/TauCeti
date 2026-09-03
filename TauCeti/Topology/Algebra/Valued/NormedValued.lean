/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# The topology of a nonarchimedean normed field is valuative

`Mathlib/Topology/Algebra/Valued/NormedValued.lean` turns an ultrametric normed field `K` into a
`Valued K ℝ≥0` through its norm, and `Mathlib/Topology/Algebra/Valued/ValuativeRel.lean` records
the predicate `IsValuativeTopology K` saying that the topology of `K` is the one its
`ValuativeRel K` prescribes. This file joins the two: if the norm valuation
`NormedField.valuation` is compatible with a valuative relation already present on `K`, then the
metric topology of `K` is the valuative topology, and the valuation integers `𝒪[K]` are the
closed unit ball.

The comparison is what a normed field needs in order to be a model of the valuative theory:
`Mathlib/NumberTheory/Padics/ValuativeRel.lean`, for instance, builds the valuative relation of
`ℚ_[p]` from `Padic.mulValuation` and never mentions the `p`-adic metric.

## Main results

* `TauCeti.NormedField.valuation_le_valuation_iff_norm_le_norm`: the valuative order on `K` is
  the order of the norm.
* `TauCeti.NormedField.mem_integer_iff_norm_le_one`: `𝒪[K]` is the closed unit ball.
* `TauCeti.NormedField.isValuativeTopology`: the metric topology is the valuative topology.

No nontriviality of the norm is needed: the trivially normed, hence discrete, case is covered.
-/

public section

open ValuativeRel

namespace TauCeti.NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [(_root_.NormedField.valuation (K := K)).Compatible]

/-- Compatibility of the norm valuation with the valuative relation, read on the norm: the
valuative order on `K` is the order of the norm. -/
theorem valuation_le_valuation_iff_norm_le_norm (x y : K) :
    valuation K x ≤ valuation K y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [ValuativeRel.isEquiv (valuation K) (_root_.NormedField.valuation (K := K)) x y]
  simp [← NNReal.coe_le_coe]

/-- The strict form of `TauCeti.NormedField.valuation_le_valuation_iff_norm_le_norm`. -/
theorem valuation_lt_valuation_iff_norm_lt_norm (x y : K) :
    valuation K x < valuation K y ↔ ‖x‖ < ‖y‖ := by
  simp only [← not_le, valuation_le_valuation_iff_norm_le_norm]

/-- The valuation integers of `K` are the elements of norm at most one. -/
@[simp]
theorem mem_integer_iff_norm_le_one {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation K),
    valuation_le_valuation_iff_norm_le_norm, norm_one]

/-- The metric topology of an ultrametric normed field whose norm valuation is compatible with a
valuative relation on it is the valuative topology. All of the content is Mathlib's
`NormedField.toValued`, whose `is_topological_valuation` field is precisely the hypothesis of
`IsValuativeTopology.of_mem_nhds_zero_iff_vle`. This is a `theorem` rather than an `instance`:
the compatibility hypothesis is not something typeclass inference should search for on an
arbitrary normed field. -/
theorem isValuativeTopology : IsValuativeTopology K :=
  letI := _root_.NormedField.toValued (K := K)
  .of_mem_nhds_zero_iff_vle _ (Valued.is_topological_valuation _)

end TauCeti.NormedField
