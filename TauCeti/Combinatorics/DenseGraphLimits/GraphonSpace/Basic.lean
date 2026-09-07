/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The metric space of graphons

The coupling cut distance is a pseudometric on graphons over a fixed probability carrier.  This
file equips the strict graphon type with that pseudometric and forms its separation quotient,
identifying two representatives exactly when their cut distance is zero.  The quotient carries the
resulting genuine metric.

The quotient is fixed-carrier: `GraphonSpace Ω μ` contains graphons on `(Ω, μ)`.  Graphons on
different carriers are still compared by the cross-carrier `cutDist`; they are not bundled into a
single universe-level quotient.  The abbreviation `GraphonSpaceI` names the canonical quotient on
the unit interval.

Two graphons at cut distance zero — for instance a graphon and any measure-preserving
rearrangement of it — are topologically indistinguishable in the cut-metric topology, so the
identification that turns the pseudometric into a metric is exactly the separation quotient of the
strict graphon type.

## Main definitions

* `TauCeti.DenseGraphLimits.GraphonSpace` is the corresponding fixed-carrier quotient;
* `TauCeti.DenseGraphLimits.GraphonSpaceI` is the quotient over the unit interval.

## Main results

* `TauCeti.DenseGraphLimits.Graphon.dist_eq_cutDist` identifies the graphon distance with the
  coupling cut distance;
* `TauCeti.DenseGraphLimits.dist_graphonSpace_mk_mk` computes the quotient distance on
  representatives;
* `TauCeti.DenseGraphLimits.graphonSpace_mk_eq_mk_iff` characterises equality of representatives.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Section 6.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Section 8.2.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The coupling cut distance gives strict graphons on one probability carrier a pseudometric.

Distinct strict representatives can have distance zero, for example after a measure-preserving
rearrangement, so this is intentionally not a `MetricSpace`. -/
instance Graphon.instPseudoMetricSpace : PseudoMetricSpace (Graphon Ω μ) where
  dist := cutDist
  dist_self := cutDist_self
  dist_comm := cutDist_comm
  dist_triangle := cutDist_triangle

/-- The distance between strict graphons on one carrier is their coupling cut distance. -/
@[simp]
theorem Graphon.dist_eq_cutDist (U W : Graphon Ω μ) : dist U W = cutDist U W := (rfl)

/-- The fixed-carrier graphon space: strict graphons modulo vanishing cut distance. -/
abbrev GraphonSpace (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Type _ :=
  SeparationQuotient (Graphon Ω μ)

/-- The graphon-space distance between representatives is their coupling cut distance. -/
@[simp]
theorem dist_graphonSpace_mk_mk (U W : Graphon Ω μ) :
    dist (SeparationQuotient.mk U) (SeparationQuotient.mk W) = cutDist U W :=
  SeparationQuotient.dist_mk U W

/-- Two representatives determine the same point of graphon space exactly when their coupling cut
distance vanishes. -/
@[simp high]
theorem graphonSpace_mk_eq_mk_iff (U W : Graphon Ω μ) :
    SeparationQuotient.mk U = SeparationQuotient.mk W ↔ cutDist U W = 0 := by
  rw [SeparationQuotient.mk_eq_mk, Metric.inseparable_iff, Graphon.dist_eq_cutDist]

/-- The canonical graphon space over the unit interval with Lebesgue measure. -/
abbrev GraphonSpaceI : Type _ := GraphonSpace I (volume : Measure I)

end DenseGraphLimits

end TauCeti
