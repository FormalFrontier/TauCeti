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

The implementation deliberately uses Mathlib's `SeparationQuotient`.  Once `cutDist` is installed
as the pseudometric on strict graphons, Mathlib supplies both the quotient metric and its
representative formula.  The named `graphonSetoid` keeps the defining relation visible to users.

## Main definitions

* `TauCeti.DenseGraphLimits.graphonSetoid` identifies graphons at cut distance zero;
* `TauCeti.DenseGraphLimits.GraphonSpace` is the corresponding fixed-carrier quotient;
* `TauCeti.DenseGraphLimits.GraphonSpaceI` is the quotient over the unit interval.

## Main results

* `TauCeti.DenseGraphLimits.dist_graphonSpace_mk_mk` computes the quotient distance on
  representatives;
* `TauCeti.DenseGraphLimits.GraphonSpace.mk_eq_mk` characterizes equality of representatives by
  vanishing cut distance.

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

/-- The equivalence relation on fixed-carrier graphons given by vanishing cut distance.

This is Mathlib's inseparability setoid for the cut-distance pseudometric, so its quotient inherits
the generic separation-quotient metric. -/
abbrev graphonSetoid : Setoid (Graphon Ω μ) := inseparableSetoid (Graphon Ω μ)

/-- Two graphons are related by `graphonSetoid` exactly when their cut distance is zero. -/
@[simp]
theorem graphonSetoid_rel_iff (U W : Graphon Ω μ) :
    graphonSetoid U W ↔ cutDist U W = 0 :=
  Metric.inseparable_iff

/-- The fixed-carrier graphon space: strict graphons modulo vanishing cut distance. -/
def GraphonSpace (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Type _ :=
  Quotient (graphonSetoid (μ := μ))

/-- The canonical graphon space over the unit interval with Lebesgue measure. -/
abbrev GraphonSpaceI : Type _ := GraphonSpace I (volume : Measure I)

/-- The cut-distance quotient is a genuine metric space. -/
instance GraphonSpace.instMetricSpace : MetricSpace (GraphonSpace Ω μ) :=
  inferInstanceAs (MetricSpace (SeparationQuotient (Graphon Ω μ)))

namespace GraphonSpace

/-- The class of a strict graphon in graphon space. -/
def mk (W : Graphon Ω μ) : GraphonSpace Ω μ :=
  Quotient.mk (graphonSetoid (μ := μ)) W

/-- Every point of graphon space has a strict graphon representative. -/
theorem surjective_mk : Function.Surjective (mk : Graphon Ω μ → GraphonSpace Ω μ) :=
  Quotient.mk_surjective

/-- Prove a property of graphon space by proving it on every strict representative. -/
protected theorem inductionOn {motive : GraphonSpace Ω μ → Prop} (W : GraphonSpace Ω μ)
    (mk : ∀ U, motive (GraphonSpace.mk U)) : motive W :=
  Quotient.inductionOn W mk

/-- Define a function on graphon space from a function on strict graphons that is invariant under
zero cut distance. -/
protected def lift {X : Sort*} (f : Graphon Ω μ → X)
    (h : ∀ U W, cutDist U W = 0 → f U = f W) : GraphonSpace Ω μ → X :=
  Quotient.lift f fun U W hUW => h U W (graphonSetoid_rel_iff U W |>.mp hUW)

/-- A lifted function on graphon space evaluates on a class by evaluating its representative. -/
@[simp]
theorem lift_mk {X : Sort*} (f : Graphon Ω μ → X)
    (h : ∀ U W, cutDist U W = 0 → f U = f W) (W : Graphon Ω μ) :
    GraphonSpace.lift f h (mk W) = f W :=
  (rfl)

/-- Two representatives determine the same point of graphon space exactly when their cut distance
vanishes. -/
@[simp]
theorem mk_eq_mk (U W : Graphon Ω μ) : mk U = mk W ↔ cutDist U W = 0 :=
  SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

end GraphonSpace

/-- The distance between the classes of two graphons is their coupling cut distance. -/
@[simp]
theorem dist_graphonSpace_mk_mk (U W : Graphon Ω μ) :
    dist (GraphonSpace.mk U) (GraphonSpace.mk W) = cutDist U W :=
  (rfl)

end DenseGraphLimits

end TauCeti
