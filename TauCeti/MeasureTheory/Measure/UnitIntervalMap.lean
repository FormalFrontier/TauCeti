/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Representation

/-!
# Realizing a probability law by a map from the unit interval

Every standard Borel probability space `(Ω, μ)` receives a measure-preserving map from
`(I, volume)`: there is `f : I → Ω` with `volume.map f = μ`. This is Theorem A.9 of Janson's
*Graphons, cut norm and distance, couplings and rearrangements*.

**Atoms are allowed.** No atomless hypothesis appears, and none is needed: the statement is an
existence claim about a map *into* `Ω`, not a bijection, so a law concentrated on finitely many
points is realized by a step function on `I`. The regressions below pin this down at a Dirac mass,
at a finite mixture, and at a mixture of an atom with a continuous part — the cases where an
atomless reading of the theorem would fail.

This is the transport underlying the Layer 5 identification of coupling cut distance with the
classical measure-preserving-map infimum: every coupling, being itself standard Borel, is realized
by a pair of such maps. That identification is not proved here.

## Main results

* `MeasureTheory.Measure.exists_measurePreserving_from_unitInterval` — a measure-preserving
  `f : I → Ω` onto any standard Borel probability space.

## Implementation

Mathlib's `MeasureTheory.Measure.exists_measurable_map_eq` already supplies the function and the
pushforward identity; the content here is packaging them as `MeasurePreserving`, which is
definitionally that pair. Mathlib states it with `[Nonempty Ω]`, which is not carried here: a
probability measure on `Ω` already forces `Ω` to be nonempty, and
`nonempty_of_isProbabilityMeasure` supplies the instance inside the proof.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem A.9.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 5 — the `(I, volume)` transport
  target. The atomless mod-null equivalence `exists_mpModNull_equiv_unitInterval` and the map form
  `cutDistPullback` are separate targets and are not built here.
-/

public section

open MeasureTheory unitInterval

open scoped ENNReal

namespace MeasureTheory.Measure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Janson A.9.** Every standard Borel probability space receives a measure-preserving map from
the unit interval with Lebesgue measure.

No atomless hypothesis is needed: `μ` may be a Dirac mass, a finite mixture, or a mixture of atoms
with a continuous part. -/
theorem exists_measurePreserving_from_unitInterval (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ f : I → Ω, MeasurePreserving f volume μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨f, hf_meas, hf_map⟩ := μ.exists_measurable_map_eq
  exact ⟨f, hf_meas, hf_map⟩

/-! ### Regressions: the atomic cases

`exists_measurePreserving_from_unitInterval` is stated without an atomless hypothesis. These three
instantiations are what that buys, and they fail for any formulation that quietly assumes `μ` has
no atoms. -/

/-- Regression: a Dirac mass is realized, by the constant map. -/
private theorem exists_measurePreserving_from_unitInterval_dirac (a : Ω) :
    ∃ f : I → Ω, MeasurePreserving f volume (Measure.dirac a) :=
  exists_measurePreserving_from_unitInterval _

/-- Regression: a finite mixture of atoms is realized. -/
private theorem exists_measurePreserving_from_unitInterval_finite_atomic (a b : Ω) :
    ∃ f : I → Ω, MeasurePreserving f volume
      ((1 / 2 : ℝ≥0∞) • Measure.dirac a + (1 / 2 : ℝ≥0∞) • Measure.dirac b) := by
  have : IsProbabilityMeasure
      ((1 / 2 : ℝ≥0∞) • Measure.dirac a + (1 / 2 : ℝ≥0∞) • Measure.dirac b) := by
    constructor; simp [ENNReal.inv_two_add_inv_two]
  exact exists_measurePreserving_from_unitInterval _

/-- Regression: a mixture of an atom with a continuous part is realized. -/
private theorem exists_measurePreserving_from_unitInterval_mixed :
    ∃ f : I → ℝ, MeasurePreserving f volume
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)
        + (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have : IsProbabilityMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)
      + (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor; simp [Real.volume_Icc, ENNReal.inv_two_add_inv_two]
  exact exists_measurePreserving_from_unitInterval _

end MeasureTheory.Measure
