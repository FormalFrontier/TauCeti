/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Zero-one laws are almost surely constant

A zero-one measure gives every measurable set mass `0` or `1`. Mathlib's
`MeasureTheory.IsZeroOneMeasure.exists_eq_dirac` identifies such a measure with a Dirac mass, but
only when the carrier is standard Borel. This file records the form that survives on an arbitrary
carrier: a measurable map *into* a standard Borel space is almost surely constant, because its
pushforward is again a zero-one probability measure and is therefore Dirac.

The carrier itself needs no Borel structure, so this applies to a space that carries a measurable
map into a standard Borel space without being one — for instance `ProbabilityMeasure α` for a
countably generated `α`, which
`TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure` evaluates into a
countable power of `ℝ≥0∞`.

## Main results

* `TauCeti.MeasureTheory.IsZeroOneMeasure.exists_ae_eq_const`: under a zero-one measure, an
  almost-everywhere measurable map into a standard Borel space agrees almost everywhere with a
  single value.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

/-- **A zero-one law is almost surely constant along a measurable map.** The pushforward of a
nonzero zero-one measure along `f` is again a zero-one probability measure; on a standard Borel
space it is therefore a Dirac mass at some `q`, and `f` equals `q` almost everywhere.

The carrier `Ω` needs no topological or Borel structure of its own, and `f` need only be
almost-everywhere measurable. -/
theorem IsZeroOneMeasure.exists_ae_eq_const {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [StandardBorelSpace β] {π : Measure Ω} [NeZero π] [_root_.MeasureTheory.IsZeroOneMeasure π]
    {f : Ω → β} (hf : AEMeasurable f π) :
    ∃ q : β, ∀ᵐ ω ∂π, f ω = q := by
  have : IsProbabilityMeasure π := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := π) with (h | h)
    · simp_all
    · exact ⟨h⟩
  have : IsProbabilityMeasure (π.map f) := Measure.isProbabilityMeasure_map hf
  have : _root_.MeasureTheory.IsZeroOneMeasure (π.map f) := {
    zero_one₀ := fun s hs => by
      rw [Measure.map_apply_of_aemeasurable hf hs]
      exact _root_.MeasureTheory.Measure.zero_one π (f ⁻¹' s) }
  obtain ⟨q, hq⟩ := _root_.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac (μ := π.map f)
  refine ⟨q, ae_of_ae_map (p := fun y => y = q) hf ?_⟩
  rw [hq]
  simp

end MeasureTheory

end TauCeti
