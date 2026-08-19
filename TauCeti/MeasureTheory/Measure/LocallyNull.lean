/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Locally null images

This file provides a local-to-global criterion for the image of a set to have measure zero.

## Main results

* `TauCeti.measure_image_null_of_locally_null`: an image is null as soon as it is locally null.
-/

public section

open MeasureTheory Set

open scoped Topology

namespace TauCeti

variable {E F : Type*} [TopologicalSpace E] [SecondCountableTopology E] [MeasurableSpace F]
  {ν : Measure F} {f : E → F} {s : Set E}

/-- If every point of `s` has a neighbourhood within `s` whose image under `f` is null, then the
image of `s` is null. A countable subcover, available because the source is second countable,
reduces the global statement to the local ones; this is the image version of
`MeasureTheory.measure_null_of_locally_null`. -/
theorem measure_image_null_of_locally_null (h : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, ν (f '' u) = 0) :
    ν (f '' s) = 0 := by
  choose! u hu hu0 using h
  obtain ⟨t, hts, htc, hst⟩ := TopologicalSpace.countable_cover_nhdsWithin hu
  refine measure_mono_null (image_mono hst) ?_
  rw [image_iUnion₂]
  exact (measure_biUnion_null_iff htc).2 fun x hx ↦ hu0 x (hts hx)

end TauCeti

end
