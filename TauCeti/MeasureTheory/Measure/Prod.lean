/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Marginals of coordinatewise pushforwards

The first (respectively second) marginal of the coordinatewise pushforward
`π.map (Prod.map f g)` of a measure on a product space is the pushforward of the first
(respectively second) marginal.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Measure

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The first marginal of a coordinatewise pushforward is the pushforward of the first
marginal. -/
@[simp]
theorem fst_map_prodMap {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    (π : Measure (X × Y)) {f : X → X'} {g : Y → Y'} (hf : Measurable f)
    (hg : Measurable g) :
    (π.map (Prod.map f g)).fst = π.fst.map f := by
  rw [Prod.map_def]
  exact (Measure.fst_map_prodMk (μ := π) (X := f ∘ Prod.fst) (Y := g ∘ Prod.snd)
    (hg.comp measurable_snd)).trans (Measure.map_map hf measurable_fst).symm

/-- The second marginal of a coordinatewise pushforward is the pushforward of the second
marginal. -/
@[simp]
theorem snd_map_prodMap {X' Y' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    (π : Measure (X × Y)) {f : X → X'} {g : Y → Y'} (hf : Measurable f)
    (hg : Measurable g) :
    (π.map (Prod.map f g)).snd = π.snd.map g := by
  rw [Prod.map_def]
  exact (Measure.snd_map_prodMk (μ := π) (X := f ∘ Prod.fst) (Y := g ∘ Prod.snd)
    (hf.comp measurable_fst)).trans (Measure.map_map hg measurable_snd).symm

end Measure

end TauCeti
