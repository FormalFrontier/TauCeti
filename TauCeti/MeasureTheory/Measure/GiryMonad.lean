/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Naturality of the Giry monad's `bind`

Pushing a `Measure.bind` mixture forward by a measurable map commutes with the bind: the
pushforward of a mixture is the mixture of the pushforwards.

Mathlib carries this naturality for `PMF` (`PMF.map_bind`) but not for `Measure`, although all
of its ingredients — `Measure.bind_bind` and `Measure.bind_dirac_eq_map` — are there. This file
supplies the missing `Measure` form.

It is stated for an a.e.-measurable kernel `g`, which is the hypothesis `Measure.bind_bind`
needs, and it is the shape mixture arguments want: `bind` is how a random measure is integrated
against its mixing law, so pushing a mixture forward along a coordinate map — a marginal — is a
routine step.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {S γ δ : Type*} [MeasurableSpace S] [MeasurableSpace γ] [MeasurableSpace δ]

/-- **Naturality of `bind`.** Pushing a `Measure.bind` mixture forward by a measurable map
commutes with the bind: the pushforward of the mixture is the mixture of the pushforwards, i.e.
the Giry-monad identity `map F ∘ bind g = bind (map F ∘ g)`.

Obtained from associativity of `bind` together with `bind_dirac_eq_map`. -/
theorem map_bind {μ : Measure S} {g : S → Measure γ} (hg : AEMeasurable g μ)
    {F : γ → δ} (hF : Measurable F) :
    (μ.bind g).map F = μ.bind fun ω => (g ω).map F := by
  have hdirac : AEMeasurable (fun x : γ => Measure.dirac (F x)) (μ.bind g) :=
    (Measure.measurable_dirac.comp hF).aemeasurable
  rw [← Measure.bind_dirac_eq_map (μ.bind g) hF, Measure.bind_bind hg hdirac]
  simp_rw [Measure.bind_dirac_eq_map _ hF]

end MeasureTheory

end TauCeti
