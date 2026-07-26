/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The Giry monad's `map`/`bind` interchange laws

Two ways `Measure.map` and `Measure.bind` commute:

* `map_bind` — pushing a mixture forward is the mixture of the pushforwards,
  `map F ∘ bind g = bind (map F ∘ g)`;
* `bind_map` — binding after a pushforward reindexes the mixing measure,
  `bind g ∘ map f = bind (g ∘ f)`.

Mathlib carries both for `PMF` (`PMF.map_bind`, `PMF.bind_map`) but neither for `Measure`,
although all of their ingredients — `Measure.bind_bind`, `Measure.bind_dirac_eq_map`,
`Measure.dirac_bind` — are there. This file supplies the missing `Measure` forms.

They are the shape mixture arguments want: `bind` is how a random measure is integrated against
its mixing law, so pushing a mixture forward along a coordinate map (a marginal), or rewriting a
mixture over a pushforward mixing law, are both routine steps.
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

/-- **Binding after a pushforward.** Binding `g` against a pushforward measure reindexes the
mixing measure: `bind g ∘ map f = bind (g ∘ f)`.

Obtained from associativity of `bind` together with `bind_dirac_eq_map` and `dirac_bind`. This is
the `Measure` form of `PMF.bind_map`. -/
theorem bind_map {μ : Measure S} {f : S → γ} (hf : Measurable f)
    {g : γ → Measure δ} (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  have hdirac : AEMeasurable (fun x : S => Measure.dirac (f x)) μ :=
    (Measure.measurable_dirac.comp hf).aemeasurable
  rw [← Measure.bind_dirac_eq_map μ hf, Measure.bind_bind hdirac hg.aemeasurable]
  simp_rw [Function.comp_def, Measure.dirac_bind hg]

end MeasureTheory

end TauCeti
