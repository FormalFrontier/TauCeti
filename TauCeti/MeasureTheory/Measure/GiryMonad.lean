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

The file also records `bind_add`, additivity of `Measure.bind` in the mixing measure. Mathlib has
the `ℝ≥0∞`-homogeneity `Measure.bind_smul` and the `Measure.sum`-indexed `Measure.bind_sum`, but
not the binary sum; together with `Measure.bind_smul` it makes `bind` an affine operation on
mixing measures.
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
    {F : γ → δ} (hF : Measurable F) : (μ.bind g).map F = μ.bind fun ω => (g ω).map F := by
  have hdirac : AEMeasurable (fun x : γ => Measure.dirac (F x)) (μ.bind g) :=
    (Measure.measurable_dirac.comp hF).aemeasurable
  rw [← Measure.bind_dirac_eq_map (μ.bind g) hF, Measure.bind_bind hg hdirac]
  simp_rw [Measure.bind_dirac_eq_map _ hF]

/-- **Binding after a pushforward.** Binding `g` against a pushforward measure reindexes the
mixing measure: `bind g ∘ map f = bind (g ∘ f)`.

This is the `Measure` form of `PMF.bind_map`, and like it is a `simp` lemma: it rewrites a bind of
a mapped measure into the canonical single-bind form. -/
@[simp]
theorem bind_map {μ : Measure S} {f : S → γ} (hf : AEMeasurable f μ)
    {g : γ → Measure δ} (hg : AEMeasurable g (μ.map f)) : (μ.map f).bind g = μ.bind (g ∘ f) := by
  unfold Measure.bind
  rw [AEMeasurable.map_map_of_aemeasurable hg hf]

/-- **`Measure.bind` is additive in the mixing measure.** Mixing against the sum of two measures
is the sum of the two mixtures.

Together with Mathlib's `Measure.bind_smul` this says that a fixed measurable kernel acts affinely
on mixing measures. Mathlib has the `Measure.sum`-indexed `Measure.bind_sum`, of which this is the
binary case. -/
theorem bind_add (μ ν : Measure S) {g : S → Measure γ} (hg : Measurable g) :
    (μ + ν).bind g = μ.bind g + ν.bind g := by
  unfold Measure.bind
  rw [Measure.map_add _ _ hg]
  ext s hs
  rw [Measure.join_apply hs, Measure.add_apply, Measure.join_apply hs, Measure.join_apply hs,
    lintegral_add_measure]

end MeasureTheory

end TauCeti
