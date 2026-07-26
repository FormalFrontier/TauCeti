/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Public: the generic mixture representation this specializes, and the directing measure whose law
-- `deFinettiMeasure` is.
public import TauCeti.Probability.Exchangeability.MixedIID.Mixture
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic

/-!
# The de Finetti measure

The law of the canonical directing measure, as a probability measure on `ProbabilityMeasure α`,
together with the specialization of the mixture representation to it.

## Main results

* `deFinettiMeasure` — the law of `directingProbabilityMeasure`, bundled as a
  `ProbabilityMeasure (ProbabilityMeasure α)`, with `deFinettiMeasure_toMeasure` exposing its
  underlying measure.
* `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith` — the mixture representation against
  it, for a process whose canonical directing measure is a mixing representative.

## Hypotheses

The generic representation `pathLaw_eq_bind_infinitePi_of_mixedIIDWith` needs only
`[IsFiniteMeasure μ]`, a.e.-measurable coordinates, and a witness. The definition here needs more,
because the canonical directing measure is built from a conditional distribution: a probability base
law `[IsProbabilityMeasure μ]`, a standard-Borel nonempty **state** space
`[StandardBorelSpace α] [Nonempty α]`, and pointwise `Measurable` coordinates.

No theorem here assumes `[StandardBorelSpace Ω]`. That hypothesis is what *supplying* the canonical
witness costs — `mixedIIDWith_of_contractable` carries it — so the specialization below takes the
witness as an explicit hypothesis instead of deriving it.

## What is not here

The Layer 6 bullet in `TauCetiRoadmap/Exchangeability/README.md` asks for the mixture form with `π`
the **unique** law of `ν`. Uniqueness (`mixedIID_mixingLaw_unique`) is not proved here or anywhere
yet: at the roadmap's stated generality it needs finite-dimensional compact-box mixed-moment
determinacy, which does not exist. That bullet is therefore only partly discharged, and the roadmap
name `deFinetti_mixture` stays reserved for the theorem that *derives* a canonical witness rather
than assuming one.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- The law of the canonical directing measure `directingProbabilityMeasure μ X`, as a probability
measure on `ProbabilityMeasure α`.

This is the **de Finetti measure** — the mixing law `π` of the de Finetti representation —
*precisely when* `directingProbabilityMeasure μ X` is a `MixedIIDWith` witness for `X`, which is
what `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith` assumes. The definition itself
assumes no exchangeability or contractability, so for a general measurable process it is just that
pushforward and need not represent the path law at all.

Bundling records at the type level that the mixing law is a probability measure, and supports the
downstream weak-topology and convergence APIs, which are stated for `ProbabilityMeasure`; it coerces
back to `Measure` for the `bind` representation. Bundling is also why measurability is required at
construction time, as the argument `hX`: `Measure.map` of a non-measurable function is `0`, which is
not a probability measure, so the pushforward is not known to be one without it. -/
def deFinettiMeasure (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → α)
    (hX : ∀ n, Measurable (X n)) : ProbabilityMeasure (ProbabilityMeasure α) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
    (f := directingProbabilityMeasure μ X)
    (measurable_directingProbabilityMeasure
      (μ := μ) (tailProcess_le_ambient 0 fun j _ => hX j)).aemeasurable

/-- The underlying measure of the de Finetti measure is the pushforward of the directing measure. -/
@[simp]
theorem deFinettiMeasure_toMeasure {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (hX : ∀ n, Measurable (X n)) :
    (deFinettiMeasure μ X hX : Measure (ProbabilityMeasure α))
      = μ.map (directingProbabilityMeasure μ X) := by
  simp only [deFinettiMeasure, ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk]

/-- **The mixture representation against the de Finetti measure.** When the canonical directing
measure is a mixing representative for `X`, the path law of `X` is the `deFinettiMeasure`-mixture of
the infinite product measures.

The witness hypothesis is taken rather than derived: `mixedIIDWith_of_contractable` supplies it, but
only under `[StandardBorelSpace Ω]`, and taking it here keeps that assumption out of this
statement. -/
theorem pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} (hX : ∀ n, Measurable (X n))
    (h : MixedIIDWith μ X (directingProbabilityMeasure μ X)) :
    pathLaw μ X
      = (deFinettiMeasure μ X hX : Measure (ProbabilityMeasure α)).bind
          fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  rw [deFinettiMeasure_toMeasure]
  exact pathLaw_eq_bind_infinitePi_of_mixedIIDWith (fun n => (hX n).aemeasurable) h

end Probability

end TauCeti
