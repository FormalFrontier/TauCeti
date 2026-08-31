/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
`[IsFiniteMeasure μ]`, a.e.-measurable coordinates, and a witness. Defining
`deFinettiMeasure μ X` additionally needs a probability base law `[IsProbabilityMeasure μ]` and a
standard-Borel nonempty state space `[StandardBorelSpace α] [Nonempty α]`, because the canonical
directing measure is built from a conditional distribution. It takes no measurability or tail-space
hypothesis: `ProbabilityMeasure.map` is defined for every function. The later identification uses a
`MixedIIDWith` witness, whose definition includes coordinatewise a.e. measurability.

No theorem here assumes `[StandardBorelSpace Ω]`, and the specialization below takes the witness as
an explicit hypothesis rather than deriving it. That is an import boundary, not a mathematical
cost: `Contractable.conditionallyIIDWith_directingProbabilityMeasure` supplies the witness with no
hypothesis on `Ω` at all, but it belongs to the `L²` route, which this file does not import.
`TauCeti.Probability.DeFinetti.CanonicalMixture` does import it, and states the resulting
witness-free representation theorems for contractable and exchangeable processes.

## Final representation

The Layer 6 bullet in `TauCetiRoadmap/Exchangeability/README.md` asks for the mixture form with `π`
the **unique** law of `ν`. That uniqueness is `mixedIID_mixingLaw_unique`, proved alongside the
generic representation in `Exchangeability/MixedIID/Mixture.lean`; it is stated for `MixedIIDWith`
witnesses and so does not mention `deFinettiMeasure`. The theorem `deFinetti_mixture` in
`TauCeti.Probability.DeFinetti.Representation` derives the unique mixing-law representation from
exchangeability without assuming a witness, and
`eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi` in
`TauCeti.Probability.DeFinetti.CanonicalMixture` identifies its witness with `deFinettiMeasure`.
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
back to `Measure` for the `bind` representation. No measurability is required at construction
time: `Measure.map` of a non-measurable function is a Dirac mass, so the pushforward of a
probability measure is always a probability measure. The identification of this measure with the
mixing law instead uses a `MixedIIDWith` witness, which includes coordinatewise a.e.
measurability. -/
def deFinettiMeasure (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → α) :
    ProbabilityMeasure (ProbabilityMeasure α) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
    (directingProbabilityMeasure μ X)

/-- The underlying measure of the de Finetti measure is the pushforward of the directing measure. -/
@[simp]
theorem deFinettiMeasure_toMeasure {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α} :
    (deFinettiMeasure μ X : Measure (ProbabilityMeasure α))
      = μ.map (directingProbabilityMeasure μ X) := by
  simpa only [deFinettiMeasure, ProbabilityMeasure.coe_mk] using
    ProbabilityMeasure.toMeasure_map
      (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)

/-- **The mixture representation against the de Finetti measure.** When the canonical directing
measure is a mixing representative for `X`, the path law of `X` is the `deFinettiMeasure`-mixture of
the infinite product measures.

The witness hypothesis is taken rather than derived, to keep this file free of any de Finetti proof
route. `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_contractable`, in
`TauCeti.Probability.DeFinetti.CanonicalMixture`, discharges it from contractability alone. -/
theorem pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    (h : MixedIIDWith μ X (directingProbabilityMeasure μ X)) :
    pathLaw μ X
      = (deFinettiMeasure μ X : Measure (ProbabilityMeasure α)).bind
          fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  rw [deFinettiMeasure_toMeasure]
  exact pathLaw_eq_bind_infinitePi_of_mixedIIDWith h

end Probability

end TauCeti
