/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.Correspondence
-- Non-public: used only inside proofs — the canonical directing measure is a `ConditionallyIIDWith`
-- witness for any contractable process, which is what turns `deFinettiMeasure` into *the* mixing
-- law. No declaration of it occurs in an exported signature.
import TauCeti.Probability.DeFinetti.ViaL2.ConditionallyIID
-- Non-public: `exchangeable_iff_exchangeableLaw_pathLaw` derives the process-level exchangeability
-- that the identification theorems no longer take as a hypothesis.
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge

/-!
# The de Finetti measure is the mixing law

The development names the mixing law of an exchangeable process three times:

* `deFinettiMeasure μ X hTail`, the law of the canonical tail directing measure
  (`DeFinetti/Mixture.lean`);
* the unique witness `π` produced by `deFinetti_mixture` (`DeFinetti/Representation.lean`);
* `deFinettiEquiv.symm ρ`, the mixing law read off an exchangeable path law
  (`DeFinetti/Correspondence.lean`).

This file proves they agree. The first is a construction on the sample space, the second an
existential characterization of the path law, and the third the inverse of a bijection; without
these identifications a caller holding one of them cannot use the theorems stated about the others.

## Main results

* `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_contractable` and
  `..._of_exchangeable` — the mixture representation directly from contractability or
  exchangeability, with no witness supplied by the caller.
* `eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi` — *every* mixing law representing the path
  law is `deFinettiMeasure`; this is what identifies the `deFinetti_mixture` witness.
* `deFinettiEquiv_symm_eq_deFinettiMeasure` — the correspondence reads `deFinettiMeasure` off the
  packaged path law.

## Hypotheses

The witness that drives everything here is
`Contractable.conditionallyIIDWith_directingProbabilityMeasure`: a contractable process with
measurable coordinates, valued in a nonempty standard Borel state space, under a finite measure,
has `directingProbabilityMeasure μ X` as a directing measure. No standard-Borel hypothesis is
imposed on the sample space `Ω`, so neither is one imposed below; a probability base measure is
needed only because `deFinettiMeasure` is bundled as a `ProbabilityMeasure`.

`[Nonempty α]` cannot be dropped here even though a probability measure on `Ω` together with `X 0`
exhibits a point of `α`: it is not only a hypothesis. `deFinettiMeasure` is built from
`condDistrib`, so the instance is needed to *elaborate the statements themselves*, not just to
prove them.

The coordinates must be exactly measurable for two concrete reasons, neither of which is about
`deFinettiMeasure` itself — that elaborates for an arbitrary `X`, taking only a tail-measurability
bound. First, `Contractable.conditionallyIIDWith_directingProbabilityMeasure`, which supplies the
witness, asks for `∀ n, Measurable (X n)`. Second, the bound handed to `deFinettiMeasure` is built
here as `tailProcess_le_ambient 0 fun j _ => hX_meas j`, which needs measurable coordinates to
produce it.

## Why the `L²` route supplies the witness

The theorems below carry no route suffix, yet the witness comes from the `L²` route. That is not a
route claim: `deFinettiMeasure` is the law of `directingProbabilityMeasure μ X`, and the `L²`
route's conditional summit is the one that names *that* object. The martingale route reaches the
conditional summit through `conditionallyIIDWith_of_contractable_pathSpace`, whose witness lives on
path space, and its mixture-side `mixedIIDWith_of_contractable` names the canonical directing
measure only under `[StandardBorelSpace Ω]`. Taking the witness from the `L²` route is therefore
what keeps that hypothesis out of these statements; a martingale-route proof would give a strictly
weaker theorem, not a differently-named one.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 6** (the mixture-of-product-measures
  form with `π` the unique law of `ν`) and **Layer 8** (the affine correspondence). This file adds
  no new mathematics to either; it connects the objects those bullets produce.
* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- **The mixture representation of a contractable process**, against its own de Finetti measure.
Unlike `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith`, no witness is asked of the
caller: the canonical directing measure is one, by
`Contractable.conditionallyIIDWith_directingProbabilityMeasure`. -/
theorem pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_contractable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    pathLaw μ X
      = (deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) :
          Measure (ProbabilityMeasure α)).bind
          fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_mixedIIDWith hX_meas
    (mixedIIDWith_of_conditionallyIIDWith
      (hX.conditionallyIIDWith_directingProbabilityMeasure hX_meas))

/-- **The de Finetti representation of an exchangeable process**, against its own de Finetti
measure. This is `deFinetti_mixture` with the existential witness replaced by the canonical
construction. -/
theorem pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_exchangeable {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} (hX : Exchangeable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    pathLaw μ X
      = (deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) :
          Measure (ProbabilityMeasure α)).bind
          fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_contractable
    (hX.contractable fun n => (hX_meas n).aemeasurable) hX_meas

/-- **The de Finetti measure is the unique mixing law.** Any probability measure on
`ProbabilityMeasure α` representing the path law of an exchangeable process as an infinite-product
mixture is `deFinettiMeasure`.

In particular the witness returned by `deFinetti_mixture` is this one, so a concrete mixing law
established by any other route can be compared with the canonical construction.

Exchangeability is not assumed: `hπ` already exhibits the path law as a de Finetti barycenter, and
every barycenter of a mixing probability law is an exchangeable path law. -/
theorem eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {π : ProbabilityMeasure (ProbabilityMeasure α)}
    (hπ : pathLaw μ X = (π : Measure (ProbabilityMeasure α)).bind
      fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) :
    π = deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) := by
  have hlaw : ExchangeableLaw (pathLaw μ X) := by
    rw [hπ, ← deFinettiBarycenter_def]
    exact exchangeableLaw_deFinettiBarycenter
  have hX : Exchangeable μ X :=
    (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hX_meas n).aemeasurable).2 hlaw
  obtain ⟨π₀, -, huniq⟩ := deFinetti_mixture hX fun n => (hX_meas n).aemeasurable
  rw [huniq π hπ,
    huniq _ (pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_exchangeable hX hX_meas)]

/-- **The correspondence recovers the de Finetti measure.** Reading the mixing law off the path law
of an exchangeable process, through the inverse of `deFinettiEquiv`, gives the canonical
`deFinettiMeasure`.

The packaged exchangeable law is taken as a hypothesis rather than constructed, so the caller may
supply whichever bundling of `pathLaw μ X` is at hand. Exchangeability of the process is not
assumed separately: `ρ.2` and `hρ` already say the path law is exchangeable. -/
theorem deFinettiEquiv_symm_eq_deFinettiMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {ρ : {ρ : ProbabilityMeasure (ℕ → α) // ExchangeableLaw (ρ : Measure (ℕ → α))}}
    (hρ : ((ρ : ProbabilityMeasure (ℕ → α)) : Measure (ℕ → α)) = pathLaw μ X) :
    deFinettiEquiv.symm ρ
      = deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) := by
  have hX : Exchangeable μ X :=
    (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hX_meas n).aemeasurable).2 (hρ ▸ ρ.2)
  exact deFinettiEquiv_symm_eq
    (by rw [hρ, deFinettiBarycenter_def]
        exact pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_exchangeable hX hX_meas)

end Probability

end TauCeti
