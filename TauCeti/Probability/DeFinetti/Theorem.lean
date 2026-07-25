/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.BlockFactorization
-- Non-public: used only inside proofs — the Layer-0 bridges from conditional i.i.d. back to
-- exchangeability and contractability.
import TauCeti.Probability.Exchangeability.MixedIID.Implications

/-!
# The de Finetti–Ryll-Nardzewski equivalences, mixture form

The equivalence forms of the de Finetti summit, in their **mixture** form: for a process with
measurable coordinates, valued in a nonempty standard Borel space, under a finite measure,

* exchangeable **iff** mixed i.i.d. (`exchangeable_iff_mixedIID`),
* contractable **iff** mixed i.i.d. (`contractable_iff_mixedIID`, the two-way form), and
* contractable **iff** exchangeable and mixed i.i.d.
  (`contractable_iff_exchangeable_and_mixedIID`, the roadmap's conjunction form, derived
  from the two-way form)

— Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1 (pp. 26–28). The
hard direction is the merged reverse-martingale de Finetti chain
(`mixedIID_of_contractable`); the converse directions are the Layer-0 bridges
(`MixedIID.exchangeable`, `MixedIID.contractable`).

The roadmap reserves the names `deFinetti`, `deFinetti_equivalence`, and
`deFinetti_RyllNardzewski_equivalence` for the theorems concluding the genuine `ConditionallyIID`
predicate — the joint-law disintegration — and directs that "summit theorems conclude
`ConditionallyIID`, never merely `MixedIID`"
(`TauCetiRoadmap/Exchangeability/README.md`, Layers 6–7). That predicate is not yet defined here,
so this file deliberately exposes no `deFinetti*` handle: the equivalences below are the mixture
forms, named as such. The handles return with the conditional predicate.

Both equivalences hold on an arbitrary measurable sample space `Ω` under `[IsFiniteMeasure μ]`;
the standard-Borel hypothesis sits only on the state space `α`, each value of the mixing
representative being a probability measure on `α`. (The *mixing law* itself — the law of `ν` — is a
measure on `ProbabilityMeasure α`, not on `α`.)

Adapted from `cameronfreer/exchangeability` (`DeFinetti/TheoremViaMartingale.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`); the statements here are the source's final wrappers,
generalized from `[StandardBorelSpace Ω]` + probability measures to arbitrary measurable `Ω` +
finite measures.

## Main results

* `exchangeable_iff_mixedIID` — de Finetti's theorem as an equivalence, mixture form.
* `contractable_iff_mixedIID` — the two-way Ryll-Nardzewski equivalence, mixture form.
* `contractable_iff_exchangeable_and_mixedIID` — the roadmap's conjunction form.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- **De Finetti's theorem, mixture equivalence form** (Kallenberg, Theorem 1.1). A process with
measurable coordinates, valued in a nonempty standard Borel space, under a finite measure, is
exchangeable iff it is mixed i.i.d. The forward direction is the reverse-martingale
de Finetti chain (`mixedIID_of_exchangeable`); the converse is the mixture computation
`MixedIID.exchangeable`, which needs no side hypotheses. -/
theorem exchangeable_iff_mixedIID [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Exchangeable μ X ↔ MixedIID μ X :=
  ⟨fun hX => mixedIID_of_exchangeable hX hX_meas, fun hX => hX.exchangeable⟩

/-- **De Finetti–Ryll-Nardzewski, two-way mixture form.** A process with measurable coordinates,
valued in a nonempty standard Borel space, under a finite measure, is contractable iff it is mixed
i.i.d. Forward: the reverse-martingale de Finetti chain (`mixedIID_of_contractable`);
converse: `MixedIID.contractable`, which needs no side hypotheses. -/
theorem contractable_iff_mixedIID [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ MixedIID μ X :=
  ⟨fun hX => mixedIID_of_contractable hX hX_meas, fun hX => hX.contractable⟩

/-- **The de Finetti–Ryll-Nardzewski equivalence, mixture form** (Kallenberg, Theorem 1.1), in the
roadmap's conjunction shape: contractable iff exchangeable and mixed i.i.d. Derived from the two-way
`contractable_iff_mixedIID`, with the exchangeability conjunct supplied by
`MixedIID.exchangeable` (the conjunct is redundant given mixed i.i.d., but this is
the shape the roadmap names). -/
theorem contractable_iff_exchangeable_and_mixedIID [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ Exchangeable μ X ∧ MixedIID μ X :=
  (contractable_iff_mixedIID hX_meas).trans
    ⟨fun hX => ⟨hX.exchangeable, hX⟩, And.right⟩

end Probability

end TauCeti
