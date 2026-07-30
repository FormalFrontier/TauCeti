/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.JointRectangle
public import TauCeti.Probability.DeFinetti.BlockFactorization
-- Non-public: used only inside proofs — the Layer-0 bridges `MixedIID.exchangeable` and
-- `MixedIID.contractable`, from the mixture identity back to exchangeability and contractability.
import TauCeti.Probability.Exchangeability.MixedIID.Implications
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map

/-!
# The de Finetti–Ryll-Nardzewski theorem and equivalences

The de Finetti summit in its **conditional** form, together with its conditional and mixture
equivalences.

`conditionallyIID_of_contractable` is the sharp statement: a contractable process valued in a
nonempty standard Borel space is conditionally i.i.d., a joint-law disintegration given a directing
measure. Since exchangeability implies contractability, `conditionallyIID_of_exchangeable` is de
Finetti's theorem in the same sharp form. For a process with measurable coordinates, valued in a
nonempty standard Borel space, under a finite measure, the conditional equivalences read

* exchangeable **iff** conditionally i.i.d. (`deFinetti_equivalence`), and
* contractable **iff** exchangeable and conditionally i.i.d.
  (`deFinetti_RyllNardzewski_equivalence`).

Their integrated-out mixture forms read

* exchangeable **iff** mixed i.i.d. (`exchangeable_iff_mixedIID`),
* contractable **iff** mixed i.i.d. (`contractable_iff_mixedIID`, the two-way form), and
* contractable **iff** exchangeable and mixed i.i.d.
  (`contractable_iff_exchangeable_and_mixedIID`, the roadmap's conjunction form, derived
  from the two-way form)

— Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Theorem 1.1 (pp. 26–28). The
hard direction is the merged reverse-martingale de Finetti chain
(`mixedIID_of_contractable`); the converse directions are the Layer-0 bridges
(`MixedIID.exchangeable`, `MixedIID.contractable`).

The roadmap directs that "summit theorems conclude `ConditionallyIID`, never merely `MixedIID`"
(`TauCetiRoadmap/Exchangeability/README.md`, Layers 6–7). Both conditional implications do so. The
contractable theorem's witness is reachable explicitly:
`conditionallyIIDWith_of_contractable_pathSpace` names the tail conditional law on path space and
`ConditionallyIIDWith.of_pathLaw` transports it.

All theorems hold on an arbitrary measurable sample space `Ω` under `[IsFiniteMeasure μ]`;
the standard-Borel hypothesis sits only on the state space `α`, each value of the mixing
representative being a probability measure on `α`. (The *mixing law* itself — the law of `ν` — is a
measure on `ProbabilityMeasure α`, not on `α`.)

The mixture equivalences are adapted from `cameronfreer/exchangeability`
(`DeFinetti/TheoremViaMartingale.lean`, pin `e0532e59ceff23edab44dda9ab0655debbc9cc22`); those
statements are the source's final wrappers, generalized from `[StandardBorelSpace Ω]` + probability
measures to arbitrary measurable `Ω` + finite measures. The conditional summit is not adapted
from it: that repository's legacy `ConditionallyIID` denotes the mixture identity, so it proves
a strictly weaker statement.

## Main results

* `conditionallyIID_of_contractable` — the conditional summit: contractable implies conditionally
  i.i.d., strengthening the forward direction of `contractable_iff_mixedIID`.
* `conditionallyIID_of_exchangeable`, `deFinetti` — de Finetti's theorem in conditional form.
* `deFinetti_equivalence` — exchangeable iff conditionally i.i.d.
* `deFinetti_RyllNardzewski_equivalence` — contractable iff exchangeable and conditionally i.i.d.
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

/-- **The conditional summit: contractable ⇒ conditionally i.i.d.** A contractable process valued in
a nonempty standard Borel space has a directing measure given which every finite distinct block is
i.i.d., as a joint-law disintegration.

This is the sharp form. It strengthens `contractable_iff_mixedIID`, whose forward direction
concludes only the mixture identity, which the roadmap is explicit should never be mistaken for the
summit. No standard-Borel hypothesis is imposed on the sample space.

The witness is available explicitly: `conditionallyIIDWith_of_contractable_pathSpace` names the tail
conditional law on path space, and `ConditionallyIIDWith.of_pathLaw` transports it here. -/
theorem conditionallyIID_of_contractable [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  exact ConditionallyIID.of_directing
    ((conditionallyIIDWith_of_contractable_pathSpace
      (Contractable.coordinate_pathLaw hX fun i => (hX_meas i).aemeasurable)).of_pathLaw hX_meas)

/-- **De Finetti's theorem, conditional form.** An exchangeable process valued in a nonempty
standard Borel space is conditionally i.i.d. No standard-Borel hypothesis is imposed on the sample
space. -/
theorem conditionallyIID_of_exchangeable [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Exchangeable μ X)
    (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable
    (hX.contractable fun n => (hX_meas n).aemeasurable) hX_meas

/-- **De Finetti's theorem.** An exchangeable process valued in a nonempty standard Borel space is
conditionally i.i.d. This is the conventional theorem-name handle for
`conditionallyIID_of_exchangeable`. -/
theorem deFinetti [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  conditionallyIID_of_exchangeable hX hX_meas

/-- **De Finetti's theorem as an equivalence.** A process with measurable coordinates, valued in a
nonempty standard Borel space, is exchangeable iff it is conditionally i.i.d. -/
theorem deFinetti_equivalence [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) :
    Exchangeable μ X ↔ ConditionallyIID μ X :=
  ⟨fun hX => conditionallyIID_of_exchangeable hX hX_meas,
    fun hX => hX.exchangeable⟩

/-- **The de Finetti–Ryll-Nardzewski equivalence.** A process with measurable coordinates, valued
in a nonempty standard Borel space, is contractable iff it is both exchangeable and conditionally
i.i.d. -/
theorem deFinetti_RyllNardzewski_equivalence [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) :
    Contractable μ X ↔ Exchangeable μ X ∧ ConditionallyIID μ X := by
  constructor
  · intro hX
    have hX_cond := conditionallyIID_of_contractable hX hX_meas
    exact ⟨hX_cond.exchangeable, hX_cond⟩
  · exact fun hX => hX.2.contractable

end Probability

end TauCeti
