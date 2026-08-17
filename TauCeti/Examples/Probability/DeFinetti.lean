/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Probability.DeFinetti

/-!
# Worked examples: the de Finetti public API

This file imports **only** `TauCeti.Probability.DeFinetti`, and that is its whole content: each
example is a bare reference to a name Layer 7 advertises, so the file elaborates exactly when the
curated facade exports everything it promises. Nothing is proved and nothing is declared; the
import is not public, so this adds no second route to the API.

A failure here means an export went missing, not that a proof broke: a summit can be proved, and
its module built, while the facade never re-exports it, leaving the name unreachable for a caller
who imports only the facade.

## One advertised name does not exist

Layer 7 spells one endpoint `exchangeable_of_mixedIID`; the repository proves it canonically as
`MixedIID.exchangeable`, which is checked below under that name. No alias is introduced.

`deFinetti_empiricalMeasure` is not currently exported. Unlike the topology-free fixed-set endpoint
below, its weak-convergence statement requires an explicitly chosen compatible Polish topology,
which `[StandardBorelSpace α]` alone does not select.

Every other advertised name is checked below.

## The mathematical worked examples live elsewhere

The roadmap's worked-example list is discharged with the objects each concerns, not here: the
conditionally i.i.d. coin-flip construction in `Exchangeability/ConditionallyIID/CoinFlips.lean`,
the constant-witness characterisation of i.i.d. in `ConditionallyIID/Const.lean`, and the
stationary but non-exchangeable 3-cycle in `Exchangeability/ThreeCycle.lean`.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 7** (public API and examples), whose
  suggested home for this file is `TauCeti/Examples/Probability/DeFinetti.lean`.
-/

open MeasureTheory

namespace TauCeti

namespace Probability

-- The process predicates.
example := @Exchangeable
example := @FullyExchangeable
example := @Contractable
example := @MixedIIDWith
example := @MixedIID
example := @ConditionallyIIDWith
example := @ConditionallyIID

-- Relations between them.
example := @exchangeable_iff_fullyExchangeable
example := @contractable_of_exchangeable
example := @MixedIID.exchangeable
example := @mixedIIDWith_of_conditionallyIIDWith
example := @mixedIID_of_conditionallyIID

-- The summits: unsuffixed is the martingale route, the suffixed ones name theirs.
example := @conditionallyIID_of_contractable
example := @conditionallyIID_of_exchangeable
example := @deFinetti
example := @deFinetti_equivalence
example := @deFinetti_RyllNardzewski_equivalence
example := @mixedIID_of_contractable
example := @deFinetti_viaL2
example := @deFinetti_viaKoopman

-- Representation, disintegration and uniqueness.
example := @ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw
example := @deFinetti_mixture
example := @mixedIID_mixingLaw_unique
example := @conditionallyIID_ae_unique
example := @exchangeable_extreme_iff_iid

-- Empirical-frequency convergence. These two are promised by separate facade imports:
-- `ConditionallyIID.StrongLaw` for the conditional statement, `DeFinetti.EmpiricalMeasure` for the
-- de Finetti endpoint. Neither is re-exported by the other.
example := @ConditionallyIIDWith.tendsto_average_ae
example := @deFinetti_tendsto_empiricalMeasure_apply

/-! ### Using the canonical mixing law -/

section CanonicalMixture

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]

/-- An exchangeable process whose path law happens to be the i.i.d. law `P^{⊗ℕ}` has the point mass
at `P` as its de Finetti measure. -/
example {Ω : Type*} [MeasurableSpace Ω] [Nonempty α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n)) (P : ProbabilityMeasure α)
    (hpath : pathLaw μ X = Measure.infinitePi fun _ : ℕ => (P : Measure α)) :
    (deFinettiMeasure μ X (tailProcess_le_ambient 0 fun j _ => hX_meas j) :
        Measure (ProbabilityMeasure α)) = Measure.dirac P :=
  congrArg ProbabilityMeasure.toMeasure
    (eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi (π := ⟨Measure.dirac P, inferInstance⟩)
      hX_meas
      (by rw [hpath, ← deFinettiBarycenter_dirac P, deFinettiBarycenter_def,
        ProbabilityMeasure.coe_mk])).symm

end CanonicalMixture

end Probability

end TauCeti
