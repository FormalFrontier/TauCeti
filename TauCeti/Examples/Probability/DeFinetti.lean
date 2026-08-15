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

A failure here means an export went missing, not that a proof broke — the gap this guards against
is the one where `deFinetti_viaL2` existed on `main` for some time without being reachable from the
facade.

## Two advertised names do not exist

Layer 7's list includes two declarations that are absent from the repository, so they cannot be
checked here:

* `exchangeable_of_mixedIID` — only the converse, `mixedIID_of_exchangeable`, is proved;
* `deFinetti_empiricalMeasure` — not started, and blocked on a roadmap decision recorded in
  `Exchangeability/STATUS.md`: under `[StandardBorelSpace α]` alone no compatible Polish topology
  is selected, so the target as worded is not yet well-posed.

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

end Probability

end TauCeti
