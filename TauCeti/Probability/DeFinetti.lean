/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability
public import TauCeti.Probability.DeFinetti.Theorem
public import TauCeti.Probability.DeFinetti.Representation
public import TauCeti.Probability.DeFinetti.CountableIndex
public import TauCeti.Probability.Exchangeability.MixedIID.Mixture
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Unique

/-!
# De Finetti's theorem

The completed representation API: the summit theorems, their equivalence forms, the unique mixture
representation, both uniqueness statements, and the countable-index extension.

This module declares nothing of its own; it is a curated re-export, and it builds on
`TauCeti.Probability.Exchangeability` rather than duplicating it.

## What is here

* `conditionallyIID_of_contractable` — the summit: contractable implies conditionally i.i.d.;
* `conditionallyIID_of_exchangeable` and `deFinetti` — de Finetti's theorem in conditional form;
* `deFinetti_equivalence`, `deFinetti_RyllNardzewski_equivalence` — the equivalence forms;
* `deFinetti_mixture` — the unique mixture representation;
* `mixedIID_mixingLaw_unique` — uniqueness of the mixing *law*;
* `conditionallyIID_ae_unique` — a.e. uniqueness of the directing *measure*;
* `conditionallyIID_of_exchangeableFamily` — the countable-index extension.

The two uniqueness statements are genuinely different, and the difference is the point of the
conditional predicate: only the law `μ.map ν` is pinned down by the mixture identity, whereas a
directing measure is pinned down almost everywhere.

## What is deliberately not here

Route-specific endpoints. The `L²` and Koopman developments are not complete, so no `viaL2` or
`viaKoopman` names exist to export; this facade grows when they land. Likewise the empirical and
extreme-point work beyond what has already merged.

Worked examples are also excluded, and are reachable from their own modules.
-/
