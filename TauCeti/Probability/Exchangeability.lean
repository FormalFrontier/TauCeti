/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.FullyExchangeable
public import TauCeti.Probability.Exchangeability.Map
public import TauCeti.Probability.Exchangeability.Family
public import TauCeti.Probability.Exchangeability.FiniteMarginals
public import TauCeti.Probability.Exchangeability.IID
public import TauCeti.Probability.Exchangeability.MixedIID.Implications
public import TauCeti.Probability.Exchangeability.MixedIID.Const
public import TauCeti.Probability.Exchangeability.MixedIID.Map
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Implications
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Const
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Exchangeability: the symmetry layer

The reusable symmetry API — predicates, their basic implications, reindexing, closure under
coordinate maps, and the path-law bridges — without de Finetti's theorem.

This module declares nothing of its own; it is a curated re-export.

## What is here

* the finite-dimensional laws `blockLaw`, `prefixLaw`, `pathLaw`, and finite-marginal uniqueness;
* the symmetry predicates `ExchangeableAt`, `Exchangeable`, `FullyExchangeable`, `Contractable`,
  and the index-generic `ExchangeableFamily`;
* the representation predicates `MixedIIDWith`, `MixedIID`, `ConditionallyIIDWith`,
  `ConditionallyIID`, with their constructors, accessors, and simp-normal forms;
* the implications between them, including the symmetry consequences of each and the projection
  from the conditional predicate to the mixture one;
* reindexing along injections, and closure under measurable coordinate maps;
* the constant-witness (i.i.d.) degenerate case.

## What is deliberately not here

**De Finetti's theorem and everything that concludes it** — import
`TauCeti.Probability.DeFinetti` for that. The dependency runs one way: the de Finetti facade builds
on this one, never the reverse, and this module does not transitively import
`TauCeti.Probability.DeFinetti.Theorem`.

Also excluded: the martingale, `L²`, and Koopman route internals; the Hewitt–Savage and path-space
σ-field development; and the worked examples. Those are reachable by importing their own modules,
and are not part of the curated surface.
-/
