/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability
public import TauCeti.Probability.DeFinetti.Representation
public import TauCeti.Probability.DeFinetti.ViaL2.Theorem
public import TauCeti.Probability.DeFinetti.ViaKoopman.Theorem
public import TauCeti.Probability.DeFinetti.CountableIndex
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Unique
public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Extreme
public import TauCeti.Probability.Exchangeability.PathSpace.Law.ZeroOne
public import TauCeti.Probability.DeFinetti.Correspondence
public import TauCeti.Probability.DeFinetti.CanonicalMixture
public import TauCeti.Probability.Exchangeability.ConditionallyIID.WeakConvergence
public import TauCeti.Probability.DeFinetti.EmpiricalMeasure
public import TauCeti.Probability.DeFinetti.Coding

/-!
# De Finetti's theorem

The completed representation API: the summit theorems, their equivalence forms, the unique mixture
representation, both uniqueness statements, the countable-index extension, and the correspondence
between mixing laws and exchangeable path laws.

This module declares nothing of its own; it is a curated re-export, and it builds on
`TauCeti.Probability.Exchangeability` rather than duplicating it.

## What is here

* `conditionallyIID_of_contractable` — the summit: contractable implies conditionally i.i.d.;
* `conditionallyIID_of_exchangeable` and `deFinetti` — de Finetti's theorem in conditional form;
* `deFinetti_equivalence`, `contractable_iff_conditionallyIID`,
  `deFinetti_RyllNardzewski_equivalence` — the equivalence forms. These and the summits above ask
  only for a.e. measurable coordinates, matching the uniqueness endpoints below;
* `deFinetti_viaL2`, `conditionallyIID_of_contractable_viaL2` and
  `deFinetti_RyllNardzewski_equivalence_viaL2` — the same summits proved by the `L²` averaging
  route rather than the martingale one. The unsuffixed names above are the martingale route;
  the suffixed ones name the route explicitly, and are what Layer 7 of the roadmap advertises;
* `deFinetti_viaKoopman` and `conditionallyIID_of_contractable_viaKoopman` — the same summits proved
  by the Koopman route, through the shift-invariant σ-algebra rather than the tail. The three route
  modules are independent at the import level: none imports another;
* `deFinetti_mixture` — the unique mixture representation;
* `mixedIID_mixingLaw_unique` — uniqueness of the mixing *law*;
* `conditionallyIID_ae_unique` — a.e. uniqueness of the directing *measure*;
* `conditionallyIID_of_exchangeableFamily` — the countable-index extension;
* `exchangeable_extreme_iff_iid` — the extreme exchangeable laws are exactly the i.i.d. laws;
* `ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw` — the full-path joint disintegration;
* `exchangeableSigma_trivial_iff_iid` — an exchangeable law is a product law exactly when its
  exchangeable σ-algebra is trivial;
* `deFinettiBarycenter` and `deFinettiEquiv` — the affine correspondence carrying a mixing law to
  its exchangeable path law, with `deFinettiBarycenter_mem_extremePoints_iff` identifying the
  point masses with the extreme laws and
  `deFinettiEquiv_convexComb` / `deFinettiEquiv_symm_convexComb` giving the affinity in both
  directions, at the bundled level;
* `deFinettiMeasure` and its identifications —
  `pathLaw_eq_bind_infinitePi_deFinettiMeasure_of_exchangeable`,
  `eq_deFinettiMeasure_of_pathLaw_eq_bind_infinitePi` and
  `deFinettiEquiv_symm_eq_deFinettiMeasure` — tying the canonical directing measure's law to the
  `deFinetti_mixture` witness and to the inverse of the correspondence;
* `deFinetti_tendsto_empiricalMeasure_apply` — on each fixed measurable set, the mass given by the
  directing measure of an exchangeable process is the almost-sure limit of the empirical
  frequencies, with `ConditionallyIIDWith.tendsto_average_ae` the conditional strong law behind it;
* `deFinetti_empiricalMeasure` — on a Polish state space, the directing measure is the almost-sure
  weak limit of the empirical measures themselves, with
  `ConditionallyIIDWith.tendsto_empiricalMeasure_ae` its conditional form;
* `deFinetti_coding` — the functional form of the representation: the joint law of the directing
  measure and an exchangeable process is the law of their coded pair, formed from an independent
  i.i.d. uniform sequence under the fixed measurable map `unitIntervalCoding`, with
  `exchangeableLaw_iff_exists_coding` the resulting path-law equivalence.

The two uniqueness statements are genuinely different, and the difference is the point of the
conditional predicate: only the law `μ.map ν` is pinned down by the mixture identity, whereas a
directing measure is pinned down almost everywhere.

## Scope

This facade exports the stable representation and uniqueness API. Proof routes keep their own
endpoints and internals in their own modules, and the worked examples live with the examples;
both are reachable directly.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 7** (public API), which specifies
  this facade and the symmetry facade it builds on.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), Theorem 1.1,
  for the representation theorem this module exposes.
-/
