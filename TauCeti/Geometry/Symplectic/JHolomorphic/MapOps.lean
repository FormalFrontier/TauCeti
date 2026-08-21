/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Congruence
public import TauCeti.Geometry.Symplectic.JHolomorphic.Neg
public import TauCeti.Geometry.Symplectic.JHolomorphic.Transport

/-!
# Operations preserving constant-structure `J`-holomorphic maps

This file is the aggregate import for elementary map-level operations under which the
normed-vector-space constant-structure `J`-holomorphic predicates are invariant, used by the
analytic Heegaard Floer roadmap.

* **Negation.** A real-linear map satisfies `F ∘ J = J' ∘ F` exactly when it satisfies the same
  equation after both almost complex structures are negated, `F ∘ (-J) = (-J') ∘ F`, so the
  predicate is unchanged when both structures change sign.
* **Congruence.** A constant-structure `J`-holomorphic condition depends only on a local
  representative of the map near the point or within the source set, because the underlying
  Frechet derivative is local under eventual equality.
* **Transport.** The predicate is invariant under continuous real-linear changes of source and
  target coordinates: if `f : V → W` is constant-structure `J`-holomorphic and `eV : V ≃L[ℝ] V'`,
  `eW : W ≃L[ℝ] W'`, then `v' ↦ eW (f (eV.symm v'))` is constant-structure `J`-holomorphic for the
  transported almost complex structures. The structures are transported by the linear-algebra API
  in `TauCeti.Geometry.Symplectic.Transport`; `JHolomorphicTransport` adds the matching map-level
  calculus.

These lemmas are the chart-level bookkeeping needed before the roadmap upgrades the local
Cauchy--Riemann equation to almost complex manifolds, where maps are constantly replaced by equal
local representatives in overlapping charts, restricted domains are reflected or reoriented, and
tangent charts change coordinates.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.neg_neg` and its within-set, setwise, and global
  analogues, with the rewrite-friendly `TauCeti.isConstStructureJHolomorphicAt_neg_neg_iff` family:
  invariance under negating both almost complex structures.
* `TauCeti.IsConstStructureJHolomorphicAt.congr_of_eventuallyEq`,
  `TauCeti.IsConstStructureJHolomorphicWithinAt.congr_mono`,
  `TauCeti.isConstStructureJHolomorphicWithinAt_congr_set_nhdsNE`,
  `TauCeti.IsConstStructureJHolomorphicOn.congr`, and their equivalence forms: the locality API.
* `TauCeti.IsConstStructureJHolomorphicAt.transport` and its within-set, setwise, and global
  analogues, with the `TauCeti.isConstStructureJHolomorphicAt_transport_iff` family: invariance
  under continuous real-linear coordinate changes.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: constant-structure `J`-holomorphicity is the Cauchy--Riemann equation
`df ∘ J = J' ∘ df`, and coordinate changes conjugate both `J` and `df`. The congruence proofs are
thin wrappers around Mathlib's Frechet-derivative congruence lemmas in
`Mathlib.Analysis.Calculus.FDeriv.Congr`.
-/

public section

namespace TauCeti

end TauCeti
