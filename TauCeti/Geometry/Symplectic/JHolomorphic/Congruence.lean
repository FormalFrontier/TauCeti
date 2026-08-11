/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic

/-!
# Congruence lemmas for constant-structure `J`-holomorphic maps

This file records the locality API for the normed-vector-space constant-structure `J`-holomorphic
predicates used
by the analytic Heegaard Floer roadmap. A constant-structure `J`-holomorphic condition depends only
on a local
representative of the map near the point or within the source set, because the underlying
Frechet derivative has the same locality property.

These lemmas are the chart-level bookkeeping needed before the roadmap upgrades the local
Cauchy--Riemann equation to almost complex manifolds, where maps are constantly replaced by
equal local representatives in overlapping charts and restricted domains.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.congr_of_eventuallyEq`: pointwise locality under equality
in a
  neighborhood.
* `TauCeti.IsConstStructureJHolomorphicWithinAt.congr_of_eventuallyEq` and
  `TauCeti.IsConstStructureJHolomorphicWithinAt.congr_mono`: within-set locality under equality in
  the
  source filter or on a smaller source set.
* `TauCeti.isConstStructureJHolomorphicWithinAt_congr_set_nhdsNE`: changing the source set near the
base
  point in a punctured neighborhood.
* `TauCeti.IsConstStructureJHolomorphicOn.congr_mono`, `IsConstStructureJHolomorphicOn.congr`, and
  `isConstStructureJHolomorphicOn_congr`: setwise congruence API.

The proofs are thin wrappers around Mathlib's Frechet-derivative congruence lemmas in
`Mathlib.Analysis.Calculus.FDeriv.Congr`.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

variable {V W : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f g : V → W} {s t : Set V} {x : V}

/-- Pointwise constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in a
neighborhood of the point. -/
lemma IsConstStructureJHolomorphicAt.congr_of_eventuallyEq
    (hf : IsConstStructureJHolomorphicAt J J' f x)
    (hfg : g =ᶠ[𝓝 x] f) : IsConstStructureJHolomorphicAt J J' g x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt
    (hf.hasFDerivAt.congr_of_eventuallyEq hfg) hf.derivative_isComplexLinear

/-- Pointwise constant-structure `J`-holomorphicity is unchanged under local equality near the
point. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicAt_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsConstStructureJHolomorphicAt J J' f x ↔ IsConstStructureJHolomorphicAt J J' g x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm,
    fun hg => hg.congr_of_eventuallyEq hfg⟩

/-- A pointwise constant-structure `J`-holomorphic map may be replaced by a map equal to it
everywhere. -/
lemma IsConstStructureJHolomorphicAt.congr (hf : IsConstStructureJHolomorphicAt J J' f x)
    (hfg : ∀ y, g y = f y) : IsConstStructureJHolomorphicAt J J' g x :=
  hf.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

/-- Pointwise constant-structure `J`-holomorphicity is invariant under pointwise equality of
maps. -/
lemma isConstStructureJHolomorphicAt_congr (hfg : ∀ y, f y = g y) :
    IsConstStructureJHolomorphicAt J J' f x ↔ IsConstStructureJHolomorphicAt J J' g x :=
  (Filter.EventuallyEq.isConstStructureJHolomorphicAt_iff (Filter.Eventually.of_forall hfg))

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in the
source-set neighborhood filter, provided the values also agree at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_of_eventuallyEq
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f)
    (hx : g x = f x) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.congr_of_eventuallyEq hfg hx)
    hf.derivative_isComplexLinear

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in the
source-set neighborhood filter, when the base point belongs to the source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_of_eventuallyEq_of_mem
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set constant-structure `J`-holomorphicity is unchanged under local equality in the
source-set
neighborhood filter, provided the values agree at the base point. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : f x = g x) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' g s x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm hx.symm,
    fun hg => hg.congr_of_eventuallyEq hfg hx⟩

/-- Within-set constant-structure `J`-holomorphicity is unchanged under local equality in the
source-set
neighborhood filter, when the base point belongs to the source set. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff_of_mem (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : x ∈ s) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' g s x :=
  Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by an equal
map on the
source set and at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : g x = f x) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg.eventuallyEq_nhdsWithin hx

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by an equal
map on the
source set, when the base point belongs to the source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr'
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : x ∈ s) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr hfg (hfg hx)

/-- Restrict the source set and replace a within-set constant-structure `J`-holomorphic map by one
equal to it on
the smaller source set and at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_mono
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : g x = f x) (hts : t ⊆ s) :
    IsConstStructureJHolomorphicWithinAt J J' g t x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.congr_mono hfg hx hts) hf.derivative_isComplexLinear

/-- Restrict the source set and replace a within-set constant-structure `J`-holomorphic map by one
equal to it on
the smaller source set, when the base point belongs to that smaller source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_mono'
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : x ∈ t) (hts : t ⊆ s) :
    IsConstStructureJHolomorphicWithinAt J J' g t x :=
  hf.congr_mono hfg (hfg hx) hts

/-- Within-set constant-structure `J`-holomorphicity is invariant under changing the source set in a
punctured
neighborhood of the base point. -/
lemma isConstStructureJHolomorphicWithinAt_congr_set_nhdsNE (hst : s =ᶠ[𝓝[≠] x] t) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f t x := by
  constructor
  · intro hf
    rcases (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf with
      ⟨f', hf', hlin⟩
    exact (isConstStructureJHolomorphicWithinAt_iff J J' f t x).mpr
      ⟨f', (hasFDerivWithinAt_congr_set_nhdsNE hst).mp hf', hlin⟩
  · intro hf
    rcases (isConstStructureJHolomorphicWithinAt_iff J J' f t x).mp hf with
      ⟨f', hf', hlin⟩
    exact (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mpr
      ⟨f', (hasFDerivWithinAt_congr_set_nhdsNE hst).mpr hf', hlin⟩

/-- Setwise constant-structure `J`-holomorphicity on a smaller source set is unchanged after
replacing a map by
one equal to it on that smaller source set. -/
lemma IsConstStructureJHolomorphicOn.congr_mono (hf : IsConstStructureJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f t) (hts : t ⊆ s) : IsConstStructureJHolomorphicOn J J' g t :=
  isConstStructureJHolomorphicOn_of_forall fun x hx =>
    have hxgf : g x = f x := hfg hx
    (hf.isConstStructureJHolomorphicWithinAt (hts hx)).congr_mono hfg hxgf hts

/-- Setwise constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal to
it on the
source set. -/
lemma IsConstStructureJHolomorphicOn.congr (hf : IsConstStructureJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f s) : IsConstStructureJHolomorphicOn J J' g s :=
  hf.congr_mono hfg (fun _ hx => hx)

/-- Setwise constant-structure `J`-holomorphicity is invariant under equality of maps on the source
set. -/
lemma isConstStructureJHolomorphicOn_congr (hfg : Set.EqOn f g s) :
    IsConstStructureJHolomorphicOn J J' f s ↔ IsConstStructureJHolomorphicOn J J' g s :=
  ⟨fun hf => hf.congr fun _ hx => (hfg hx).symm,
    fun hg => hg.congr hfg⟩

/-- A globally constant-structure `J`-holomorphic map may be replaced by a pointwise equal map. -/
lemma IsConstStructureJHolomorphic.congr (hf : IsConstStructureJHolomorphic J J' f)
    (hfg : ∀ x, g x = f x) :
    IsConstStructureJHolomorphic J J' g :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).congr hfg

/-- Global constant-structure `J`-holomorphicity is invariant under pointwise equality of maps. -/
lemma isConstStructureJHolomorphic_congr (hfg : ∀ x, f x = g x) :
    IsConstStructureJHolomorphic J J' f ↔ IsConstStructureJHolomorphic J J' g :=
  ⟨fun hf => hf.congr fun x => (hfg x).symm,
    fun hg => hg.congr hfg⟩

end TauCeti
