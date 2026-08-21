/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# A submodule of a topological module is a topological module

A submodule carries the subspace topology. Of the three continuity classes that make that
topology a module topology, Mathlib supplies **one outright** and **one under extra hypotheses**:

* `SMulMemClass.continuousSMul` gives the jointly continuous action `A × ↥p → ↥p` on any `SetLike`
  subobject, with no side conditions beyond the ambient `ContinuousSMul A M`. This file adds
  nothing there.
* `Submodule.topologicalAddGroup` gives `ContinuousAdd ↥p`, but only for a `Ring A` acting on an
  `AddCommGroup M` that is already a topological *group*.

So there are exactly two gaps, and they are what this file fills:

* **`ContinuousAdd` at the generality of its own class** — an `AddCommMonoid` ambient with
  `ContinuousAdd` is outside `Submodule.topologicalAddGroup`'s hypotheses, and
  `AddSubmonoid.continuousAdd`, which is at the right generality, is not keyed on `Submodule`.
* **`ContinuousConstSMul` with no topology on the scalars** — `SMulMemClass.continuousSMul` needs
  a topology on `A` and `ContinuousSMul A M`, whereas
  `TauCeti.Huber.restrictedMvPowerSeriesSubmodule` asks only for `ContinuousConstSMul A M` with
  `A` untopologised. That is the form this instance is for.

## Main results

* `Submodule.continuousAdd`: addition on `↥p` is continuous, asking only `ContinuousAdd` of the
  ambient module rather than a topological group structure.
* `Submodule.continuousConstSMul`: each scalar acts continuously on `↥p`, with no topology on the
  scalars.
-/

public section

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]

/-- **Addition on a submodule is continuous.** Mathlib has this for an `AddSubmonoid`, and for a
`Submodule` only through `Submodule.topologicalAddGroup`, which needs the ambient module to be a
topological group. A `ContinuousAdd` ambient is enough. -/
instance continuousAdd [ContinuousAdd M] (p : Submodule A M) : ContinuousAdd p :=
  inferInstanceAs (ContinuousAdd p.toAddSubmonoid)

/-- **Each scalar acts continuously on a submodule**, since it does so on the ambient module and
the action is the restriction of that one. -/
instance continuousConstSMul [ContinuousConstSMul A M] (p : Submodule A M) :
    ContinuousConstSMul A p :=
  Topology.IsInducing.subtypeVal.continuousConstSMul id rfl

end Submodule
