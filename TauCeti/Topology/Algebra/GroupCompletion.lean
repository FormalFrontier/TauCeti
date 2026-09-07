/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import TauCeti.Topology.UniformSpace.Completion

/-!
# Countable generation of `𝓝 0` passes to the separated completion

The zero-point form of `UniformSpace.Completion.isCountablyGenerated_nhds_coe`, registered as an
instance. Only a zero and a uniformity are needed; no group structure, no separation, no
completeness.

It exists because results in the Huber development carry `[(𝓝 (0 : A)).IsCountablyGenerated]` and
are applied with `A` a completion — in particular to `A⟨X₁,…,Xₖ⟩`, the completion of the
restricted-series subring, where
`TauCeti.Huber.isCountablyGenerated_nhds_zero_weightedRestrictedSubring` supplies the property
downstairs and this carries it up.

## Main results

* `UniformSpace.Completion.isCountablyGenerated_nhds_zero`.
-/

public section

open Filter
open scoped Topology

namespace UniformSpace.Completion

/-- **Countable generation of `𝓝 0` passes to the separated completion.**

An instance rather than a theorem because it is consumed by typeclass resolution, whereas the
general statement it specialises is about an arbitrary point and cannot be. -/
instance isCountablyGenerated_nhds_zero {G : Type*} [Zero G] [UniformSpace G]
    [(𝓝 (0 : G)).IsCountablyGenerated] : (𝓝 (0 : Completion G)).IsCountablyGenerated := by
  have h := isCountablyGenerated_nhds_coe (x := (0 : G))
  rwa [coe_zero] at h

end UniformSpace.Completion

end
