/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# The compact-open topology on maps out of a compact space into a discrete space

A continuous map `f` from a compact space to a discrete space has finite image, and each of its
fibres is closed, hence compact. Prescribing the value of a map on each of those finitely many
fibres is therefore a finite intersection of compact-open subbasic sets, so it is an open
condition, and it pins the map down to `f` itself. Consequently `C(X, Y)` is discrete.

Compactness of `X` is used and not merely convenient: for `X = ℕ` discrete and `Y = Bool` the
compact subsets of `X` are the finite ones, so the compact-open topology on `C(ℕ, Bool)` is the
product topology, which is not discrete.
-/

public section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The compact-open topology on the continuous maps from a compact space to a discrete space is
discrete. -/
instance discreteTopology [CompactSpace X] [DiscreteTopology Y] :
    DiscreteTopology C(X, Y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro f
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have hset : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨?_, fun h ↦ ext fun x ↦ h (f x) ⟨x, rfl⟩ rfl⟩
    rintro rfl _ _ _ hx
    exact hx
  rw [hset]
  exact hfin.isOpen_biInter fun y _ ↦ isOpen_setOfPred_mapsTo
    (isClosed_singleton.preimage f.continuous).isCompact (isOpen_discrete _)

end ContinuousMap
