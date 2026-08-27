/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# The group sum of a finite-group representation has the invariants as its range

Mathlib names the group sum `∑ g, ρ g` of a finite-group representation `Representation.norm`,
builds the averaging projection `Representation.averageMap` separately out of the group-algebra
element `GroupAlgebra.average`, and records that the latter projects onto the invariants
(`Representation.isProj_averageMap`). What it does not record is how the two operators relate.
The group sum is the shape a symmetrization operator actually takes at a use site, where the
normalizing factor `⅟(#G)` is usually left implicit, and reinstating it by hand is the step that
gets rewritten.

This file supplies the bridge. Unfolding the group algebra once identifies `averageMap` with
`norm` scaled by `⅟(#G)`, and since scaling by a unit changes no image, `norm` has the same range
as the projection: the invariants.

## Main results

* `Representation.averageMap_eq_invOf_card_smul_norm`: the averaging projection is the group sum
  `Representation.norm` scaled by the inverse of the group order.
* `Representation.range_norm_eq_invariants`: the group sum `Representation.norm ρ` has the
  invariants as its range.
-/
public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]

/-- **The averaging projection is the normalized group sum.** Mathlib defines
`Representation.averageMap` through the group algebra; this unfolds that definition to the group sum
`Representation.norm`, scaled by the inverse of the group order. -/
theorem averageMap_eq_invOf_card_smul_norm :
    ρ.averageMap = ⅟(Fintype.card G : k) • ρ.norm := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, norm]

/-- **The group sum has the invariants as its range.** When `#G` is invertible in `k`, the operator
`Representation.norm ρ = ∑ g, ρ g` maps onto the invariants of `ρ`: it agrees with the averaging
projection up to the unit `#G`, so the two have the same image. -/
@[simp]
theorem range_norm_eq_invariants : LinearMap.range ρ.norm = ρ.invariants := by
  rw [← ρ.isProj_averageMap.range, averageMap_eq_invOf_card_smul_norm]
  refine le_antisymm ?_ (LinearMap.range_smul_le_range _ _)
  convert LinearMap.range_smul_le_range (⅟(Fintype.card G : k) • ρ.norm) (Fintype.card G : k)
  rw [smul_smul, mul_invOf_self, one_smul]

end Representation
