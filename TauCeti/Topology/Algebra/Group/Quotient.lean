/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Quotients of topological groups by normal subgroups

Generic facts about the quotient of a topological group by a normal subgroup, phrased for the
unbundled classes `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`: neither compactness
nor total disconnectedness is needed, so the results apply in particular to profinite groups.

## Main results

* `QuotientGroup.isClopen_image_mk`: the image of an open normal subgroup of `G` under the
  quotient map `G → G ⧸ N` is clopen.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
  [N.Normal]

/-- The image of an open normal subgroup of `G` in the quotient by a normal subgroup `N` is
clopen: it is open because the quotient map is open, and closed because it is an open
subgroup of the topological group `G ⧸ N`. -/
theorem isClopen_image_mk (U : OpenNormalSubgroup G) :
    IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) := by
  have hopen : IsOpen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) :=
    QuotientGroup.isOpenMap_coe _ U.toOpenSubgroup.isOpen'
  have heq : (QuotientGroup.mk : G → G ⧸ N) '' (U : Set G) =
      (Subgroup.map (QuotientGroup.mk' N) U.toOpenSubgroup.toSubgroup : Set (G ⧸ N)) := by
    -- `(U : Set G)` coerces through the `OpenNormalSubgroup` `SetLike` instance, while
    -- `Subgroup.coe_map` is stated for the `Set G` coercion of the underlying `Subgroup`.
    -- The two coercions are definitionally equal and Mathlib provides no lemma bridging
    -- them, so the normalization below can only go through `rfl`.
    rw [show (U : Set G) = ((↑U : Subgroup G) : Set G) from rfl]
    exact (Subgroup.coe_map (QuotientGroup.mk' N) U.toOpenSubgroup.toSubgroup).symm
  rw [heq]
  exact ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩

end QuotientGroup

end TauCeti
