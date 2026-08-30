/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Quotients of topological groups by normal subgroups

Generic facts about the quotient of a topological group by a normal subgroup, phrased for the
unbundled classes `[Group G] [TopologicalSpace G] [IsTopologicalGroup G]`: neither compactness
nor total disconnectedness is needed, so the results apply in particular to profinite groups.

## Main results

* `QuotientGroup.isClopen_image_mk`: the image of an open subgroup of `G` under the
  quotient map `G → G ⧸ N` is clopen.
* `QuotientGroup.comapMk'OpenNormalOrderIso`: open normal subgroups of `G ⧸ N` correspond,
  as lattices, to the open normal subgroups of `G` containing `N`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
  [N.Normal]

/-- The image of an open subgroup of `G` in the quotient by a normal subgroup `N` is
clopen: it is open because the quotient map is open, and closed because it is an open
subgroup of the topological group `G ⧸ N`. -/
theorem isClopen_image_mk (U : OpenSubgroup G) :
    IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) := by
  have hopen : IsOpen ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) :=
    QuotientGroup.isOpenMap_coe _ U.isOpen'
  have heq : (QuotientGroup.mk : G → G ⧸ N) '' (U : Set G) =
      (Subgroup.map (QuotientGroup.mk' N) U.toSubgroup : Set (G ⧸ N)) := by
    -- `(U : Set G)` coerces through the `OpenSubgroup` `SetLike` instance, while
    -- `Subgroup.coe_map` is stated for the `Set G` coercion of the underlying `Subgroup`.
    -- The two coercions are definitionally equal and Mathlib provides no lemma bridging
    -- them, so the normalization below can only go through `rfl`.
    rw [show (U : Set G) = ((↑U : Subgroup G) : Set G) from rfl]
    exact (Subgroup.coe_map (QuotientGroup.mk' N) U.toSubgroup).symm
  rw [heq]
  exact ⟨Subgroup.isClosed_of_isOpen _ hopen, hopen⟩

/-- The correspondence theorem for open normal subgroups: the open normal subgroups of
`G ⧸ N` correspond, as lattices, to the open normal subgroups of `G` containing `N`. -/
def comapMk'OpenNormalOrderIso (N : Subgroup G) [N.Normal] :
    OpenNormalSubgroup (G ⧸ N) ≃o
      { U : OpenNormalSubgroup G // (N : Subgroup G) ≤ U.toSubgroup } where
  toFun U :=
    ⟨{ toOpenSubgroup :=
        ⟨Subgroup.comap (QuotientGroup.mk' N) U.toSubgroup,
          (U.toOpenSubgroup.isOpen').preimage (QuotientGroup.continuous_mk (N := N))⟩ },
      QuotientGroup.le_comap_mk' N U.toSubgroup⟩
  invFun U :=
    { toOpenSubgroup :=
        ⟨Subgroup.map (QuotientGroup.mk' N) U.1.toSubgroup,
          QuotientGroup.isOpenMap_coe _ U.1.toOpenSubgroup.isOpen'⟩
      isNormal' :=
        Subgroup.Normal.map inferInstance (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) }
  left_inv U := OpenNormalSubgroup.toSubgroup_injective
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _)
  right_inv U := Subtype.ext <| OpenNormalSubgroup.toSubgroup_injective <|
    by
      dsimp only
      rw [QuotientGroup.comap_map_mk']
      exact sup_eq_right.mpr U.2
  map_rel_iff' {U V} := by
    constructor
    · intro h
      exact (Subgroup.comap_le_comap_of_surjective (QuotientGroup.mk'_surjective N)).mp h
    · intro h
      exact (Subgroup.comap_le_comap_of_surjective (QuotientGroup.mk'_surjective N)).mpr h

@[simp]
theorem comapMk'OpenNormalOrderIso_apply_toSubgroup (U : OpenNormalSubgroup (G ⧸ N)) :
    (comapMk'OpenNormalOrderIso N U : OpenNormalSubgroup G).toSubgroup =
      Subgroup.comap (QuotientGroup.mk' N) U.toSubgroup := by
  simp [comapMk'OpenNormalOrderIso]

@[simp]
theorem comapMk'OpenNormalOrderIso_symm_apply_toSubgroup
    (U : { V : OpenNormalSubgroup G // (N : Subgroup G) ≤ V.toSubgroup }) :
    ((comapMk'OpenNormalOrderIso N).symm U : OpenNormalSubgroup (G ⧸ N)).toSubgroup =
      Subgroup.map (QuotientGroup.mk' N) U.1.toSubgroup := by
  simp [comapMk'OpenNormalOrderIso]

end QuotientGroup

end TauCeti
