/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.Topology.Algebra.Group.Quotient

/-!
# Profinite groups: quotients by normal subgroups, and open subgroups

The foundational layer for profinite groups in the unbundled classes: `G` is a group with a
topology making it a topological group, compact and totally disconnected. The separation chain
itself needs no new work — Mathlib derives `T1Space`, `T2Space` and `T3Space` on such a `G` from
`TotallyDisconnectedSpace.t1Space` and `IsTopologicalGroup.regularSpace` — so no statement of
the profinite and pro-`p` development has to carry a `[T2Space G]` hypothesis.

What is genuinely missing is total disconnectedness of a quotient by a *closed* normal
subgroup. We prove it through the clopen-image argument: the quotient map sends the open
normal subgroups of `G` to clopen neighbourhoods of the identity in `G ⧸ N`, their
intersection is the image of `N`, and in a compact Hausdorff group the connected component of
the identity is the intersection of its clopen neighbourhoods. With the compactness,
topological-group and separation instances, `G ⧸ N` is then a profinite group again.

Closedness of `N` is needed only for the total-disconnectedness results: a quotient by a
non-closed subgroup is not even `T1` (take `ℤ̂ ⧸ ℤ` with `ℤ` dense), so
`QuotientGroup.connectedComponent_one` and `QuotientGroup.instTotallyDisconnectedSpace`
carry the hypothesis, while the clopen-image statement is valid for an arbitrary normal subgroup.

## Main results

* `Subgroup.eq_iInf_sup_openNormalSubgroup`: a closed subgroup is the infimum of the
  subgroups `N ⊔ U` with `U` open normal.
* `QuotientGroup.connectedComponent_one`, `QuotientGroup.instTotallyDisconnectedSpace`:
  the quotient of a profinite group by a closed normal subgroup is totally disconnected.
* `Subgroup.iInf_openNormalSubgroup_eq_bot`: the infimum of the open normal subgroups of a
  profinite group is trivial.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 1.1.4 and Theorem 1.1.6.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- A closed subgroup of a profinite group is the infimum of the subgroups `N ⊔ U`, over the
open normal subgroups `U` of `G`: the open normal subgroups are cofinal among the open
subgroups containing `N`. This is the saturation statement behind the clopen-image argument
for quotients, and the form of `ProfiniteGrp.closedSubgroup_eq_sInf_open` that the pro-`p`
development uses. -/
theorem _root_.Subgroup.eq_iInf_sup_openNormalSubgroup (N : Subgroup G)
    (hN : IsClosed (N : Set G)) :
    N = ⨅ U : OpenNormalSubgroup G, N ⊔ U.toSubgroup := by
  refine le_antisymm (le_iInf fun U => le_sup_left) fun x hx => ?_
  by_contra hxN
  obtain ⟨K, hKopen, hKN, hxK⟩ :
      ∃ K : Subgroup G, IsOpen (K : Set G) ∧ N ≤ K ∧ x ∉ K := by
    by_contra! hall
    refine hxN ?_
    -- `closedSubgroup_eq_sInf_open` is stated for a bundled `ClosedSubgroup`; its coercion
    -- to `Subgroup G` is definitionally `N`, but `rw` matches only syntactic patterns, so
    -- record the coercion-free equation first.
    have hNsInf : (N : Subgroup G) = sInf {K : Subgroup G | IsOpen (K : Set G) ∧ N ≤ K} :=
      ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨N, hN⟩
    rw [hNsInf]
    exact Subgroup.mem_sInf.mpr fun K hK => hall K hK.1 hK.2
  obtain ⟨U₀, hU₀⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hKopen (Subgroup.one_mem K)
  exact hxK ((sup_le hKN fun y hy => hU₀ hy) (Subgroup.mem_iInf.mp hx U₀))

/-- In a profinite group, an element that lies in every open normal subgroup is `1`. -/
theorem _root_.Subgroup.eq_one_of_mem_iInf_openNormalSubgroup {x : G}
    (hx : ∀ U : OpenNormalSubgroup G, x ∈ U.toSubgroup) : x = 1 := by
  by_contra hxone
  have hopen : IsOpen ({x}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have hone : (1 : G) ∈ ({x}ᶜ : Set G) := by simp [Ne.symm hxone]
  obtain ⟨U₀, hU₀⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  exact (Set.mem_compl_singleton_iff.mp (hU₀ (hx U₀))) rfl

/-- In a profinite group, the infimum of the open normal subgroups is trivial. -/
@[simp]
theorem _root_.Subgroup.iInf_openNormalSubgroup_eq_bot :
    (⨅ U : OpenNormalSubgroup G, U.toSubgroup) = ⊥ := by
  simpa using (Subgroup.eq_iInf_sup_openNormalSubgroup (⊥ : Subgroup G)
    isClosed_singleton).symm

namespace QuotientGroup

variable {N : Subgroup G} [N.Normal]

/-- In the quotient of a profinite group by a closed normal subgroup, the connected
component of the identity is trivial: it is contained in every clopen image `mk '' U`, and
the intersection of those images is the image of `N`, a single point. -/
theorem connectedComponent_one (hN : IsClosed (N : Set G)) :
    connectedComponent (1 : G ⧸ N) = {1} := by
  have key : ⋂ U : OpenNormalSubgroup G, (QuotientGroup.mk : G → G ⧸ N) '' (U : Set G) =
      (QuotientGroup.mk : G → G ⧸ N) '' (N : Set G) := by
    ext z
    simp only [Set.mem_iInter, Set.mem_image]
    constructor
    · intro h
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
      refine ⟨g, ?_, rfl⟩
      have hN' : g ∈ ⨅ U : OpenNormalSubgroup G, N ⊔ U.toSubgroup := by
        refine Subgroup.mem_iInf.mpr fun U => ?_
        rw [sup_comm]
        have hgU : g ∈ (QuotientGroup.mk : G → G ⧸ N) ⁻¹'
            ((QuotientGroup.mk : G → G ⧸ N) '' (U : Set G)) := by simpa using h U
        rw [QuotientGroup.preimage_image_mk_eq_mul] at hgU
        -- `Subgroup.mul_normal` is stated for the `Set G` coercion of a `Subgroup`, but `U`
        -- coerces through the `OpenNormalSubgroup` `SetLike` instance; the two coercions are
        -- definitionally equal and Mathlib provides no lemma bridging them, so normalize by
        -- `rfl` before the rewrite.
        rw [show ((U : Set G) : Set G) = ((↑U : Subgroup G) : Set G) from rfl] at hgU
        rwa [← Subgroup.mul_normal] at hgU
      rwa [← Subgroup.eq_iInf_sup_openNormalSubgroup N hN] at hN'
    · rintro ⟨g, hg, rfl⟩ U
      exact ⟨1, U.one_mem', QuotientGroup.eq.mpr (by simpa using hg)⟩
  have himg : (QuotientGroup.mk : G → G ⧸ N) '' (N : Set G) = {1} := by
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (QuotientGroup.eq_one_iff g).mpr hg
    · rintro rfl
      exact ⟨1, Subgroup.one_mem N, QuotientGroup.mk_one N⟩
  have hsub : connectedComponent (1 : G ⧸ N) ⊆ {1} := by
    intro y hy
    have hy' : y ∈ ⋂ U : OpenNormalSubgroup G,
        (QuotientGroup.mk : G → G ⧸ N) '' (U : Set G) :=
      Set.mem_iInter.mpr fun U =>
        IsClopen.connectedComponent_subset (isClopen_image_mk U.toOpenSubgroup)
        ⟨1, U.one_mem', QuotientGroup.mk_one N⟩ hy
    rw [key, himg] at hy'
    exact hy'
  exact le_antisymm hsub (Set.singleton_subset_iff.mpr mem_connectedComponent)

/-- The quotient of a profinite group by a closed normal subgroup is totally disconnected.
Together with the compactness, topological-group and separation instances, this says that
`G ⧸ N` is a profinite group again. -/
instance instTotallyDisconnectedSpace [hN : IsClosed (N : Set G)] :
    TotallyDisconnectedSpace (G ⧸ N) :=
  totallyDisconnectedSpace_iff_connectedComponent_one.mpr (connectedComponent_one hN)

end QuotientGroup

end TauCeti
