/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.Topology.Algebra.Group.Profinite.ProP

/-!
# Sylow subgroups of a profinite group

A `p`-Sylow subgroup of a profinite group `G` is a closed pro-`p` subgroup whose image in
every continuous finite quotient of `G` has index prime to `p`. This file introduces that
predicate, `IsProPSylow`, and proves that every profinite group has one.

## Main results

* `isProP_iff_forall_isPGroup_map_mk'`: a subgroup of a profinite group is pro-`p` exactly
  when its image in every finite quotient is a `p`-group.
* `IsProPSylow`: the `p`-Sylow predicate.
* `isProPSylow_iff_isPGroup_and_not_dvd_index`, `isProPSylow_iff_exists_sylow`: on a discrete
  group the predicate is the finite one, and on a finite discrete group it picks out exactly
  Mathlib's `Sylow` subgroups.
* `IsProP.isProPSylow_top`: in a pro-`p` group the whole group is `p`-Sylow.
* `exists_isProPSylow`: every profinite group has a `p`-Sylow subgroup.

The supernatural reformulation of the index condition, `¬ p ∣ profiniteIndex P G`, needs the
supernatural index and is not proved here.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

/-! ### Pro-`p` subgroups through the finite quotients -/

/-- The comparison map `K ⧸ N → K ⧸ M` attached to `N ≤ M` is surjective. -/
private theorem quotientMapId_surjective {K : Type*} [Group K] (N M : Subgroup K) [N.Normal]
    [M.Normal] (h : N ≤ Subgroup.comap (MonoidHom.id K) M) :
    Function.Surjective (QuotientGroup.map N M (MonoidHom.id K) h) :=
  QuotientGroup.map_surjective_of_surjective N M (MonoidHom.id K)
    (fun y => by
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective M y
      exact ⟨x, hx⟩) h

omit [TopologicalSpace G] in
/-- The image of `H` in `G ⧸ U` is `H ⧸ (U ∩ H)`, so being a `p`-group is the same condition
for the two. -/
private theorem isPGroup_quotient_subgroupOf_iff (H U : Subgroup G) [U.Normal] :
    IsPGroup p (H ⧸ U.subgroupOf H) ↔ IsPGroup p (H.map (QuotientGroup.mk' U)) := by
  let f : H →* G ⧸ U := (QuotientGroup.mk' U).comp H.subtype
  have hker : f.ker = U.subgroupOf H := by
    ext x
    simp [f, Subgroup.mem_subgroupOf]
  have hrange : f.range = H.map (QuotientGroup.mk' U) := by
    simp [f, MonoidHom.range_comp]
  rw [← hrange]
  exact ⟨fun hq => (hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hker.symm)).of_equiv
      (QuotientGroup.quotientKerEquivRange f),
    fun hm => (hm.of_equiv (QuotientGroup.quotientKerEquivRange f).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hker)⟩

/-- The image of a pro-`p` subgroup in a finite quotient of the ambient group is a
`p`-group. -/
theorem IsProP.isPGroup_map_mk' {H : Subgroup G} (hH : IsProP p H)
    (U : OpenNormalSubgroup G) :
    IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  refine (isPGroup_quotient_subgroupOf_iff H U.toSubgroup).mp ?_
  exact isProP_def.mp hH
    { toOpenSubgroup := ⟨U.toSubgroup.subgroupOf H,
        Subgroup.subgroupOf_isOpen H U.toSubgroup U.toOpenSubgroup.isOpen⟩
      isNormal' := Subgroup.normal_subgroupOf }

/-! ### The `p`-Sylow predicate -/

/-- A subgroup `P` of a profinite group `G` is a **`p`-Sylow subgroup** when it is closed, is
pro-`p` in the subspace topology, and its image in every continuous finite quotient of `G` has
index prime to `p`. -/
structure IsProPSylow (p : ℕ) (P : Subgroup G) : Prop where
  /-- A `p`-Sylow subgroup of a profinite group is closed. -/
  isClosed : IsClosed (P : Set G)
  /-- A `p`-Sylow subgroup is pro-`p` for the subspace topology. -/
  isProP : IsProP p P
  /-- The image of a `p`-Sylow subgroup in each finite quotient has index prime to `p`. -/
  not_dvd_index_map_mk' :
    ∀ U : OpenNormalSubgroup G, ¬ p ∣ (P.map (QuotientGroup.mk' U.toSubgroup)).index

section Discrete

variable [DiscreteTopology G]

/-- On a discrete group the `p`-Sylow condition is the usual one: a `p`-subgroup of index
prime to `p`. -/
theorem isProPSylow_iff_isPGroup_and_not_dvd_index {P : Subgroup G} :
    IsProPSylow p P ↔ IsPGroup p P ∧ ¬ p ∣ P.index := by
  constructor
  · refine fun hP => ⟨isProP_iff_isPGroup.mp hP.isProP, ?_⟩
    have h := hP.not_dvd_index_map_mk'
      { toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩, isNormal' := inferInstance }
    rwa [Subgroup.index_map, QuotientGroup.ker_mk', sup_bot_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.index_top,
      mul_one] at h
  · refine fun hP => ⟨isClosed_discrete _, hP.1.isProP, fun U h => hP.2 ?_⟩
    exact h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))

/-- On a finite discrete group, `IsProPSylow` picks out exactly the Sylow `p`-subgroups in
Mathlib's sense. -/
theorem isProPSylow_iff_exists_sylow [Finite G] [Fact p.Prime] {P : Subgroup G} :
    IsProPSylow p P ↔ ∃ S : Sylow p G, (S : Subgroup G) = P := by
  rw [isProPSylow_iff_isPGroup_and_not_dvd_index]
  exact ⟨fun h => ⟨h.1.toSylow h.2, rfl⟩, fun ⟨S, hS⟩ => hS ▸ ⟨S.isPGroup', S.not_dvd_index⟩⟩

end Discrete

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group whose image in every finite quotient of the ambient group
is a `p`-group is pro-`p`. The open normal subgroups of `G` form a neighbourhood basis of `1`,
so every open normal subgroup of `H` contains one of the subgroups `U ∩ H`. -/
theorem isProP_of_forall_isPGroup_map_mk' {H : Subgroup G}
    (h : ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup))) :
    IsProP p H := by
  refine isProP_def.mpr fun W => ?_
  obtain ⟨V, hVopen, hVW⟩ : ∃ V : Set G, IsOpen V ∧ Subtype.val ⁻¹' V = (W : Set H) :=
    isOpen_induced_iff.mp W.toOpenSubgroup.isOpen
  have hV1 : (1 : G) ∈ V := by
    have h1 : (1 : H) ∈ Subtype.val ⁻¹' V := by rw [hVW]; exact W.one_mem'
    exact h1
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen hV1
  have hle : U.toSubgroup.subgroupOf H ≤ W.toSubgroup := fun x hx => by
    have hxV : x ∈ Subtype.val ⁻¹' V := hU (Subgroup.mem_subgroupOf.mp hx)
    rw [hVW] at hxV
    exact hxV
  have hp : IsPGroup p (H ⧸ U.toSubgroup.subgroupOf H) :=
    (isPGroup_quotient_subgroupOf_iff H U.toSubgroup).mpr (h U)
  exact hp.of_surjective
    (QuotientGroup.map _ W.toSubgroup (MonoidHom.id H) (by simpa using hle))
    (quotientMapId_surjective _ W.toSubgroup (by simpa using hle))

/-- A subgroup of a profinite group is pro-`p` exactly when its image in every finite quotient
of the ambient group is a `p`-group. -/
theorem isProP_iff_forall_isPGroup_map_mk' (H : Subgroup G) :
    IsProP p H ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) :=
  ⟨fun hH => hH.isPGroup_map_mk', isProP_of_forall_isPGroup_map_mk'⟩

/-- In a pro-`p` group the whole group is a `p`-Sylow subgroup. -/
theorem IsProP.isProPSylow_top [Fact p.Prime] (hG : IsProP p G) :
    IsProPSylow p (⊤ : Subgroup G) where
  isClosed := by simp
  isProP := isProP_of_forall_isPGroup_map_mk' fun U => by
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact (isProP_def.mp hG U).of_equiv Subgroup.topEquiv.symm
  not_dvd_index_map_mk' U := by
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), Subgroup.index_top]
    exact Nat.Prime.not_dvd_one Fact.out

/-! ### Existence -/

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The preimage in `G` of a subgroup of a finite quotient `G ⧸ U` is closed, being an open
subgroup of `G`. -/
private theorem isClosed_comap_mk' (U : OpenNormalSubgroup G)
    (K : Subgroup (G ⧸ U.toSubgroup)) :
    IsClosed ((K.comap (QuotientGroup.mk' U.toSubgroup) : Subgroup G) : Set G) := by
  refine Subgroup.isClosed_of_isOpen _ ?_
  rw [Subgroup.coe_comap]
  exact (isOpen_discrete _).preimage QuotientGroup.continuous_mk

variable (p G) in
/-- The inverse system, over the open normal subgroups of `G`, of the sets of Sylow
`p`-subgroups of the finite quotients of `G`. The transition maps are `Sylow.mapSurjective`
along the comparison maps `G ⧸ U → G ⧸ V`. -/
private def sylowDiagram [Fact p.Prime] : OpenNormalSubgroup G ⥤ Type u where
  obj U := Sylow p (G ⧸ U.toSubgroup)
  map {U V} f := TypeCat.ofHom (Sylow.mapSurjective (p := p)
    (quotientMapId_surjective U.toSubgroup V.toSubgroup (leOfHom f)))
  map_id U := by
    ext S : 3
    exact Sylow.ext (by simp)
  map_comp {U V W} f g := by
    ext S : 3
    refine Sylow.ext ?_
    simp only [TypeCat.Fun.toFun_apply, TypeCat.ofHom_apply, types_comp_apply,
      Sylow.coe_mapSurjective, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup y
    simp

variable [Fact p.Prime]

variable (p G) in
omit [TotallyDisconnectedSpace G] in
/-- A compatible choice of Sylow `p`-subgroups of the finite quotients of `G`. Compatibility is
recorded as monotonicity of the associated family of open subgroups of `G`: if `U ≤ V`, the
preimage of the chosen Sylow subgroup of `G ⧸ U` is contained in that of `G ⧸ V`. -/
private theorem exists_monotone_comap_sylow :
    ∃ S : ∀ U : OpenNormalSubgroup G, Sylow p (G ⧸ U.toSubgroup),
      Monotone fun U => Subgroup.comap (QuotientGroup.mk' U.toSubgroup)
        (S U : Subgroup (G ⧸ U.toSubgroup)) := by
  have hfin : ∀ U : OpenNormalSubgroup G, Finite ((sylowDiagram p G).obj U) := fun U =>
    show Finite (Sylow p (G ⧸ U.toSubgroup)) from
      Finite.of_injective (fun S => (S : Subgroup (G ⧸ U.toSubgroup))) fun _ _ h => Sylow.ext h
  have hne : ∀ U : OpenNormalSubgroup G, Nonempty ((sylowDiagram p G).obj U) := fun U =>
    show Nonempty (Sylow p (G ⧸ U.toSubgroup)) from inferInstance
  obtain ⟨S₀, hS₀⟩ := nonempty_sections_of_finite_cofiltered_system (sylowDiagram p G)
  let S : ∀ U : OpenNormalSubgroup G, Sylow p (G ⧸ U.toSubgroup) := S₀
  refine ⟨S, fun U V h x hx => ?_⟩
  have hSUV : (S U : Subgroup (G ⧸ U.toSubgroup)).map
      (QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) h)
      = (S V : Subgroup (G ⧸ V.toSubgroup)) :=
    congrArg Sylow.toSubgroup (hS₀ (homOfLE h) : Sylow.mapSurjective (p := p)
      (quotientMapId_surjective U.toSubgroup V.toSubgroup h) (S U) = S V)
  rw [Subgroup.mem_comap] at hx ⊢
  rw [← hSUV]
  exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk x, hx,
    QuotientGroup.map_mk' U.toSubgroup V.toSubgroup (MonoidHom.id G) h x⟩

variable {S : ∀ U : OpenNormalSubgroup G, Sylow p (G ⧸ U.toSubgroup)}

omit [TotallyDisconnectedSpace G] in
/-- If the family of preimages is monotone, then the preimage of a Sylow subgroup at a smaller
level already maps onto the chosen Sylow subgroup at a larger one: its image is a Sylow
subgroup contained in the chosen one, hence equal to it. -/
private theorem map_comap_sylow_eq
    (hS : Monotone fun U => Subgroup.comap (QuotientGroup.mk' U.toSubgroup)
      (S U : Subgroup (G ⧸ U.toSubgroup)))
    {W U : OpenNormalSubgroup G} (h : W ≤ U) :
    (Subgroup.comap (QuotientGroup.mk' W.toSubgroup)
        (S W : Subgroup (G ⧸ W.toSubgroup))).map (QuotientGroup.mk' U.toSubgroup)
      = (S U : Subgroup (G ⧸ U.toSubgroup)) := by
  have hcomp : (QuotientGroup.mk' U.toSubgroup : G →* G ⧸ U.toSubgroup)
      = (QuotientGroup.map W.toSubgroup U.toSubgroup (MonoidHom.id G) h).comp
        (QuotientGroup.mk' W.toSubgroup) := by
    ext x
    exact (QuotientGroup.map_mk' W.toSubgroup U.toSubgroup (MonoidHom.id G) h x).symm
  have hself : (Subgroup.comap (QuotientGroup.mk' W.toSubgroup)
      (S W : Subgroup (G ⧸ W.toSubgroup))).map (QuotientGroup.mk' W.toSubgroup)
      = (S W : Subgroup (G ⧸ W.toSubgroup)) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hmap : (Subgroup.comap (QuotientGroup.mk' W.toSubgroup)
      (S W : Subgroup (G ⧸ W.toSubgroup))).map (QuotientGroup.mk' U.toSubgroup)
      = ((Sylow.mapSurjective (p := p)
        (quotientMapId_surjective W.toSubgroup U.toSubgroup h) (S W) :
          Sylow p (G ⧸ U.toSubgroup)) : Subgroup (G ⧸ U.toSubgroup)) := by
    rw [Sylow.coe_mapSurjective, hcomp, ← Subgroup.map_map, hself]
  rw [hmap]
  exact ((Sylow.mapSurjective (p := p)
    (quotientMapId_surjective W.toSubgroup U.toSubgroup h) (S W)).is_maximal'
      (S U).isPGroup' (hmap ▸ Subgroup.map_le_iff_le_comap.mpr (hS h))).symm

omit [TotallyDisconnectedSpace G] in
/-- The infimum of the preimages of a monotone family of Sylow subgroups maps onto each member
of the family. This is where compactness of `G` enters: the sets of elements lying over a fixed
point of `S U` and inside a given member of the family form a directed family of nonempty
closed subsets. -/
private theorem iInf_comap_sylow_map_eq
    (hS : Monotone fun U => Subgroup.comap (QuotientGroup.mk' U.toSubgroup)
      (S U : Subgroup (G ⧸ U.toSubgroup)))
    (U : OpenNormalSubgroup G) :
    (⨅ V, Subgroup.comap (QuotientGroup.mk' V.toSubgroup)
        (S V : Subgroup (G ⧸ V.toSubgroup))).map (QuotientGroup.mk' U.toSubgroup)
      = (S U : Subgroup (G ⧸ U.toSubgroup)) := by
  set Q : OpenNormalSubgroup G → Subgroup G := fun V =>
    Subgroup.comap (QuotientGroup.mk' V.toSubgroup) (S V : Subgroup (G ⧸ V.toSubgroup))
  have hQclosed : ∀ V, IsClosed (Q V : Set G) := fun V => isClosed_comap_mk' V _
  refine le_antisymm ((Subgroup.map_mono (iInf_le Q U)).trans_eq
    (map_comap_sylow_eq hS le_rfl)) fun y hy => ?_
  have : Nonempty (OpenNormalSubgroup G) := ⟨U⟩
  set T : OpenNormalSubgroup G → Set G := fun V =>
    (Q V : Set G) ∩ (QuotientGroup.mk' U.toSubgroup) ⁻¹' {y} with hT
  have hTclosed : ∀ V, IsClosed (T V) := fun V =>
    (hQclosed V).inter (isClosed_singleton.preimage QuotientGroup.continuous_mk)
  have hTne : ∀ V, (T V).Nonempty := fun V => by
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp
      ((map_comap_sylow_eq hS (inf_le_right : V ⊓ U ≤ U)) ▸ hy)
    exact ⟨x, hS (inf_le_left : V ⊓ U ≤ V) hx, hxy⟩
  have hTdir : Directed (· ⊇ ·) T := fun V V' =>
    ⟨V ⊓ V', fun x hx => ⟨hS (inf_le_left : V ⊓ V' ≤ V) hx.1, hx.2⟩,
      fun x hx => ⟨hS (inf_le_right : V ⊓ V' ≤ V') hx.1, hx.2⟩⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hTdir hTne (fun V => (hTclosed V).isCompact) hTclosed
  rw [Set.mem_iInter] at hx
  exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_iInf.mpr fun V => (hx V).1, (hx U).2⟩

variable (p G) in
/-- **Existence of `p`-Sylow subgroups.** Every profinite group has a `p`-Sylow subgroup: a
compatible family of Sylow subgroups of the finite quotients exists by Kőnig's lemma, and the
infimum of their preimages is the required closed pro-`p` subgroup. -/
theorem exists_isProPSylow : ∃ P : Subgroup G, IsProPSylow p P := by
  obtain ⟨S, hS⟩ := exists_monotone_comap_sylow p G
  refine ⟨⨅ V, Subgroup.comap (QuotientGroup.mk' V.toSubgroup)
    (S V : Subgroup (G ⧸ V.toSubgroup)), ?_, ?_, ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isClosed_iInter fun V => isClosed_comap_mk' V _
  · exact isProP_of_forall_isPGroup_map_mk' fun U =>
      (iInf_comap_sylow_map_eq hS U) ▸ (S U).isPGroup'
  · exact fun U => (iInf_comap_sylow_map_eq hS U) ▸ (S U).not_dvd_index

end Profinite

end TauCeti
