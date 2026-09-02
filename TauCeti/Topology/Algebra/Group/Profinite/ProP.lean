/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.GroupTheory.PGroup

/-!
# Pro-p groups

A topological group is pro-`p` when each of its continuous finite quotients is a `p`-group.
For the unbundled profinite groups used in Tau Ceti, these quotients are represented by the
quotients by open normal subgroups. This file introduces that quotient-form predicate and its
covariant API: abstract `p`-groups are pro-`p`, continuous surjective images of pro-`p` groups
are pro-`p`, and hence so are topological quotients. It also records invariance under
topological group isomorphism and agreement with `IsPGroup` for a discrete topology.

Closedness of a normal subgroup is not needed for the predicate to descend to its quotient.
It is needed only when one wants the quotient of a profinite group to be profinite again; that
separate topological fact is supplied by `QuotientGroup.instTotallyDisconnectedSpace`.

The second half of the file is the contravariant direction, where the group the property is
transported to is no longer a quotient. All of it rests on one criterion,
`isProP_of_forall_exists_normal_le`: a group is pro-`p` as soon as each of its open normal
subgroups contains a normal subgroup — not necessarily open — with `p`-group quotient. In a
profinite group the open normal subgroups form a neighbourhood basis of `1`
(`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`), which is what produces those
witnesses, first for an inducing homomorphism into a profinite pro-`p` group and then for a
product. Subgroups and inverse limits are the two cases of interest: a subgroup carries the
induced topology, and `ProfiniteGrp.limit` is by construction a subgroup of the product of the
objects of the diagram. Together with the covariant half this gives the inverse-limit
description of pro-`p` groups, `isProP_iff_exists_continuousMulEquiv_limit`.

## Main results

* `IsProP`: every quotient by an open normal subgroup is a `p`-group.
* `IsPGroup.isProP`: an abstract `p`-group with any topology is pro-`p`.
* `isProP_iff_isPGroup`: for a discrete topology, pro-`p` agrees with `IsPGroup`.
* `IsProP.of_surjective`: a continuous surjective image of a pro-`p` group is pro-`p`.
* `IsProP.quotient`: a quotient of a pro-`p` group by a normal subgroup is pro-`p`.
* `isProP_congr`: the predicate is invariant under topological group isomorphism.
* `isProP_of_forall_exists_normal_le`: the criterion through a cofinal family of normal
  subgroups with `p`-group quotient.
* `IsProP.of_isInducing`: pro-`p` passes to the source of an inducing homomorphism into a
  profinite pro-`p` group.
* `IsProP.subgroup`: a subgroup of a profinite pro-`p` group is pro-`p`.
* `IsProP.pi`: a product of profinite pro-`p` groups is pro-`p`.
* `IsProP.limit`: an inverse limit of pro-`p` profinite groups is pro-`p`.
* `isProP_iff_exists_continuousMulEquiv_limit`: a profinite group is pro-`p` exactly when it is
  topologically isomorphic to an inverse limit of finite `p`-groups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2 and Proposition 2.2.1.
-/

public section

namespace TauCeti

universe u v w

/-- A topological group is **pro-`p`** when every quotient by an open normal subgroup is a
`p`-group. For a profinite group these are exactly its continuous finite quotients. -/
def IsProP (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup)

variable {p : ℕ}

namespace IsPGroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An abstract `p`-group is pro-`p` for any topology: all of its group quotients are
`p`-groups. -/
theorem _root_.IsPGroup.isProP (hG : IsPGroup p G) : IsProP p G :=
  fun U ↦ hG.to_quotient U.toSubgroup

end IsPGroup

section Discrete

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- On a group with the discrete topology, being pro-`p` is equivalent to being a `p`-group. -/
@[simp]
theorem isProP_iff_isPGroup : IsProP p G ↔ IsPGroup p G := by
  refine ⟨fun hG ↦ ?_, IsPGroup.isProP⟩
  let U : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩
      isNormal' := inferInstance }
  exact (hG U).of_equiv QuotientGroup.quotientBot

end Discrete

namespace IsProP

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- A continuous surjective image of a pro-`p` group is pro-`p`. -/
theorem of_surjective (hG : IsProP p G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsProP p H := by
  intro U
  let V : OpenNormalSubgroup G :=
    { toOpenSubgroup := U.toOpenSubgroup.comap f hf
      isNormal' := U.isNormal'.comap f }
  let _ : V.toSubgroup.Normal := V.isNormal'
  let q : G ⧸ V.toSubgroup →* H ⧸ U.toSubgroup :=
    QuotientGroup.map V.toSubgroup U.toSubgroup f le_rfl
  apply (hG V).of_surjective q
  exact QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup f
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp hsurj) le_rfl

/-- A quotient of a pro-`p` group by a normal subgroup is pro-`p`.

No closedness hypothesis is needed here: closedness controls whether the quotient topology is
Hausdorff and profinite, not whether its open-normal quotients are `p`-groups. -/
theorem quotient (hG : IsProP p G) (N : Subgroup G) [N.Normal] : IsProP p (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- A topological group isomorphism carries the pro-`p` property to its target. -/
theorem of_equiv (hG : IsProP p G) (e : G ≃ₜ* H) : IsProP p H :=
  hG.of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective

end IsProP

/-- Being pro-`p` is invariant under topological group isomorphism. -/
theorem isProP_congr {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃ₜ* H) : IsProP p G ↔ IsProP p H :=
  ⟨fun hG ↦ hG.of_equiv e, fun hH ↦ hH.of_equiv e.symm⟩

/-! ### Stability under subgroups, products and limits -/

/-- A criterion for being pro-`p`: it suffices that every open normal subgroup of `G` contains
*some* normal subgroup with `p`-group quotient. The witnessing subgroups need not be open,
which is what makes the criterion usable. -/
theorem isProP_of_forall_exists_normal_le {G : Type u} [Group G] [TopologicalSpace G]
    (h : ∀ U : OpenNormalSubgroup G, ∃ N : Subgroup G, ∃ _ : N.Normal,
      N ≤ U.toSubgroup ∧ IsPGroup p (G ⧸ N)) :
    IsProP p G := by
  intro U
  obtain ⟨N, _, hNU, hN⟩ := h U
  have hle : N ≤ U.toSubgroup.comap (MonoidHom.id G) := by simpa using hNU
  exact hN.of_surjective (QuotientGroup.map N U.toSubgroup (MonoidHom.id G) hle)
    (QuotientGroup.map_surjective_of_surjective N U.toSubgroup (MonoidHom.id G)
      (QuotientGroup.mk'_surjective U.toSubgroup) hle)

/-- The quotient of a group by the kernel of a homomorphism to a `p`-group is a `p`-group. -/
private theorem isPGroup_quotient_ker {G : Type u} [Group G] {K : Type v} [Group K]
    (hK : IsPGroup p K) (f : G →* K) : IsPGroup p (G ⧸ f.ker) :=
  hK.of_injective (QuotientGroup.kerLift f) (QuotientGroup.kerLift_injective f)

namespace IsProP

/-- Being pro-`p` passes to the source of an *inducing* homomorphism into a profinite pro-`p`
group. Neither injectivity of `f` nor closedness of its image is needed: only that `G` carries
the topology induced from `H`. -/
theorem of_isInducing {G : Type u} [Group G] [TopologicalSpace G] {H : Type v} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hH : IsProP p H) {f : G →* H} (hf : Topology.IsInducing f) : IsProP p G := by
  refine isProP_of_forall_exists_normal_le fun V ↦ ?_
  obtain ⟨t, ht, htV⟩ := hf.isOpen_iff.mp V.toOpenSubgroup.isOpen
  have h1 : (1 : H) ∈ t := by
    have h1V : (1 : G) ∈ f ⁻¹' t := by rw [htV]; exact V.toSubgroup.one_mem
    simpa using h1V
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  refine ⟨((QuotientGroup.mk' U.toSubgroup).comp f).ker, inferInstance, fun x hx ↦ ?_,
    isPGroup_quotient_ker (hH U) _⟩
  have hxt : x ∈ f ⁻¹' t :=
    hU ((QuotientGroup.eq_one_iff (f x)).mp (MonoidHom.mem_ker.mp hx))
  rw [htV] at hxt
  exact hxt

/-- Every subgroup of a profinite pro-`p` group is pro-`p` in the subspace topology. Closedness
of the subgroup is not needed for this; it is what makes the subgroup profinite in its own
right. -/
theorem subgroup {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G) (H : Subgroup G) :
    IsProP p H :=
  hG.of_isInducing (f := H.subtype) Topology.IsInducing.subtypeVal

/-- A product of profinite pro-`p` groups is pro-`p`. Taking the index type finite gives
stability under finite products. -/
theorem pi {ι : Type w} {G : ι → Type u} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, CompactSpace (G i)]
    [∀ i, TotallyDisconnectedSpace (G i)] (h : ∀ i, IsProP p (G i)) :
    IsProP p (∀ i, G i) := by
  refine isProP_of_forall_exists_normal_le fun W ↦ ?_
  obtain ⟨I, t, hIt, hsub⟩ :=
    isOpen_pi_iff.mp W.toOpenSubgroup.isOpen 1 W.toSubgroup.one_mem
  choose U hU using fun i : I ↦
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hIt i i.2).1 (hIt i i.2).2
  refine ⟨(MonoidHom.pi fun i : I ↦
      (QuotientGroup.mk' (U i).toSubgroup).comp (Pi.evalMonoidHom G i)).ker, inferInstance,
    fun x hx ↦ ?_, isPGroup_quotient_ker (IsPGroup.pi fun i : I ↦ h i (U i)) _⟩
  refine hsub fun i hi ↦ hU ⟨i, hi⟩ ((QuotientGroup.eq_one_iff (x i)).mp ?_)
  exact congrFun (MonoidHom.mem_ker.mp hx) ⟨i, hi⟩

open CategoryTheory in
/-- An inverse limit of pro-`p` profinite groups is pro-`p`. -/
theorem limit {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})
    (h : ∀ j, IsProP p (F.obj j)) : IsProP p (ProfiniteGrp.limit F) :=
  (IsProP.pi h).subgroup (ProfiniteGrp.limitConePtAux F)

end IsProP

open CategoryTheory in
/-- A profinite group is pro-`p` exactly when it is topologically isomorphic to an inverse limit
of finite `p`-groups. The forward direction realises `G` as the limit of its own quotients by
open normal subgroups. -/
theorem isProP_iff_exists_continuousMulEquiv_limit {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    IsProP p G ↔ ∃ (J : Type u) (_ : SmallCategory J) (F : J ⥤ FiniteGrp.{u}),
      (∀ j, IsPGroup p (F.obj j)) ∧
        Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp)) := by
  refine ⟨fun hG ↦ ⟨OpenNormalSubgroup (ProfiniteGrp.of G), inferInstance,
    ProfiniteGrp.toFiniteQuotientFunctor (ProfiniteGrp.of G), fun U ↦ hG U,
    ⟨ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor (ProfiniteGrp.of G)⟩⟩, ?_⟩
  rintro ⟨J, _, F, hF, ⟨e⟩⟩
  refine (IsProP.limit _ fun j ↦ ?_).of_equiv e.symm
  exact IsPGroup.isProP (hF j)

end TauCeti
