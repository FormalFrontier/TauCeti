/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP

/-!
# The maximal pro-`p` quotient of a profinite group

The **pro-`p` kernel** `TauCeti.proPKernel p G` of a topological group `G` is the intersection
of the open normal subgroups whose quotient is a `p`-group, and the **maximal pro-`p`
quotient** `TauCeti.maximalProPQuotient p G` is `G ⧸ proPKernel p G`, written `G(p)` in the
literature. This file constructs both and proves the theorems that pin them down.

The pro-`p` kernel is defined for an arbitrary topological group, and is normal there. It is
closed as soon as `G` is a topological group, and functorial for arbitrary continuous
homomorphisms; compactness enters only through the key finiteness step
`TauCeti.exists_isPGroup_quotient_le`: the open normal subgroups with `p`-group quotient are
downward directed, so if their intersection lies in an open subgroup `W` then, by Cantor's
intersection theorem for a directed family of closed sets, one of them already lies in `W`.
That step is what makes `G(p)` pro-`p` at all — being a quotient by an intersection of
subgroups with `p`-group quotient does not by itself say anything about its own finite
quotients — and it also gives the comparison `proPKernel p G = ⊥ ↔ IsProP p G`.

Following `TopologicalAbelianization` in Mathlib, the maximal pro-`p` quotient is an `abbrev`
for the quotient group, so that its group, topological and profinite instances — including
`TauCeti.QuotientGroup.instTotallyDisconnectedSpace`, which applies because the pro-`p` kernel
is closed — are found by instance search rather than restated.

## Main definitions

* `TauCeti.proPKernel`: the intersection of the open normal subgroups with `p`-group quotient.
* `TauCeti.maximalProPQuotient`: the quotient of `G` by its pro-`p` kernel.
* `TauCeti.maximalProPQuotient.mk`: the canonical continuous projection `G → G(p)`.
* `TauCeti.maximalProPQuotient.lift`: the factorization of a continuous homomorphism to a
  pro-`p` profinite group through `G(p)`.
* `TauCeti.maximalProPQuotient.map`: functoriality of `G(p)` in `G`.
* `TauCeti.maximalProPQuotient.continuousMulEquivOfIsProP`: a pro-`p` profinite group is its
  own maximal pro-`p` quotient.

## Main results

* `TauCeti.exists_isPGroup_quotient_le`: an open normal subgroup containing the pro-`p` kernel
  contains one with `p`-group quotient.
* `TauCeti.isProP_maximalProPQuotient`: the maximal pro-`p` quotient of a profinite group is
  pro-`p`.
* `TauCeti.proPKernel_eq_bot_iff`: a profinite group is pro-`p` exactly when its pro-`p`
  kernel is trivial.
* `TauCeti.maximalProPQuotient.lift_coe` and `TauCeti.maximalProPQuotient.hom_ext`: the
  universal property of `G(p)`.
* `TauCeti.maximalProPQuotient.lift_comp_map` and `TauCeti.maximalProPQuotient.comp_lift`: the
  factorization is natural in the source and in the target.
* `TauCeti.proPKernel_maximalProPQuotient`: the construction is idempotent.

## References

This is the Layer 3 milestone "The maximal pro-`p` quotient" of the human-authored roadmap
`TauCetiRoadmap/ProfiniteProPGroups/README.md`, which supplies the blueprint followed here: it
freezes the names `proPKernel` and `maximalProPQuotient`, defines the kernel as the intersection
of the open normal subgroups with `p`-group quotient, asks for it to be closed, normal,
characteristic for continuous automorphisms and preserved by continuous homomorphisms, prescribes
the compactness argument carried out in `TauCeti.exists_isPGroup_quotient_le` — that an open
normal subgroup containing the kernel already contains a member of the defining family — and
asks for the quotient map, the universal property, the idempotence and the functoriality to be
stated once, here.

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2 for pro-`p` groups. The pro-`p`
  kernel and the maximal pro-`p` quotient are the case of finite `p`-groups of the maximal
  pro-`C` quotient of a profinite group treated there.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ}

section Defs

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The **pro-`p` kernel** of a topological group `G`: the intersection of the open normal
subgroups of `G` whose quotient is a `p`-group. It is the kernel of the projection onto the
maximal pro-`p` quotient `TauCeti.maximalProPQuotient`. -/
def proPKernel (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup

/-- Membership in the pro-`p` kernel: `x` lies in it exactly when it lies in every open normal
subgroup with `p`-group quotient. -/
@[simp]
theorem mem_proPKernel {x : G} :
    x ∈ proPKernel p G ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) → x ∈ U.toSubgroup := by
  simp [proPKernel, Subgroup.mem_iInf, Subtype.forall]

/-- The pro-`p` kernel is contained in every open normal subgroup with `p`-group quotient. -/
theorem proPKernel_le {U : OpenNormalSubgroup G} (hU : IsPGroup p (G ⧸ U.toSubgroup)) :
    proPKernel p G ≤ U.toSubgroup :=
  fun _ hx ↦ mem_proPKernel.mp hx U hU

/-- The pro-`p` kernel is normal, being an intersection of normal subgroups. -/
instance instNormalProPKernel : (proPKernel p G).Normal :=
  Subgroup.normal_iInf_normal fun U ↦ U.1.isNormal'

/-- The pro-`p` kernel as a set is the intersection of the open normal subgroups with `p`-group
quotient. -/
theorem coe_proPKernel :
    (proPKernel p G : Set G) =
      ⋂ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)},
        (U.1.toSubgroup : Set G) :=
  Subgroup.coe_iInf

/-- The pro-`p` kernel is closed, being an intersection of open — hence closed — subgroups. -/
instance instIsClosedProPKernel [IsTopologicalGroup G] :
    IsClosed ((proPKernel p G : Subgroup G) : Set G) := by
  rw [coe_proPKernel]
  exact isClosed_iInter fun U ↦ U.1.toOpenSubgroup.isClosed

end Defs

section Compact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- An open normal subgroup of a compact group containing the pro-`p` kernel already contains
an open normal subgroup with `p`-group quotient. -/
theorem exists_isPGroup_quotient_le {W : OpenNormalSubgroup G}
    (hW : proPKernel p G ≤ W.toSubgroup) :
    ∃ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) ∧ U.toSubgroup ≤ W.toSubgroup := by
  -- The family is nonempty, witnessed by `⊤`, whose quotient is trivial.
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  have hne : Nonempty {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)} :=
    ⟨⟨{ toOpenSubgroup := ⟨⊤, isOpen_univ⟩
        isNormal' := inferInstance }, IsPGroup.of_subsingleton p (G ⧸ (⊤ : Subgroup G))⟩⟩
  -- It is downward directed, because `G ⧸ (U ⊓ V)` embeds in `(G ⧸ U) × (G ⧸ V)`.
  have hdir : Directed (· ⊇ ·)
      fun U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)} ↦
        (U.1.toSubgroup : Set G) := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩
    exact ⟨⟨U ⊓ V, hU.quotient_inf hV⟩, Set.inter_subset_left, Set.inter_subset_right⟩
  -- Its members are closed and its intersection is the pro-`p` kernel, so Cantor's
  -- intersection theorem places one of them inside the open set `W`.
  have hsub : (⋂ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)},
      (U.1.toSubgroup : Set G)) ⊆ (W.toOpenSubgroup : Set G) := by
    rw [← coe_proPKernel]
    exact hW
  obtain ⟨U, hU⟩ := exists_subset_nhds_of_compactSpace hdir
    (fun U ↦ U.1.toOpenSubgroup.isClosed) (W.toOpenSubgroup.isOpen.mem_nhdsSet.mpr hsub)
  exact ⟨U.1, U.2, hU⟩

/-- An open normal subgroup of a compact group containing the pro-`p` kernel has `p`-group
quotient. -/
theorem isPGroup_quotient_of_proPKernel_le {W : OpenNormalSubgroup G}
    (hW : proPKernel p G ≤ W.toSubgroup) : IsPGroup p (G ⧸ W.toSubgroup) := by
  obtain ⟨U, hU, hUW⟩ := exists_isPGroup_quotient_le hW
  refine hU.of_surjective
    (QuotientGroup.map U.toSubgroup W.toSubgroup (MonoidHom.id G) hUW) fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, QuotientGroup.map_mk _ _ _ _ g⟩

/-- The quotient of a compact group by any normal subgroup containing the pro-`p` kernel is
pro-`p`. -/
theorem isProP_quotient_of_proPKernel_le {N : Subgroup G} [N.Normal]
    (hN : proPKernel p G ≤ N) : IsProP p (G ⧸ N) := by
  rw [isProP_def]
  intro W
  let V : OpenNormalSubgroup G :=
    { toOpenSubgroup := W.toOpenSubgroup.comap (QuotientGroup.mk' N) QuotientGroup.continuous_mk
      isNormal' := W.isNormal'.comap _ }
  let _ : V.toSubgroup.Normal := V.isNormal'
  have hNV : N ≤ V.toSubgroup := fun x hx ↦
    Subgroup.mem_comap.mpr (by
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact W.one_mem')
  refine (isPGroup_quotient_of_proPKernel_le (W := V) (hN.trans hNV)).of_surjective
    (QuotientGroup.map V.toSubgroup W.toSubgroup (QuotientGroup.mk' N) le_rfl) ?_
  exact QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective W.toSubgroup).comp (QuotientGroup.mk'_surjective N)) le_rfl

section TotallyDisconnected

variable [TotallyDisconnectedSpace G]

/-- A profinite group is pro-`p` exactly when its pro-`p` kernel is trivial. -/
theorem proPKernel_eq_bot_iff : proPKernel p G = ⊥ ↔ IsProP p G := by
  refine ⟨fun h ↦ isProP_def.mpr fun U ↦ isPGroup_quotient_of_proPKernel_le (h.trans_le bot_le),
    fun h ↦ le_antisymm ?_ bot_le⟩
  rw [← Subgroup.iInf_openNormalSubgroup_eq_bot (G := G)]
  exact le_iInf fun U ↦ proPKernel_le (isProP_def.mp h U)

end TotallyDisconnected

end Compact

section Functoriality

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The pro-`p` kernel is preserved by continuous homomorphisms: `f (proPKernel p G)` lands in
`proPKernel p H`. No compactness is needed, since the preimage of an open normal subgroup with
`p`-group quotient again has `p`-group quotient. -/
theorem proPKernel_le_comap (f : G →* H) (hf : Continuous f) :
    proPKernel p G ≤ (proPKernel p H).comap f := by
  intro x hx
  rw [Subgroup.mem_comap, mem_proPKernel]
  intro V hV
  exact mem_proPKernel.mp hx
    { toOpenSubgroup := V.toOpenSubgroup.comap f hf
      isNormal' := V.isNormal'.comap f } (hV.quotient_comap f)

/-- The pro-`p` kernel is invariant under a topological group isomorphism; in particular it is
characteristic for the continuous automorphisms of `G`. -/
theorem comap_proPKernel_of_continuousMulEquiv (e : G ≃ₜ* H) :
    (proPKernel p H).comap e.toMulEquiv.toMonoidHom = proPKernel p G := by
  have hcomp : e.symm.toMulEquiv.toMonoidHom.comp e.toMulEquiv.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  refine le_antisymm ?_ (proPKernel_le_comap _ e.continuous)
  calc (proPKernel p H).comap e.toMulEquiv.toMonoidHom
      ≤ ((proPKernel p G).comap e.symm.toMulEquiv.toMonoidHom).comap e.toMulEquiv.toMonoidHom :=
        Subgroup.comap_mono (proPKernel_le_comap _ e.symm.continuous)
    _ = proPKernel p G := by rw [Subgroup.comap_comap, hcomp, Subgroup.comap_id]

end Functoriality

section UniversalProperty

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- A continuous homomorphism from `G` to a pro-`p` profinite group kills the pro-`p` kernel of
`G`. -/
theorem proPKernel_le_ker (hP : IsProP p P) (f : G →* P) (hf : Continuous f) :
    proPKernel p G ≤ f.ker := by
  intro x hx
  have hxP := proPKernel_le_comap f hf hx
  rwa [Subgroup.mem_comap, proPKernel_eq_bot_iff.mpr hP, Subgroup.mem_bot] at hxP

end UniversalProperty

/-- The **maximal pro-`p` quotient** `G(p)` of a topological group `G`: the quotient of `G` by
its pro-`p` kernel. For a profinite `G` it is again profinite, and it is pro-`p` by
`TauCeti.isProP_maximalProPQuotient`. -/
abbrev maximalProPQuotient (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  G ⧸ proPKernel p G

namespace maximalProPQuotient

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The canonical continuous projection of `G` onto its maximal pro-`p` quotient. -/
def mk (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : G →ₜ* maximalProPQuotient p G where
  toMonoidHom := QuotientGroup.mk' (proPKernel p G)
  continuous_toFun := QuotientGroup.continuous_mk

@[simp]
theorem mk_apply (g : G) : mk p G g = (g : maximalProPQuotient p G) := (rfl)

theorem mk_surjective : Function.Surjective (mk p G) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_mk : MonoidHom.ker (mk p G : G →* maximalProPQuotient p G) = proPKernel p G :=
  QuotientGroup.ker_mk' _

/-- Two continuous homomorphisms out of the maximal pro-`p` quotient that agree on the image of
`G` are equal. -/
@[ext]
theorem hom_ext {M : Type*} [Monoid M] [TopologicalSpace M]
    {f g : maximalProPQuotient p G →ₜ* M}
    (h : ∀ x : G, f (x : maximalProPQuotient p G) = g (x : maximalProPQuotient p G)) : f = g :=
  DFunLike.ext _ _ fun x ↦ by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact h y

section Lift

variable {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The universal property of the maximal pro-`p` quotient: a continuous homomorphism from `G`
to a pro-`p` profinite group `P` factors through `G(p)`. The factorization is unique by
`TauCeti.maximalProPQuotient.hom_ext`. -/
def lift (hP : IsProP p P) (f : G →ₜ* P) : maximalProPQuotient p G →ₜ* P where
  toMonoidHom :=
    QuotientGroup.lift _ f.toMonoidHom (proPKernel_le_ker hP f.toMonoidHom (map_continuous f))
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff]
    exact map_continuous f

/-- The lift of `f` through `G(p)` computes on quotient representatives: it agrees with `f` on
the image of `G`. -/
@[simp]
theorem lift_coe (hP : IsProP p P) (f : G →ₜ* P) (g : G) :
    lift hP f (g : maximalProPQuotient p G) = f g := (rfl)

end Lift

/-- Functoriality of the maximal pro-`p` quotient: a continuous homomorphism `G → H` induces a
continuous homomorphism `G(p) → H(p)`. -/
def map (f : G →ₜ* H) : maximalProPQuotient p G →ₜ* maximalProPQuotient p H where
  toMonoidHom :=
    QuotientGroup.map _ _ f.toMonoidHom (proPKernel_le_comap f.toMonoidHom (map_continuous f))
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk (proPKernel p G)).continuous_iff]
    exact QuotientGroup.continuous_mk.comp (map_continuous f)

@[simp]
theorem map_coe (f : G →ₜ* H) (g : G) :
    map (p := p) f (g : maximalProPQuotient p G) = (f g : maximalProPQuotient p H) := (rfl)

/-- Functoriality preserves identities: the identity of `G` induces the identity of `G(p)`. -/
@[simp]
theorem map_id : map (p := p) (ContinuousMonoidHom.id G) = ContinuousMonoidHom.id _ :=
  hom_ext fun x ↦ by simp

/-- Functoriality preserves composition: a composite of continuous homomorphisms induces the
composite of the induced maps. -/
@[simp]
theorem map_comp {K : Type*} [Group K] [TopologicalSpace K] (f : G →ₜ* H) (g : H →ₜ* K) :
    map (p := p) (g.comp f) = (map g).comp (map f) :=
  hom_ext fun x ↦ by simp

section Naturality

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [TotallyDisconnectedSpace Q]

/-- The universal factorization is natural in the source: precomposing the lift of `g : H →ₜ* P`
with the map induced by `f : G →ₜ* H` is the lift of `g ∘ f`. -/
@[simp]
theorem lift_comp_map (hP : IsProP p P) (f : G →ₜ* H) (g : H →ₜ* P) :
    (lift hP g).comp (map f) = lift hP (g.comp f) :=
  hom_ext fun x ↦ by simp

/-- The universal factorization is natural in the target: postcomposing the lift of `f : G →ₜ* P`
with a continuous homomorphism `ψ : P →ₜ* Q` of pro-`p` profinite groups is the lift of
`ψ ∘ f`. -/
theorem comp_lift (hP : IsProP p P) (hQ : IsProP p Q) (ψ : P →ₜ* Q) (f : G →ₜ* P) :
    ψ.comp (lift hP f) = lift hQ (ψ.comp f) :=
  hom_ext fun x ↦ by simp

end Naturality

end maximalProPQuotient

section Profinite

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The maximal pro-`p` quotient of a compact group is pro-`p`. -/
theorem isProP_maximalProPQuotient : IsProP p (maximalProPQuotient p G) :=
  isProP_quotient_of_proPKernel_le le_rfl

variable [TotallyDisconnectedSpace G]

/-- The maximal pro-`p` quotient is idempotent: `G(p)` has trivial pro-`p` kernel. -/
@[simp]
theorem proPKernel_maximalProPQuotient : proPKernel p (maximalProPQuotient p G) = ⊥ :=
  proPKernel_eq_bot_iff.mpr isProP_maximalProPQuotient

namespace maximalProPQuotient

/-- On a pro-`p` profinite group the projection onto the maximal pro-`p` quotient is
bijective. -/
theorem mk_bijective_of_isProP (hG : IsProP p G) : Function.Bijective (mk p G) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff (mk p G : G →* maximalProPQuotient p G)).mp ?_, mk_surjective⟩
  rw [ker_mk]
  exact proPKernel_eq_bot_iff.mpr hG

/-- A pro-`p` profinite group is its own maximal pro-`p` quotient: the projection is a
topological group isomorphism. -/
noncomputable def continuousMulEquivOfIsProP (hG : IsProP p G) :
    G ≃ₜ* maximalProPQuotient p G :=
  ContinuousMulEquiv.mk'
    (Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective _ (mk_bijective_of_isProP hG))
      QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe)
    (map_mul (mk p G))

@[simp]
theorem continuousMulEquivOfIsProP_apply (hG : IsProP p G) (g : G) :
    continuousMulEquivOfIsProP hG g = (g : maximalProPQuotient p G) := (rfl)

end maximalProPQuotient

end Profinite

end TauCeti
