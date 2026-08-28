/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti AI contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Profinite groups: the finite-quotient limit description

Two unbundled workhorses of profinite group theory, phrased for the type-class stack
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`
(with `TotallyDisconnectedSpace G` only where needed) so that consumers outside the
`ProfiniteGrp` category can use them directly.

* The compactness lemma: a family of nonempty closed subsets of a compact space directed by
  reverse inclusion has nonempty total intersection
  (`nonempty_iInter_of_directed_nonempty_isClosed`; Ribes and Zalesskii, *Profinite Groups*,
  Proposition 1.1.4).
* The limit description: a family of cosets of the open normal subgroups of a compact totally
  disconnected group, compatible along the canonical quotient maps, is realized by a unique
  element of `G` (`existsUnique_forall_mk_eq`). This is the unbundled counterpart of
  `ProfiniteGrp.toLimit_surjective` and `ProfiniteGrp.toLimit_injective`, which describe the
  same identification for the `ProfiniteGrp` category.
-/

public section

namespace TauCeti

section Compactness

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Compactness lemma for profinite spaces** (Ribes and Zalesskii, *Profinite Groups*,
Proposition 1.1.4). A family of nonempty closed subsets of a compact space, directed by
reverse inclusion, has nonempty total intersection. -/
theorem nonempty_iInter_of_directed_nonempty_isClosed {ι : Type*} [Nonempty ι] {S : ι → Set X}
    (hdir : Directed (· ⊇ ·) S) (hne : ∀ i, (S i).Nonempty) (hcl : ∀ i, IsClosed (S i)) :
    (⋂ i, S i).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hne
    (fun i => (hcl i).isCompact) hcl

end Compactness

section LimitDescription

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Limit description of a profinite group** (unbundled). A family `x` of cosets of the open
normal subgroups of a compact totally disconnected group `G` that is compatible along the
canonical quotient maps is realized by a unique element of `G`: the natural map from `G` to
the inverse limit of the quotients `G ⧸ U` over the open normal subgroups `U` is bijective.
The bundled counterpart for the `ProfiniteGrp` category is
`ProfiniteGrp.toLimit_surjective` together with `ProfiniteGrp.toLimit_injective`. -/
theorem existsUnique_forall_mk_eq (x : ∀ U : OpenNormalSubgroup G, G ⧸ (U : Subgroup G))
    (hcompat : ∀ (U V : OpenNormalSubgroup G) (_hle : (U : Subgroup G) ≤ V) (g : G),
      QuotientGroup.mk' (U : Subgroup G) g = x U → QuotientGroup.mk' (V : Subgroup G) g = x V) :
    ∃! g : G, ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U := by
  have hneIdx : Nonempty (OpenNormalSubgroup G) :=
    ⟨{ toOpenSubgroup := ⟨⊤, isOpen_univ⟩ }⟩
  have hne : ∀ U : OpenNormalSubgroup G,
      ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}).Nonempty := fun U =>
    QuotientGroup.mk'_surjective (U : Subgroup G) (x U)
  have hcl : ∀ U : OpenNormalSubgroup G,
      IsClosed ((QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U}) := fun U =>
    isClosed_singleton.preimage (QuotientGroup.continuous_mk (N := (U : Subgroup G)))
  have hdir : Directed (· ⊇ ·) fun U : OpenNormalSubgroup G =>
      (QuotientGroup.mk' (U : Subgroup G)) ⁻¹' {x U} := by
    rintro U V
    refine ⟨U ⊓ V, fun g hgU => ?_, fun g hgV => ?_⟩
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgU ⊢
      exact hcompat (U ⊓ V) U inf_le_left g hgU
    · rw [Set.mem_preimage, Set.mem_singleton_iff] at hgV ⊢
      exact hcompat (U ⊓ V) V inf_le_right g hgV
  obtain ⟨g, hg⟩ := nonempty_iInter_of_directed_nonempty_isClosed hdir hne hcl
  refine ⟨g, fun U => Set.mem_iInter.mp hg U, fun g' hg' => ?_⟩
  have hgg : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g = x U :=
    fun U => Set.mem_iInter.mp hg U
  have hgg' : ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' (U : Subgroup G) g' = x U :=
    fun U => hg' U
  refine (inv_mul_eq_one.mp ?_).symm
  refine Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U => ?_
  exact QuotientGroup.eq.mp ((hgg U).trans (hgg' U).symm)

end LimitDescription

end TauCeti
