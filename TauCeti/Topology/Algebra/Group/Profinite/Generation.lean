/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Topological generation of a profinite group

A subset of a topological group *generates it topologically* when the abstract subgroup it
generates is dense, that is when `(Subgroup.closure s).topologicalClosure = ⊤`. This file sets
up that notion for profinite groups.

The pivot is the **generation criterion**: in a profinite group a subgroup is dense exactly
when it joins with every open normal subgroup to the whole group, equivalently when its image
generates every finite quotient. It follows from the saturation statement
`Subgroup.eq_iInf_sup_openNormalSubgroup`, and it is what turns questions about topological
generation into questions about the finite quotients.

On top of the criterion the file introduces the two predicates that the pro-`p` development is
stated against: `TauCeti.IsTopologicallyFinitelyGenerated`, which asks for a finite topological
generating set, and `TauCeti.ConvergesToOne`, which asks of a subset that every open normal
subgroup omit only finitely many of its elements. The name of the latter is justified by
`TauCeti.convergesToOne_iff_tendsto_cofinite`: for a profinite group it says exactly that the
inclusion of the subset tends to `1` along the cofinite filter. It is the side condition that
makes the cardinality of an infinite topological generating set a meaningful invariant, so the
two predicates are developed together.

## Main results

* `Subgroup.topologicalClosure_eq_top_iff_sup_openNormalSubgroup`,
  `Subgroup.topologicalClosure_eq_top_iff_map_mk'`,
  `Subgroup.topologicalClosure_closure_eq_top_iff`: the generation criterion, for a subgroup in
  join form and in finite-quotient form, and for a generating subset.
* `TauCeti.IsTopologicallyFinitelyGenerated`: some finite subset generates a dense subgroup; it
  passes to continuous surjective images, hence to quotients, and is invariant under
  topological isomorphism.
* `TauCeti.isTopologicallyFinitelyGenerated_iff_exists_forall_closure_image`: the
  finite-quotient criterion for topological finite generation.
* `TauCeti.ConvergesToOne`: every open normal subgroup omits only finitely many elements of the
  subset; finite subsets converge to `1`, subsets and continuous images of converging subsets
  converge to `1`, and for a profinite group the predicate is convergence along the cofinite
  filter.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 2; Section 2.6 for topological
  generating sets converging to `1`.
-/

public section

namespace TauCeti

open Topology

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

/-! ### The generation criterion -/

omit [TopologicalSpace G] in
/-- Along the quotient map by a normal subgroup, a subgroup has image everything exactly when
it joins with that subgroup to everything. This passes between the two forms of the generation
criterion below. -/
private theorem map_mk'_eq_top_iff (N : Subgroup G) [N.Normal] (H : Subgroup G) :
    H.map (QuotientGroup.mk' N) = ⊤ ↔ H ⊔ N = ⊤ := by
  rw [← (Subgroup.comap_injective (QuotientGroup.mk'_surjective N)).eq_iff,
    Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk']

section Criterion

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The generation criterion**, join form: a subgroup of a profinite group is dense exactly
when it joins with every open normal subgroup to the whole group. Equivalently, it meets every
coset of every open normal subgroup. -/
theorem _root_.Subgroup.topologicalClosure_eq_top_iff_sup_openNormalSubgroup {H : Subgroup G} :
    H.topologicalClosure = ⊤ ↔ ∀ U : OpenNormalSubgroup G, H ⊔ U.toSubgroup = ⊤ := by
  constructor
  · intro hH U
    have hopen : IsOpen ((H ⊔ U.toSubgroup : Subgroup G) : Set G) :=
      Subgroup.isOpen_of_openSubgroup (U := U.toOpenSubgroup) _ le_sup_right
    have hle := H.topologicalClosure_minimal (le_sup_left (b := U.toSubgroup))
      (Subgroup.isClosed_of_isOpen _ hopen)
    rwa [hH, top_le_iff] at hle
  · intro hH
    refine eq_top_iff.mpr ?_
    rw [Subgroup.eq_iInf_sup_openNormalSubgroup _ H.isClosed_topologicalClosure]
    exact le_iInf fun U ↦ (hH U).ge.trans (sup_le_sup_right H.le_topologicalClosure _)

/-- **The generation criterion**, finite-quotient form: a subgroup of a profinite group is
dense exactly when its image in every finite quotient is everything. -/
theorem _root_.Subgroup.topologicalClosure_eq_top_iff_map_mk' {H : Subgroup G} :
    H.topologicalClosure = ⊤ ↔
      ∀ U : OpenNormalSubgroup G, H.map (QuotientGroup.mk' U.toSubgroup) = ⊤ := by
  simp only [map_mk'_eq_top_iff, Subgroup.topologicalClosure_eq_top_iff_sup_openNormalSubgroup]

/-- **The generation criterion** for a generating subset: `s` generates a profinite group
topologically exactly when its image generates every finite quotient. -/
theorem _root_.Subgroup.topologicalClosure_closure_eq_top_iff {s : Set G} :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      ∀ U : OpenNormalSubgroup G,
        Subgroup.closure ((QuotientGroup.mk' U.toSubgroup) '' s) = ⊤ := by
  simp only [Subgroup.topologicalClosure_eq_top_iff_map_mk', MonoidHom.map_closure]

end Criterion

/-! ### Topological finite generation -/

/-- A topological group is **topologically finitely generated** when some finite subset
generates a dense subgroup. For a profinite group this is the finiteness condition that the
generator rank, the Schreier bound and the Frattini quotient theory are stated against. -/
def IsTopologicallyFinitelyGenerated (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤

section FinitelyGenerated

variable [IsTopologicalGroup G]

/-- An abstractly finitely generated topological group is topologically finitely generated; in
particular a finite group is, for any group topology on it. -/
theorem _root_.Group.FG.isTopologicallyFinitelyGenerated [Group.FG G] :
    IsTopologicallyFinitelyGenerated G := by
  obtain ⟨s, hs⟩ := (Group.FG.out : (⊤ : Subgroup G).FG)
  exact ⟨s, by rw [hs]; exact eq_top_iff.mpr (Subgroup.le_topologicalClosure ⊤)⟩

namespace IsTopologicallyFinitelyGenerated

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous surjective image of a topologically finitely generated group is topologically
finitely generated: the image of a finite generating set is one. -/
theorem of_surjective (hG : IsTopologicallyFinitelyGenerated G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsTopologicallyFinitelyGenerated H := by
  classical
  obtain ⟨s, hs⟩ := hG
  refine ⟨s.image f, ?_⟩
  have h := DenseRange.topologicalClosure_map_subgroup hf hsurj.denseRange hs
  rw [MonoidHom.map_closure] at h
  rwa [Finset.coe_image]

/-- A topological quotient of a topologically finitely generated group is topologically
finitely generated. -/
theorem quotient (hG : IsTopologicallyFinitelyGenerated G) (N : Subgroup G) [N.Normal] :
    IsTopologicallyFinitelyGenerated (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- A topological group isomorphism carries topological finite generation to its target. -/
theorem of_equiv (hG : IsTopologicallyFinitelyGenerated G) (e : G ≃ₜ* H) :
    IsTopologicallyFinitelyGenerated H :=
  hG.of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective

end IsTopologicallyFinitelyGenerated

/-- Topological finite generation is invariant under topological group isomorphism. -/
theorem isTopologicallyFinitelyGenerated_congr {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (e : G ≃ₜ* H) :
    IsTopologicallyFinitelyGenerated G ↔ IsTopologicallyFinitelyGenerated H :=
  ⟨fun hG ↦ hG.of_equiv e, fun hH ↦ hH.of_equiv e.symm⟩

/-- A profinite group is topologically finitely generated exactly when a single finite subset
generates all of its finite quotients at once. -/
theorem isTopologicallyFinitelyGenerated_iff_exists_forall_closure_image [CompactSpace G]
    [TotallyDisconnectedSpace G] :
    IsTopologicallyFinitelyGenerated G ↔ ∃ s : Finset G, ∀ U : OpenNormalSubgroup G,
      Subgroup.closure ((QuotientGroup.mk' U.toSubgroup) '' (s : Set G)) = ⊤ := by
  simp only [IsTopologicallyFinitelyGenerated, Subgroup.topologicalClosure_closure_eq_top_iff]

end FinitelyGenerated

/-! ### Subsets converging to the identity -/

/-- A subset of a topological group **converges to `1`** when every open normal subgroup omits
only finitely many of its elements. For a profinite group this is convergence to `1` along the
cofinite filter, by `TauCeti.convergesToOne_iff_tendsto_cofinite`; it is the side condition
under which the cardinality of a topological generating set is a meaningful invariant. -/
def ConvergesToOne {G : Type u} [Group G] [TopologicalSpace G] (s : Set G) : Prop :=
  ∀ U : OpenNormalSubgroup G, {x ∈ s | x ∉ U.toSubgroup}.Finite

variable {s t : Set G}

/-- A finite subset converges to `1`. -/
theorem _root_.Set.Finite.convergesToOne (hs : s.Finite) : ConvergesToOne s :=
  fun _ ↦ hs.subset fun _ hx ↦ hx.1

namespace ConvergesToOne

/-- A subset of a subset converging to `1` converges to `1`. -/
theorem mono (hs : ConvergesToOne s) (hts : t ⊆ s) : ConvergesToOne t :=
  fun U ↦ (hs U).subset fun _ hx ↦ ⟨hts hx.1, hx.2⟩

/-- A continuous homomorphic image of a subset converging to `1` converges to `1`. -/
theorem image {H : Type v} [Group H] [TopologicalSpace H] (hs : ConvergesToOne s) (f : G →* H)
    (hf : Continuous f) : ConvergesToOne (f '' s) := by
  intro U
  refine ((hs ⟨U.toOpenSubgroup.comap f hf, U.isNormal'.comap f⟩).image f).subset ?_
  rintro y ⟨⟨x, hxs, rfl⟩, hxU⟩
  -- membership in the pullback of `U` unfolds to membership of the image in `U`, which is
  -- what `hxU` says; `OpenSubgroup.mem_comap` is the same statement
  exact ⟨x, ⟨hxs, hxU⟩, rfl⟩

end ConvergesToOne

section Profinite

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- In a profinite group the open normal subgroups are a neighbourhood basis of `1`, so a
subset converges to `1` exactly when every neighbourhood of `1` omits only finitely many of its
elements. -/
theorem convergesToOne_iff_forall_mem_nhds :
    ConvergesToOne s ↔ ∀ V ∈ 𝓝 (1 : G), {x ∈ s | x ∉ V}.Finite := by
  refine ⟨fun hs V hV ↦ ?_, fun h U ↦ h _ (U.toOpenSubgroup.isOpen.mem_nhds U.one_mem')⟩
  obtain ⟨W, hWV, hWopen, hW1⟩ := mem_nhds_iff.mp hV
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen hW1
  -- `hU` is stated for the `Set G` coercion of `U`, which is the membership `hxU` provides
  exact (hs U).subset fun x hx ↦ ⟨hx.1, fun hxU ↦ hx.2 (hWV (hU hxU))⟩

/-- Converging to `1` is convergence to `1` along the cofinite filter: this is what the name of
`TauCeti.ConvergesToOne` refers to. -/
theorem convergesToOne_iff_tendsto_cofinite :
    ConvergesToOne s ↔ Filter.Tendsto ((↑) : s → G) Filter.cofinite (𝓝 1) := by
  rw [convergesToOne_iff_forall_mem_nhds, Filter.tendsto_def]
  refine forall₂_congr fun V _ ↦ ?_
  have hsep : {x ∈ s | x ∉ V} = ((↑) : s → G) '' (((↑) : s → G) ⁻¹' Vᶜ) := by
    rw [Subtype.image_preimage_coe]
    ext x
    simp
  rw [hsep, Set.finite_image_iff Subtype.val_injective.injOn, Filter.mem_cofinite,
    Set.preimage_compl]

end Profinite

/-- A finite topological generating set converges to `1`, so a topologically finitely generated
group has a topological generating set converging to `1`. -/
theorem IsTopologicallyFinitelyGenerated.exists_convergesToOne [IsTopologicalGroup G]
    (hG : IsTopologicallyFinitelyGenerated G) :
    ∃ s : Set G, ConvergesToOne s ∧ (Subgroup.closure s).topologicalClosure = ⊤ := by
  obtain ⟨s, hs⟩ := hG
  exact ⟨s, s.finite_toSet.convergesToOne, hs⟩

end TauCeti
