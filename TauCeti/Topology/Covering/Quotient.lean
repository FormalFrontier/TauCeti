/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient

/-!
# Intermediate quotients of a quotient covering map

Let a group `G` act on a space `E` so that `q : E → X` presents `X` as the quotient `E / G` in
the strong sense of Mathlib's `IsQuotientCoveringMap`: the fibres of `q` are the orbits, and every
point of `E` has a neighbourhood whose `G`-translates are pairwise disjoint. Let `H` be a subgroup
of `G`, and let `qH : E → Y` present `Y` as `E / H` in the same sense. The projection `q` then
factors through `qH`, and the theorem of this file is that the factor

`r : E / H → E / G`

is a covering map. Neither space is assumed connected, and no local connectedness of `X` is
needed: the sheets of `r` over the base set `q '' U` are the images in `Y` of the translates
`g • U`, whose overlaps the disjointness hypothesis controls directly.

The intended reading is that a subgroup of the deck group of a regular covering cuts out an
intermediate covering. That is the shape of the subgroup-to-cover half of the classification of
covering spaces, where `E` is the universal cover of `X` and `G` is its fundamental group; that
application is `TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj`.

## Main results

* `TauCeti.IsQuotientCoveringMap.isCoveringMap_of_comp`: the map from the quotient by a subgroup
  down to the quotient by the whole group is a covering map.

## Implementation notes

The sheets are produced by hand rather than by exhibiting `r` as a quotient covering map for some
group, because in general it is not one. The fibre of `r` over `q e` consists of the classes of
the points `g • e` for `g : G`, two of which agree exactly when `g` differs by an element of `H`;
the normalizer quotient `N_G(H) / H` acts on `E / H` over `X` by deck transformations of `r`, but
on that fibre it acts transitively only when `H` is normal in `G`. (Whether it exhausts the deck
transformations of `r` is a further question, needing connectedness hypotheses that are not
assumed here.)

So the construction goes through Mathlib's `IsOpen.trivializationDiscrete`, which turns a family
of pairwise disjoint sets on which the map is injective into a `Bundle.Trivialization`. The index
type of that family is the set of translate images itself, which makes the family injective and
its pairwise disjointness exactly the statement that two meeting translate images coincide.

## References

The `IsQuotientCoveringMap` interface this file is built on — the predicate itself, its
`disjoint` and `apply_eq_iff_mem_orbit` fields, and `IsQuotientCoveringMap.isOpenQuotientMap` —
is Junyan Xu's, in `Mathlib/Topology/Covering/Quotient.lean`.
-/

public section

namespace TauCeti

open Pointwise Topology

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
  {G : Type*} [Group G] [MulAction G E] {H : Subgroup G}
  {q : E → X} {qH : E → Y} {r : Y → X}

namespace IsQuotientCoveringMap

omit [TopologicalSpace E] [TopologicalSpace Y] in
/-- **When the `G`-translates of `U` are pairwise disjoint, two translates whose images in `Y` meet
have the same image.** So the sets `qH '' (g • U)` are pairwise equal or disjoint. This is a
statement about the fibres of `qH` alone: no topology enters. -/
private theorem image_smul_eq_image_smul_of_inter_nonempty
    (horbit : ∀ {e₁ e₂ : E}, qH e₁ = qH e₂ ↔ e₁ ∈ MulAction.orbit H e₂) {U : Set E}
    (hdisj : ∀ g : G, (g • U ∩ U).Nonempty → g = 1) {g g' : G}
    (hmeet : (qH '' (g • U) ∩ qH '' (g' • U)).Nonempty) :
    qH '' (g • U) = qH '' (g' • U) := by
  -- A point common to the two images is `qH (g • u) = qH (g' • u')` for some `u, u' ∈ U`.
  obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, _, ⟨u', hu', rfl⟩, hww'⟩ := hmeet
  obtain ⟨⟨h, hh⟩, hhu'⟩ := horbit.mp hww'.symm
  -- `H` acts through the coercion to `G` — `MulAction.subgroup_smul_def` — so the orbit witness is
  -- an element of `G` fixing `qH`, and `hhu'` retypes to the ambient action.
  have hhu : h • (g' • u') = g • u := by simpa only [MulAction.subgroup_smul_def] using hhu'
  have hmap : ∀ e : E, qH (h • e) = qH e := fun e =>
    horbit.mpr ⟨⟨h, hh⟩, MulAction.subgroup_smul_def ⟨h, hh⟩ e⟩
  have hgg' : g = h * g' := eq_of_inv_mul_eq_one <| by
    refine hdisj _ ⟨u, Set.mem_smul_set.mpr ⟨u', hu', ?_⟩, hu⟩
    rw [mul_smul, mul_smul, hhu, inv_smul_smul]
  simp [hgg', mul_smul, ← Set.image_smul, Set.image_image, hmap]

/-- The evenly covered neighbourhood of `q e` cut out by a set `U` around `e` whose `G`-translates
are pairwise disjoint. Its sheets are the images in `Y` of the translates `g • U`. -/
private theorem isEvenlyCovered_of_smul_disjoint (hq : IsQuotientCoveringMap q G)
    (hqH : IsQuotientCoveringMap qH H) (hr : r ∘ qH = q) {U : Set E} (hUo : IsOpen U)
    (hdisj : ∀ g : G, (g • U ∩ U).Nonempty → g = 1) {e : E} (heU : e ∈ U) :
    IsEvenlyCovered r (q e) (r ⁻¹' {q e}) := by
  have hrqH : ∀ y : E, r (qH y) = q y := congrFun hr
  have hcsG : ContinuousConstSMul G E := hq.toContinuousConstSMul
  have hrc : Continuous r := by
    rw [hqH.toIsQuotientMap.continuous_iff, hr]
    exact hq.continuous
  have hsheet_open : ∀ g : G, IsOpen (qH '' (g • U)) := fun g =>
    hqH.isOpenQuotientMap.isOpenMap _ (hUo.smul g)
  have hVo : IsOpen (q '' U) := hq.isOpenQuotientMap.isOpenMap _ hUo
  let : TopologicalSpace {S : Set Y // ∃ g : G, S = qH '' (g • U)} := ⊥
  have : DiscreteTopology {S : Set Y // ∃ g : G, S = qH '' (g • U)} := ⟨rfl⟩
  have : Nonempty {S : Set Y // ∃ g : G, S = qH '' (g • U)} :=
    ⟨⟨qH '' ((1 : G) • U), 1, rfl⟩⟩
  have : Nonempty (X → Y) := ⟨fun _ => qH e⟩
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (IsEvenlyCovered.of_trivialization (f := r)
      (t := hVo.trivializationDiscrete
        (Subtype.val : {S : Set Y // ∃ g : G, S = qH '' (g • U)} → Set Y) (q '' U)
        ?_ ?_ ?_ ?_ ?_) ⟨e, heU, rfl⟩)
  · -- Openness inside the base set is detected on any single sheet.
    rintro ⟨S, g, rfl⟩ W hWV
    refine ⟨fun hW => (hW.preimage hrc).inter (hsheet_open g), fun hW => ?_⟩
    have hSopen : IsOpen (q ⁻¹' W ∩ g • U) := by
      have hpull : IsOpen (qH ⁻¹' (r ⁻¹' W ∩ qH '' (g • U))) := hW.preimage hqH.continuous
      have hinter : qH ⁻¹' (r ⁻¹' W ∩ qH '' (g • U)) ∩ g • U = q ⁻¹' W ∩ g • U := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_preimage, hrqH]
        exact and_congr_left fun hw => and_iff_left ⟨w, hw, rfl⟩
      exact hinter ▸ hpull.inter (hUo.smul g)
    rw [← hq.toIsQuotientMap.isOpen_preimage]
    have hcover : q ⁻¹' W = ⋃ k : G, k • (q ⁻¹' W ∩ g • U) := by
      refine Set.Subset.antisymm (fun w hw => ?_) (Set.iUnion_subset fun k w hw => ?_)
      · obtain ⟨u, hu, hqu⟩ := hWV hw
        obtain ⟨m, hm⟩ := hq.apply_eq_iff_mem_orbit.mp hqu.symm
        refine Set.mem_iUnion.mpr ⟨m * g⁻¹, Set.mem_smul_set.mpr ⟨g • u, ⟨?_, ?_⟩, ?_⟩⟩
        · rw [Set.mem_preimage, hq.map_smul, hqu]
          exact hw
        · exact Set.smul_mem_smul_set hu
        · rw [mul_smul, inv_smul_smul]
          exact hm
      · obtain ⟨w', ⟨hw', -⟩, rfl⟩ := Set.mem_smul_set.mp hw
        rw [Set.mem_preimage, hq.map_smul]
        exact hw'
    rw [hcover]
    exact isOpen_iUnion fun k => hSopen.smul k
  · -- The map is injective on each sheet.
    rintro ⟨S, g, rfl⟩ z hz z' hz' hzz'
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hz'
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨u', hu', rfl⟩ := Set.mem_smul_set.mp hw'
    rw [hrqH, hrqH, hq.map_smul, hq.map_smul] at hzz'
    obtain ⟨k, hk⟩ := hq.apply_eq_iff_mem_orbit.mp hzz'
    have hk1 : k • u' = u := hk
    rw [hdisj k ⟨u, Set.mem_smul_set.mpr ⟨u', hu', hk1⟩, hu⟩, one_smul] at hk1
    rw [hk1]
  · -- Each sheet surjects onto the base set.
    rintro ⟨S, g, rfl⟩ v ⟨u, hu, rfl⟩
    exact ⟨qH (g • u), ⟨g • u, Set.smul_mem_smul_set hu, rfl⟩, by rw [hrqH, hq.map_smul]⟩
  · -- Distinct sheets are disjoint.
    rintro ⟨S, g, rfl⟩ ⟨S', g', rfl⟩ hne
    by_contra hcon
    exact hne (Subtype.ext (image_smul_eq_image_smul_of_inter_nonempty
      hqH.apply_eq_iff_mem_orbit hdisj
      (Set.not_disjoint_iff_nonempty_inter.mp hcon)))
  · -- The sheets exhaust the preimage of the base set.
    intro z hz
    obtain ⟨w, rfl⟩ := hqH.surjective z
    rw [Set.mem_preimage, hrqH] at hz
    obtain ⟨u, hu, hqu⟩ := hz
    obtain ⟨k, hk⟩ := hq.apply_eq_iff_mem_orbit.mp hqu.symm
    exact Set.mem_iUnion.mpr
      ⟨⟨qH '' (k • U), k, rfl⟩, ⟨w, Set.mem_smul_set.mpr ⟨u, hu, hk⟩, rfl⟩⟩

/-- **An intermediate quotient of a quotient covering map is a covering map.**

If `q : E → X` presents `X` as the quotient of `E` by a group `G` in the sense of
`IsQuotientCoveringMap`, and `qH : E → Y` presents `Y` as the quotient of `E` by a subgroup `H`
of `G`, then the map `r : Y → X` through which `q` factors is a covering map. -/
theorem isCoveringMap_of_comp (hq : IsQuotientCoveringMap q G)
    (hqH : IsQuotientCoveringMap qH H) (hr : r ∘ qH = q) : IsCoveringMap r := by
  intro x
  obtain ⟨e, rfl⟩ := hq.surjective x
  obtain ⟨U, hU, hdisj⟩ := hq.disjoint e
  refine isEvenlyCovered_of_smul_disjoint hq hqH hr isOpen_interior (fun g hg => hdisj g ?_)
    (mem_interior_iff_mem_nhds.mpr hU)
  rw [← Set.image_smul] at hg
  exact Set.Nonempty.mono
    (Set.inter_subset_inter (Set.image_mono interior_subset) interior_subset) hg

end IsQuotientCoveringMap

end TauCeti
