/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.Group.Quotient

import Mathlib.Order.Zorn
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Continuous sections of profinite quotients

Let `G` be a profinite group — compact, totally disconnected, and topological, in the unbundled
classes — and let `H` be a *closed* subgroup. This file proves that the quotient map
`G → G ⧸ H` admits a continuous section normalized at the identity coset, and deduces the same
for the projection `G ⧸ K → G ⧸ H` attached to a pair of subgroups `K ≤ H`.

The proof produces a closed left transversal: a closed set meeting every left coset of `H` exactly
once. Zorn's lemma, applied to the pairs `(K, C)` where `C` is a closed set meeting every left
coset of `H` in exactly one coset of the subgroup `K ≤ H`, yields a minimal such pair; the
refinement step shows a minimal pair has `K = ⊥`, which is exactly the transversal condition. That
step is where the topology enters: an element `h ≠ 1` of
`K` is separated from `1` by an open normal subgroup `N`, and the `N`-cosets inside a `K`-coset
`xK` biject with the cosets of the image of `K` in the finite group `G ⧸ N`, so choosing one
representative per coset there thins `C` down along a *clopen* condition, which preserves
closedness. Passing to a chain also uses compactness: Cantor's intersection theorem shows that the
intersection of a chain of such `C`'s still meets every coset.

## Main results

* `Subgroup.exists_isClosed_isComplement_left`: a closed subgroup of a profinite group has
  a closed left transversal, in Mathlib's sense `Subgroup.IsComplement`.
* `TauCeti.exists_continuous_section`: the normalized continuous section `G ⧸ H → G`.
* `TauCeti.exists_continuous_section_of_le`: the continuous section of `G ⧸ K → G ⧸ H` for `K ≤ H`.
* `TauCeti.exists_continuous_rightCosetFactorization`: the right-coset form, `g = w g * r g` with
  `w g ∈ H` and `r g` depending only on the right coset `H * g`, both continuous.

## Implementation notes

The nearby false statement is that `G ⧸ H` is a projective object, so that *every* continuous
surjection onto it splits: profinite spaces are projective only when they are extremally
disconnected, and the section below genuinely uses the group structure of the fibres. Nothing here
is needed when `H` is *open*: then `G ⧸ H` is discrete and `Quotient.out` is already continuous.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 2.2.2.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `IsCosetSelection H K C` says that the closed set `C` meets every left coset of `H` in exactly
one left coset of the subgroup `K ≤ H`. For `K = H` the set `C = Set.univ` qualifies, and for
`K = ⊥` the condition says exactly that `C` is a left transversal of `H`; the proof of
`Subgroup.exists_isClosed_isComplement_left` walks from the first to the second. -/
private structure IsCosetSelection (H K : Subgroup G) (C : Set G) : Prop where
  /-- `C` is closed. -/
  isClosed : IsClosed C
  /-- The selected cosets are cosets of a subgroup of `H`. -/
  le : K ≤ H
  /-- `C` is a union of left cosets of `K`. -/
  mul_mem : ∀ x ∈ C, ∀ k ∈ K, x * k ∈ C
  /-- `C` meets every left coset of `H`. -/
  exists_mem : ∀ g : G, ∃ x ∈ C, x⁻¹ * g ∈ H
  /-- Two elements of `C` in the same left coset of `H` lie in the same left coset of `K`. -/
  inv_mul_mem : ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y ∈ H → x⁻¹ * y ∈ K

omit [IsTopologicalGroup G] in
/-- The whole group is a selection of `H`-cosets at the level `K = H`: the starting point of the
Zorn argument. -/
private theorem isCosetSelection_univ (H : Subgroup G) : IsCosetSelection H H Set.univ where
  isClosed := isClosed_univ
  le := le_rfl
  mul_mem _ _ _ _ := Set.mem_univ _
  exists_mem g := ⟨g, Set.mem_univ _, by simp⟩
  inv_mul_mem _ _ _ _ hxy := hxy

/-- Selections are stable under intersections along a chain: this is the step of the Zorn argument
that needs compactness, through Cantor's intersection theorem for the traces on a coset. -/
private theorem isCosetSelection_sInter [CompactSpace G] {H : Subgroup G}
    (hH : IsClosed (H : Set G))
    {c : Set (Subgroup G × Set G)} (hne : c.Nonempty)
    (hc : ∀ p ∈ c, IsCosetSelection H p.1 p.2) (hchain : IsChain (· ≤ ·) c) :
    IsCosetSelection H (sInf (Prod.fst '' c)) (⋂₀ (Prod.snd '' c)) where
  isClosed := isClosed_sInter (by rintro _ ⟨p, hp, rfl⟩; exact (hc p hp).isClosed)
  le := by
    obtain ⟨p, hp⟩ := hne
    exact (sInf_le (Set.mem_image_of_mem _ hp)).trans (hc p hp).le
  mul_mem x hx k hk := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hc p hp).mul_mem x (hx _ (Set.mem_image_of_mem _ hp)) k
      (Subgroup.mem_sInf.mp hk _ (Set.mem_image_of_mem _ hp))
  exists_mem g := by
    set F : Subgroup G × Set G → Set G := fun p => p.2 ∩ {x | x⁻¹ * g ∈ H}
    have hFclosed : ∀ t ∈ F '' c, IsClosed t := by
      rintro _ ⟨p, hp, rfl⟩
      exact (hc p hp).isClosed.inter
        (hH.preimage (continuous_id.inv.mul continuous_const))
    have : Nonempty (F '' c) := (hne.image F).to_subtype
    have hdir : DirectedOn (· ⊇ ·) (F '' c) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      rcases eq_or_ne p q with rfl | hpq
      · exact ⟨F p, ⟨p, hp, rfl⟩, subset_rfl, subset_rfl⟩
      · rcases hchain hp hq hpq with hle | hle
        · exact ⟨F p, ⟨p, hp, rfl⟩, subset_rfl, Set.inter_subset_inter_left _ hle.2⟩
        · exact ⟨F q, ⟨q, hq, rfl⟩, Set.inter_subset_inter_left _ hle.2, subset_rfl⟩
    have hFne : ∀ t ∈ F '' c, t.Nonempty := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨y, hyC, hyH⟩ := (hc p hp).exists_mem g
      exact ⟨y, hyC, hyH⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed hdir hFne
      (fun t ht => (hFclosed t ht).isCompact) hFclosed
    obtain ⟨p, hp⟩ := hne
    refine ⟨x, ?_, (hx _ (Set.mem_image_of_mem _ hp)).2⟩
    rintro _ ⟨q, hq, rfl⟩
    exact (hx _ (Set.mem_image_of_mem _ hq)).1
  inv_mul_mem x hx y hy hxy := Subgroup.mem_sInf.mpr <| by
    rintro _ ⟨p, hp, rfl⟩
    exact (hc p hp).inv_mul_mem x (hx _ (Set.mem_image_of_mem _ hp)) y
      (hy _ (Set.mem_image_of_mem _ hp)) hxy

/-- **The refinement step.** A selection whose level `K` is nontrivial is not minimal: separating
`h ∈ K`, `h ≠ 1` from the identity by an open normal subgroup `N` and keeping, inside each coset
of `K`, the elements lying in one chosen coset of `N` produces a selection at the strictly smaller
level `K ⊓ N`. The chosen coset is picked in the group `G ⧸ N`, so the extra condition cutting `C`
down is the preimage of a set in a discrete space, and closedness survives. -/
private theorem IsCosetSelection.exists_lt [CompactSpace G] [TotallyDisconnectedSpace G]
    {H K : Subgroup G} {C : Set G} (hsel : IsCosetSelection H K C) {h : G} (hhK : h ∈ K)
    (hh1 : h ≠ 1) :
    ∃ K' : Subgroup G, ∃ C' : Set G, IsCosetSelection H K' C' ∧ K' < K ∧ C' ⊆ C := by
  have h1mem : (1 : G) ∈ ({h}ᶜ : Set G) := by simpa using hh1.symm
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := h)) h1mem
  set N : Subgroup G := U.toSubgroup
  have hhN : h ∉ N := fun hmem => hU hmem rfl
  have : N.Normal := U.isNormal'
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology U.isOpen'
  set φ : G →* G ⧸ N := QuotientGroup.mk' N
  set Kbar : Subgroup (G ⧸ N) := K.map φ
  obtain ⟨ρ, hρmem, hρconst⟩ : ∃ ρ : (G ⧸ N) → (G ⧸ N), (∀ t, t⁻¹ * ρ t ∈ Kbar) ∧
      ∀ t u, t⁻¹ * u ∈ Kbar → ρ t = ρ u := by
    refine ⟨fun t => (QuotientGroup.mk t : (G ⧸ N) ⧸ Kbar).out, fun t => ?_, fun t u htu => ?_⟩
    · exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    · exact congrArg Quotient.out (QuotientGroup.eq.mpr htu)
  have hρidem : ∀ t, ρ (ρ t) = ρ t := fun t => hρconst _ _ (by
    simpa using Kbar.inv_mem (hρmem t))
  have hφcont : Continuous φ := QuotientGroup.continuous_mk
  refine ⟨K ⊓ N, {x ∈ C | φ x = ρ (φ x)}, ⟨?_, ?_, ?_, ?_, ?_⟩,
    lt_of_le_of_ne inf_le_left fun heq => hhN (inf_eq_left.mp heq hhK), fun x hx => hx.1⟩
  · exact hsel.isClosed.inter ((isClosed_discrete {t : G ⧸ N | t = ρ t}).preimage hφcont)
  · exact inf_le_left.trans hsel.le
  · rintro x ⟨hxC, hxφ⟩ k hk
    have hkN : φ k = 1 := (QuotientGroup.eq_one_iff k).mpr (Subgroup.mem_inf.mp hk).2
    exact ⟨hsel.mul_mem x hxC k (Subgroup.mem_inf.mp hk).1,
      by rw [map_mul, hkN, mul_one]; exact hxφ⟩
  · intro g
    obtain ⟨x, hxC, hxH⟩ := hsel.exists_mem g
    obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp (hρmem (φ x))
    have hφxk : φ (x * k) = ρ (φ x) := by rw [map_mul, hk, mul_inv_cancel_left]
    refine ⟨x * k, ⟨hsel.mul_mem x hxC k hkK, by rw [hφxk, hρidem]⟩, ?_⟩
    have hrw : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    exact hrw ▸ H.mul_mem (H.inv_mem (hsel.le hkK)) hxH
  · rintro x ⟨hxC, hxφ⟩ y ⟨hyC, hyφ⟩ hxy
    have hK : x⁻¹ * y ∈ K := hsel.inv_mul_mem x hxC y hyC hxy
    have hbar : (φ x)⁻¹ * φ y ∈ Kbar := by
      rw [← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem φ hK
    have hxy' : φ x = φ y := by rw [hxφ, hyφ, hρconst _ _ hbar]
    have hone : φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy', inv_mul_cancel]
    exact Subgroup.mem_inf.mpr ⟨hK, (QuotientGroup.eq_one_iff _).mp hone⟩

/-- **A closed subgroup of a profinite group has a closed left transversal.** The set `C` produced
here meets every left coset of `H` in exactly one point and is closed, hence compact; that is what
makes the induced bijection `C ≃ G ⧸ H` a homeomorphism in
`TauCeti.exists_continuous_section`. -/
theorem _root_.Subgroup.exists_isClosed_isComplement_left
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ C : Set G, IsClosed C ∧ Subgroup.IsComplement C (H : Set G) := by
  obtain ⟨m, hm, hmin⟩ : ∃ m : Subgroup G × Set G, IsCosetSelection H m.1 m.2 ∧
      ∀ z : Subgroup G × Set G, IsCosetSelection H z.1 z.2 → z ≤ m → m ≤ z := by
    refine zorn_le₀ (α := (Subgroup G × Set G)ᵒᵈ) {p | IsCosetSelection H p.1 p.2} ?_
    intro c hcs hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨(H, Set.univ), isCosetSelection_univ H, by simp⟩
    · exact ⟨(sInf (Prod.fst '' c), ⋂₀ (Prod.snd '' c)),
        isCosetSelection_sInter hH hne (fun p hp => hcs hp) hchain.symm,
        fun z hz => ⟨sInf_le (Set.mem_image_of_mem _ hz),
          Set.sInter_subset_of_mem (Set.mem_image_of_mem _ hz)⟩⟩
  have hbot : m.1 = ⊥ := by
    by_contra hne
    obtain ⟨⟨h, hhK⟩, hh1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hh1 : h ≠ 1 := fun hcon => hh1 (Subtype.ext hcon)
    obtain ⟨K', C', hsel', hlt, hsub⟩ := hm.exists_lt hhK hh1
    exact hlt.ne (le_antisymm hlt.le (hmin (K', C') hsel' ⟨hlt.le, hsub⟩).1)
  refine ⟨m.2, hm.isClosed, Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_⟩
  obtain ⟨x, hxC, hxH⟩ := hm.exists_mem g
  refine ⟨⟨x, hxC⟩, hxH, ?_⟩
  rintro ⟨y, hyC⟩ hy
  have hyH : y⁻¹ * g ∈ H := hy
  have hxyH : x⁻¹ * y ∈ H := by
    have hrw : x⁻¹ * y = x⁻¹ * g * (y⁻¹ * g)⁻¹ := by group
    exact hrw ▸ H.mul_mem hxH (H.inv_mem hyH)
  have : x⁻¹ * y = 1 := by
    have := hm.inv_mul_mem x hxC y hyC hxyH
    rwa [hbot, Subgroup.mem_bot] at this
  exact Subtype.ext (inv_mul_eq_one.mp this).symm

/-- **Continuous sections of profinite quotients** (Ribes-Zalesskii, Proposition 2.2.2). For a
closed subgroup `H` of a profinite group `G` the quotient map `G → G ⧸ H` has a continuous section
sending the identity coset to `1`. This is the statement that the transgression of a five-term
exact sequence, the exactness of coinduction and the inverse in Shapiro's lemma all lift through;
for an *open* subgroup the finite transversal `Quotient.out` already suffices, and this statement
is not needed. -/
theorem exists_continuous_section [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G, Continuous s ∧ (∀ x : G ⧸ H, (QuotientGroup.mk (s x) : G ⧸ H) = x) ∧
      s (QuotientGroup.mk 1) = 1 := by
  obtain ⟨C, hCclosed, hC⟩ := Subgroup.exists_isClosed_isComplement_left H hH
  have : IsClosed (H : Set G) := hH
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCclosed.isCompact
  have hcont : Continuous fun x : C => (QuotientGroup.mk (x : G) : G ⧸ H) :=
    QuotientGroup.continuous_mk.comp continuous_subtype_val
  let e : C ≃ₜ G ⧸ H :=
    Continuous.homeoOfEquivCompactToT2 (f := hC.leftQuotientEquiv.symm) hcont
  set s₀ : G ⧸ H → G := fun q => ((e.symm q : C) : G)
  have hs₀sec : ∀ q, (QuotientGroup.mk (s₀ q) : G ⧸ H) = q :=
    hC.quotientGroupMk_leftQuotientEquiv
  have hmem : s₀ (QuotientGroup.mk 1) ∈ H := by
    have := hs₀sec (QuotientGroup.mk 1)
    rw [QuotientGroup.eq, mul_one] at this
    simpa using H.inv_mem this
  refine ⟨fun q => s₀ q * (s₀ (QuotientGroup.mk 1))⁻¹,
    (continuous_subtype_val.comp e.symm.continuous).mul continuous_const, fun q => ?_, by simp⟩
  calc (QuotientGroup.mk (s₀ q * (s₀ (QuotientGroup.mk 1))⁻¹) : G ⧸ H)
      = QuotientGroup.mk (s₀ q) := (QuotientGroup.eq.mpr (by simpa using H.inv_mem hmem)).symm
    _ = q := hs₀sec q

/-- **The continuous section of a projection between quotients of a profinite group.** For subgroups
`K ≤ H` of a profinite group with `H` closed, the projection `G ⧸ K → G ⧸ H` has a continuous
section normalized at the identity coset. -/
theorem exists_continuous_section_of_le [CompactSpace G] [TotallyDisconnectedSpace G]
    {K H : Subgroup G} (hKH : K ≤ H) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G ⧸ K, Continuous s ∧
      (∀ x : G ⧸ H, Subgroup.quotientMapOfLE hKH (s x) = x) ∧
      s (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
  obtain ⟨t, hcont, hsec, h1⟩ := exists_continuous_section H hH
  exact ⟨fun x => QuotientGroup.mk (t x), QuotientGroup.continuous_mk.comp hcont,
    fun x => by rw [Subgroup.quotientMapOfLE_apply_mk]; exact hsec x, by simp [h1]⟩

/-- **The right-coset form of the continuous section.** For a closed subgroup `H` of a profinite
group `G`, every `g : G` factors as `g = w g * r g` with `w g ∈ H`, where `r g` is a representative
of the *right* coset `H * g` depending only on that coset and `w` is the resulting `H`-valued
cocycle; both are continuous.

Mathlib's quotient `G ⧸ H` is the space of *left* cosets, so `TauCeti.exists_continuous_section`
produces a continuous choice of representatives of `g H`. Inverting exchanges the two sides:
`r g = (s ⟦g⁻¹⟧)⁻¹` lies in `H * g` and depends only on `H * g`. This is the shape the coinduced
module of Layer 7 consumes, since its defining equivariance `f (h * g) = h • f g` is along right
cosets. -/
theorem exists_continuous_rightCosetFactorization [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ (w : G → H) (r : G → G), Continuous w ∧ Continuous r ∧
      (∀ g : G, (w g : G) * r g = g) ∧
      (∀ (h : H) (g : G), w ((h : G) * g) = h * w g) ∧
      (∀ (h : H) (g : G), r ((h : G) * g) = r g) := by
  obtain ⟨s, hs_cont, hs_sec, -⟩ := exists_continuous_section H hH
  have hcoset : ∀ (h : H) (g : G),
      (QuotientGroup.mk (((h : G) * g)⁻¹) : G ⧸ H) = QuotientGroup.mk g⁻¹ := by
    intro h g
    rw [QuotientGroup.eq]
    simp [mul_assoc, h.2]
  have hmem : ∀ g : G, g * s (QuotientGroup.mk g⁻¹) ∈ H := by
    intro g
    have h := hs_sec (QuotientGroup.mk g⁻¹)
    rw [QuotientGroup.eq] at h
    simpa using H.inv_mem h
  refine ⟨fun g => ⟨g * s (QuotientGroup.mk g⁻¹), hmem g⟩,
    fun g => (s (QuotientGroup.mk g⁻¹))⁻¹, ?_, ?_, fun g => by simp, fun h g => ?_, fun h g => ?_⟩
  · exact continuous_induced_rng.2 (continuous_id.mul
      (hs_cont.comp (QuotientGroup.continuous_mk.comp continuous_inv)))
  · exact (hs_cont.comp (QuotientGroup.continuous_mk.comp continuous_inv)).inv
  · exact Subtype.ext (by simp only [hcoset, mul_assoc, Subgroup.coe_mul])
  · simp only [hcoset]

end TauCeti
