/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Nested intersections of continua

A **continuum** is a nonempty compact connected set. This file proves the standard structural
theorem about them: the intersection of a family of compact connected sets that is *downward
directed* — any two members contain a third — is again compact and connected. Mathlib has the union
counterpart, `IsPreconnected.sUnion_directed`, and Cantor's intersection theorem
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`, but not the preservation of
connectedness under a directed intersection; this file supplies it.

It is written for `TauCeti/Topology/ClusterSet.lean`, where the boundary cluster set of a map is
exhibited as such an intersection and is thereby a continuum — the first step of the Carathéodory
boundary correspondence, layer **L5** of the conformal-mapping roadmap.

Both hypotheses on the family are essential. Without directedness a circle and a secant line are
two continua meeting in two points, a disconnected intersection. Without compactness the theorem
fails even for a *decreasing sequence*: in `ℝ × ℝ` the closed connected sets
`(ℝ ×ˢ {0}) ∪ (ℝ ×ˢ {1}) ∪ (Ici n ×ˢ Icc 0 1)` — two parallel lines bridged by a strip that
recedes to infinity — intersect in the two lines, which are disconnected.

## The argument

Suppose the intersection `C` splits: `C ⊆ u ∪ v` with `u`, `v` open, both meeting `C`, and
`C ∩ u ∩ v = ∅`. Then `C \ v` and `C \ u` are disjoint nonempty compact sets, so in a Hausdorff
space they have disjoint open neighbourhoods `U` and `V`, and `C ⊆ U ∪ V`. Now the compact sets
`t i \ (U ∪ V)` are again directed and their intersection is `C \ (U ∪ V) = ∅`, so by Cantor's
intersection theorem one of them is *already* empty: some member `t i` is covered by `U ∪ V`. That
member meets both `U` and `V` — it contains `C` — so its connectedness forces `U ∩ V` to be
nonempty, a contradiction.

## Main results

* `TauCeti.isPreconnected_iInter_of_directed` — a directed intersection of compact preconnected
  sets is preconnected.
* `TauCeti.isConnected_iInter_of_directed` — the continuum form: a directed intersection of
  continua is a continuum.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* K. Kuratowski, *Topology II*, §47.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {t : ι → Set X}

/-- **A directed intersection of compact preconnected sets is preconnected.** The family `t` is
indexed by a nonempty type and directed downwards: any two members contain a third.

Both hypotheses on the family are needed; see the module docstring for the two counterexamples. -/
theorem isPreconnected_iInter_of_directed [T2Space X] [Nonempty ι] (htd : Directed (· ⊇ ·) t)
    (htc : ∀ i, IsCompact (t i)) (htp : ∀ i, IsPreconnected (t i)) :
    IsPreconnected (⋂ i, t i) := by
  rintro u v hu hv hCuv ⟨a, haC, hau⟩ ⟨b, hbC, hbv⟩
  by_contra hcon
  -- The two halves of the split, in the closed form `C \ v` and `C \ u`.
  have hCcl : IsClosed (⋂ i, t i) := isClosed_iInter fun i => (htc i).isClosed
  have hCco : IsCompact (⋂ i, t i) :=
    (htc (Classical.arbitrary ι)).of_isClosed_subset hCcl (iInter_subset _ _)
  have hmem : ∀ x ∈ ⋂ i, t i, x ∈ u → x ∉ v := fun x hx hxu hxv => hcon ⟨x, hx, hxu, hxv⟩
  have haA : a ∈ (⋂ i, t i) \ v := ⟨haC, hmem a haC hau⟩
  have hbB : b ∈ (⋂ i, t i) \ u := ⟨hbC, fun hbu => hmem b hbC hbu hbv⟩
  have hdisj : Disjoint ((⋂ i, t i) \ v) ((⋂ i, t i) \ u) := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hCuv hx.1 with hxu | hxv
    · exact hx'.2 hxu
    · exact hx.2 hxv
  -- Separate them by disjoint open sets; the intersection is covered by the two of them.
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hCco.diff hv) (hCco.diff hu) hdisj
  have hCUV : (⋂ i, t i) ⊆ U ∪ V := by
    intro x hx
    by_cases hxv : x ∈ v
    · exact Or.inr (hBV ⟨hx, fun hxu => hmem x hx hxu hxv⟩)
    · exact Or.inl (hAU ⟨hx, hxv⟩)
  -- Cantor's intersection theorem: one member of the family is already covered by `U ∪ V`.
  have hcover : ∃ i, t i ⊆ U ∪ V := by
    by_contra hno
    push Not at hno
    have hne : ∀ i, (t i \ (U ∪ V)).Nonempty := fun i => by
      obtain ⟨x, hx, hxUV⟩ := not_subset.mp (hno i)
      exact ⟨x, hx, hxUV⟩
    have hdir : Directed (· ⊇ ·) fun i => t i \ (U ∪ V) := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := htd i j
      exact ⟨k, sdiff_subset_sdiff_left hki, sdiff_subset_sdiff_left hkj⟩
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun i => t i \ (U ∪ V)) hdir hne (fun i => (htc i).diff (hU.union hV))
        fun i => ((htc i).diff (hU.union hV)).isClosed
    have hxC : x ∈ ⋂ i, t i := mem_iInter.mpr fun i => (mem_iInter.mp hx i).1
    exact (mem_iInter.mp hx (Classical.arbitrary ι)).2 (hCUV hxC)
  -- That member is preconnected and meets both `U` and `V`, so they cannot be disjoint.
  obtain ⟨i, hi⟩ := hcover
  obtain ⟨x, -, hxU, hxV⟩ :=
    htp i U V hU hV hi ⟨a, mem_iInter.mp haC i, hAU haA⟩ ⟨b, mem_iInter.mp hbC i, hBV hbB⟩
  exact disjoint_left.mp hUV hxU hxV

/-- **A directed intersection of continua is a continuum.** The nonemptiness of the intersection
is Cantor's intersection theorem, and its connectedness is
`TauCeti.isPreconnected_iInter_of_directed`. -/
theorem isConnected_iInter_of_directed [T2Space X] [Nonempty ι] (htd : Directed (· ⊇ ·) t)
    (htn : ∀ i, (t i).Nonempty) (htc : ∀ i, IsCompact (t i)) (htp : ∀ i, IsPreconnected (t i)) :
    IsConnected (⋂ i, t i) :=
  ⟨IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc
      fun i => (htc i).isClosed,
    isPreconnected_iInter_of_directed htd htc htp⟩

end TauCeti
