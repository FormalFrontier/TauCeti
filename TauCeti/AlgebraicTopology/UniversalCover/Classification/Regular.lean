/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Regular.Monodromy
public import TauCeti.Topology.Homotopy.Monodromy

/-!
# Regular connected covers and normal subgroups

A pointed connected covering recovers the image of the fundamental group of its total space in
the fundamental group of the base. This file proves the regular-cover criterion: over a
path-connected base, the covering is regular exactly when that recovered subgroup is normal.

The proof combines two existing classification results. Normality says that the recovered
subgroup is independent of the chosen point in a fibre, while pointed-cover classification says
that equality of those subgroups is exactly the existence of a deck transformation carrying one
chosen point to the other. The monodromy transport API then promotes transitivity on the chosen
fibre to regularity on every fibre.

## Main declaration

* `TauCeti.IsCoveringMap.isRegular_iff_normal_range`: a connected covering is regular exactly
  when its recovered subgroup of the fundamental group is normal.

## References

This is the regular-cover criterion in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8: a cover attached to `H` is regular (normal/Galois) exactly when `H` is normal. It uses
Mathlib's covering-space lifting criterion, due to Junyan Xu, through Tau Ceti's pointed-cover
classification; no external proof is copied or adapted here.
-/

public section

namespace TauCeti

open _root_.FundamentalGroup

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

/-- **Regular-cover criterion.** Let `p : E → X` be a covering map with path-connected,
locally path-connected total space and path-connected base. For any chosen lift `e` of `x`, the
deck action is regular exactly when the recovered subgroup
`p_* π₁(E, e) ≤ π₁(X, x)` is normal. -/
theorem IsCoveringMap.isRegular_iff_normal_range
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] [PathConnectedSpace X]
    (hp : _root_.IsCoveringMap p) (e : p ⁻¹' {x}) :
    Deck.IsRegular p ↔
      (mapOfEq ⟨p, hp.continuous⟩ e.2).range.Normal := by
  rw [Deck.isRegular_iff_fiber_isPretransitive hp e,
    TauCeti.IsCoveringMap.normal_range_iff hp e]
  constructor
  · intro htrans e'
    letI := htrans
    obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (Deck p) e e'
    have hhome : ∃ h : E ≃ₜ E, h e = e' ∧ p ∘ h = p := by
      refine ⟨φ.1, ?_, ?_⟩
      · simpa only [Deck.fiber_smul_coe] using congrArg Subtype.val hφ
      · funext z
        exact Deck.map_proj φ z
    have hrange :=
      (TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq
        hp hp e.2 e'.2).mp hhome
    simpa only using hrange.symm
  · intro hrange
    refine MulAction.IsPretransitive.mk ?_
    intro e₀ e₁
    have h₀₁ :
        (mapOfEq ⟨p, hp.continuous⟩ e₀.2).range =
          (mapOfEq ⟨p, hp.continuous⟩ e₁.2).range :=
      (hrange e₀).trans (hrange e₁).symm
    obtain ⟨h, he, hcomp⟩ :=
      TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq
        hp hp e₀.2 e₁.2 h₀₁
    let φ : Deck p := ⟨h, fun z ↦ congrFun hcomp z⟩
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    simpa only [Deck.fiber_smul_coe] using he

end TauCeti
