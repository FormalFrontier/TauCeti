/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.Topology.Homotopy.Monodromy

/-!
# Unpointed connected covers are classified by conjugacy of recovered subgroups

A pointed connected cover of `(X, x)` recovers a subgroup of `π₁(X, x)`, and two such covers
are isomorphic as pointed covers exactly when those subgroups are equal. After forgetting the chosen
points in the fibres over `x`, equality becomes conjugacy: moving the chosen lift by monodromy
conjugates the recovered subgroup, and every lift is reached by monodromy on a path-connected cover.

This file combines the pointed classification with that basepoint-change calculation. Its main
theorem says that two connected covers are isomorphic over `X`, without prescribing the image of a
chosen lift, exactly when their recovered subgroups are conjugate.

## Main declaration

* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj`: two
  path-connected, locally path-connected covers are isomorphic over the base exactly when their
  recovered subgroups are conjugate in the fundamental group of the base.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8, second bullet: the
correspondence between unpointed connected covers and conjugacy classes of subgroups of the
fundamental group.
-/

public section

namespace TauCeti

open _root_.FundamentalGroup

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {x : X} {e₀ : E} {f₀ : F}

/-- **Unpointed connected covers are classified by conjugacy of recovered subgroups.** Two
path-connected, locally path-connected covers of `X` are isomorphic over `X` exactly when,
after choosing lifts `e₀` and `f₀` of the same basepoint `x`, their recovered subgroups of
`π₁(X, x)` are conjugate.

The direction of conjugation follows the convention in
`IsCoveringMap.range_mapOfEq_monodromy`: moving `f₀` by `γ` replaces its recovered subgroup by
its image under `MulAut.conj γ`. -/
theorem IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (hpe : p e₀ = x) (hqf : q f₀ = x) :
    (∃ h : E ≃ₜ F, q ∘ h = p) ↔
      ∃ γ : FundamentalGroup X x,
        (mapOfEq ⟨p, hp.continuous⟩ hpe).range =
          (mapOfEq ⟨q, hq.continuous⟩ hqf).range.map (MulAut.conj γ).toMonoidHom := by
  constructor
  · rintro ⟨h, hcomp⟩
    have hhx : q (h e₀) = x := (congrFun hcomp e₀).trans hpe
    have hrange :
        (mapOfEq ⟨p, hp.continuous⟩ hpe).range =
          (mapOfEq ⟨q, hq.continuous⟩ hhx).range :=
      (IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq hp hq hpe hhx).mp
        ⟨h, rfl, hcomp⟩
    obtain ⟨γ, hγ⟩ := IsCoveringMap.exists_range_eq_map_conj hq
      (⟨f₀, hqf⟩ : q ⁻¹' {x}) (⟨h e₀, hhx⟩ : q ⁻¹' {x})
    exact ⟨γ, hrange.trans hγ⟩
  · rintro ⟨γ, hγ⟩
    let e₁ : q ⁻¹' {x} := hq.monodromy γ ⟨f₀, hqf⟩
    have hrange :
        (mapOfEq ⟨p, hp.continuous⟩ hpe).range =
          (mapOfEq ⟨q, hq.continuous⟩ e₁.2).range := by
      rw [IsCoveringMap.range_mapOfEq_monodromy]
      exact hγ
    obtain ⟨h, -, hcomp⟩ :=
      IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe e₁.2 hrange
    exact ⟨h, hcomp⟩

end TauCeti
