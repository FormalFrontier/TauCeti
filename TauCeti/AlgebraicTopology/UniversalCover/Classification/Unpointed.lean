/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.Topology.Homotopy.Monodromy

/-!
# Unpointed connected covers are determined by a conjugacy class of subgroups

Choosing a point in the fibre of a connected covering map over `x` recovers a subgroup of
`FundamentalGroup X x`. The pointed classification theorem says that two covers with chosen
fibre points are isomorphic over `X` precisely when these subgroups are equal. Without chosen
fibre points, equality is replaced by conjugacy: moving a fibre point by monodromy conjugates
the recovered subgroup, and every fibre point is reached by monodromy.

This file combines those two facts. For path-connected, locally path-connected covering spaces
`E` and `F`, it proves that there is a homeomorphism `E ≃ₜ F` over `X` if and only if the
subgroups recovered from any chosen lifts `e₀` and `f₀` are conjugate in `π₁(X, x)`. The
conjugacy convention is written explicitly as

`range(q, f₀) = range(p, e₀).map (MulAut.conj γ).toMonoidHom`.

The statement does not need connectedness, local connectedness, or semilocal simple
connectedness of the base. Those hypotheses are needed to construct a cover from every
subgroup, not to compare two covers which already exist.

## Main declarations

* `TauCeti.IsCoveringMap.exists_range_eq_map_conj_of_homeomorph_comp_eq`: an isomorphism of
  unpointed covers makes their recovered subgroups conjugate.
* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq_map_conj`: conjugate recovered
  subgroups give an isomorphism of unpointed covers.
* `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj`: the
  unpointed connected-cover comparison theorem.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 8, second bullet:
unpointed connected covers correspond to conjugacy classes of subgroups. It proves the
comparison-up-to-isomorphism half of that correspondence; constructing a cover from every
subgroup is the separate existence milestone in item 7.

The proof reuses `TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq` for pointed
covers and `TauCeti.IsCoveringMap.exists_range_eq_map_conj` for change of the chosen lift.
The latter is built on Junyan Xu's monodromy API in
`Mathlib.Topology.Homotopy.Lifting`; no external formalization is copied or adapted here.
-/

public section

namespace TauCeti

open _root_.FundamentalGroup

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {x : X} {e₀ : E} {f₀ : F}

namespace IsCoveringMap

/-- An isomorphism of unpointed connected covers carries the subgroup recovered from the
source basepoint to a conjugate of the subgroup recovered from the target basepoint.

The homeomorphism need not carry `e₀` to `f₀`: its image of `e₀` is another point of the
target fibre, and changing from that point to `f₀` accounts for the conjugation. -/
theorem exists_range_eq_map_conj_of_homeomorph_comp_eq [PathConnectedSpace F]
    (hp : Continuous p) (hq : _root_.IsCoveringMap q)
    (hpe : p e₀ = x) (hqf : q f₀ = x) (h : E ≃ₜ F) (hcomp : q ∘ h = p) :
    ∃ γ : FundamentalGroup X x,
      (mapOfEq ⟨q, hq.continuous⟩ hqf).range =
        (mapOfEq ⟨p, hp⟩ hpe).range.map (MulAut.conj γ).toMonoidHom := by
  have hqh : q (h e₀) = x := (congrFun hcomp e₀).trans hpe
  let f₁ : q ⁻¹' {x} := ⟨h e₀, Set.mem_singleton_iff.mpr hqh⟩
  have hrange :
      (mapOfEq ⟨p, hp⟩ hpe).range =
        (mapOfEq ⟨q, hq.continuous⟩ hqh).range := by
    have hpcomp : (⟨q, hq.continuous⟩ : C(F, X)).comp ⟨h, h.continuous⟩ =
        ⟨p, hp⟩ := by
      ext e
      exact congrFun hcomp e
    apply le_antisymm
    · rintro _ ⟨γ, rfl⟩
      refine ⟨mapOfEq ⟨h, h.continuous⟩ rfl γ, ?_⟩
      rw [TauCeti.FundamentalGroup.mapOfEq_comp]
      exact TauCeti.FundamentalGroup.mapOfEq_congr hpcomp _ _ γ
    · rintro _ ⟨δ, rfl⟩
      obtain ⟨γ, rfl⟩ :=
        (TauCeti.FundamentalGroup.homeomorphMulEquiv h e₀).surjective δ
      refine ⟨γ, ?_⟩
      rw [TauCeti.FundamentalGroup.homeomorphMulEquiv_apply,
        TauCeti.FundamentalGroup.mapOfEq_comp]
      exact (TauCeti.FundamentalGroup.mapOfEq_congr hpcomp _ _ γ).symm
  let f : q ⁻¹' {x} := ⟨f₀, Set.mem_singleton_iff.mpr hqf⟩
  obtain ⟨γ, hγ⟩ := IsCoveringMap.exists_range_eq_map_conj hq f₁ f
  refine ⟨γ, ?_⟩
  simpa only [f₁, f] using hγ.trans (congrArg
    (fun H : Subgroup (FundamentalGroup X x) => H.map (MulAut.conj γ).toMonoidHom)
    hrange.symm)

/-- If two pointed connected covers recover conjugate subgroups, then forgetting the chosen
fibre points makes the covers isomorphic over the base. -/
theorem exists_homeomorph_comp_eq_of_range_eq_map_conj
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (hpe : p e₀ = x) (hqf : q f₀ = x) (γ : FundamentalGroup X x)
    (hrange : (mapOfEq ⟨q, hq.continuous⟩ hqf).range =
      (mapOfEq ⟨p, hp.continuous⟩ hpe).range.map (MulAut.conj γ).toMonoidHom) :
    ∃ h : E ≃ₜ F, q ∘ h = p := by
  let e : p ⁻¹' {x} := ⟨e₀, Set.mem_singleton_iff.mpr hpe⟩
  let e₁ : p ⁻¹' {x} := hp.monodromy γ e
  have hpe₁ : p (e₁ : E) = x := Set.mem_singleton_iff.mp e₁.2
  have hrange₁ :
      (mapOfEq ⟨p, hp.continuous⟩ hpe₁).range =
        (mapOfEq ⟨q, hq.continuous⟩ hqf).range := by
    calc
      (mapOfEq ⟨p, hp.continuous⟩ hpe₁).range =
          (mapOfEq ⟨p, hp.continuous⟩ hpe).range.map
            (MulAut.conj γ).toMonoidHom := by
              simpa only [e, e₁] using IsCoveringMap.range_mapOfEq_monodromy hp e γ
      _ = (mapOfEq ⟨q, hq.continuous⟩ hqf).range := hrange.symm
  obtain ⟨h, -, hcomp⟩ :=
    IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp hq hpe₁ hqf hrange₁
  exact ⟨h, hcomp⟩

/-- **Unpointed connected covers are classified up to isomorphism by the conjugacy class of
the subgroup they recover.** There is a homeomorphism of the total spaces over `X` exactly
when the subgroups recovered from chosen lifts of `x` are conjugate in `π₁(X, x)`.

The chosen lifts occur only in the subgroup invariant; the homeomorphism is not required to
map one chosen lift to the other. -/
theorem exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj
    [PathConnectedSpace E] [LocallyPathConnectedSpace E]
    [PathConnectedSpace F] [LocallyPathConnectedSpace F]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x) :
    (∃ h : E ≃ₜ F, q ∘ h = p) ↔
      ∃ γ : FundamentalGroup X x,
        (mapOfEq ⟨q, hq.continuous⟩ hqf).range =
          (mapOfEq ⟨p, hp.continuous⟩ hpe).range.map (MulAut.conj γ).toMonoidHom := by
  constructor
  · rintro ⟨h, hcomp⟩
    exact IsCoveringMap.exists_range_eq_map_conj_of_homeomorph_comp_eq
      hp.continuous hq hpe hqf h hcomp
  · rintro ⟨γ, hrange⟩
    exact IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq_map_conj hp hq hpe hqf γ hrange

end IsCoveringMap

end TauCeti
