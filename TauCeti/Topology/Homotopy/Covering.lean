/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering maps, lifting criteria, and fundamental-group monodromy

This file records generic covering-space consequences of Mathlib's path-lifting and
monodromy API. For a covering map `p : E → X` whose total space is simply connected,
choosing a lift `e` over `x` identifies `π₁(X, x)` with the fibre over `x` by sending a
loop class to its monodromy translate of `e`.

It also records that a covering map is injective on fundamental groups — the
fundamental-group form of Mathlib's `IsCoveringMap.injective_path_homotopic_map`, which states
the same injectivity for the Hom-sets of the fundamental groupoid.

It also records the lifting criterion in a subgroup form used by the universal-covers
roadmap. Mathlib already proves the fundamental result
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`: a map `f : A → X` lifts through
a covering map `p : E → X`, with prescribed basepoint lift `e₀`, when
`f_* π₁(A, a₀)` is contained in `p_* π₁(E, e₀)`. The classification of covers often inserts
an intermediate subgroup `H ≤ π₁(X, f a₀)`: one first proves `f_* π₁(A, a₀) ≤ H`, and
separately identifies `H` as a subgroup of the image of `p_*`.

## Main declarations

* `TauCeti.IsCoveringMap.map_injective` and `TauCeti.IsCoveringMap.mapOfEq_injective`: a
  covering map is injective on fundamental groups.
* `TauCeti.IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le_subgroup`: lift when
  `f_* π₁(A, a₀) ≤ H ≤ p_* π₁(E, e₀)`.
* `existsUnique_continuousMap_lifts_of_subsingleton_fundamentalGroup`: lift when the source
  fundamental group is subsingleton.
* `TauCeti.IsCoveringMap.fundamentalGroupEquivFiber`: the monodromy bijection
  `FundamentalGroup X x ≃ p ⁻¹' {x}`, `γ ↦ monodromy γ e`.
* `TauCeti.IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply`: the inverse sends a
  fibre point to the loop class whose monodromy translate of the chosen lift is that point.

## References

This builds directly on Junyan Xu's covering-space lifting and monodromy API in
`Mathlib.Topology.Homotopy.Lifting`. The subgroup lifting criterion is a thin wrapper around
Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, and uses the
trivial-source fundamental-group range lemmas from
`TauCeti.AlgebraicTopology.FundamentalGroup.Basic`. -/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}
variable {A : Type*} [TopologicalSpace A]

open _root_.FundamentalGroup

/-- A covering map induces an injective map on fundamental groups. This is the fundamental-group
form of Mathlib's `IsCoveringMap.injective_path_homotopic_map`, which states the same injectivity
for every Hom-set of the fundamental groupoid. -/
theorem IsCoveringMap.map_injective (hp : _root_.IsCoveringMap p) (e : E) :
    Function.Injective (_root_.FundamentalGroup.map ⟨p, hp.continuous⟩ e) := by
  intro δ δ' h
  rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply] at h
  exact hp.injective_path_homotopic_map e e h

/-- A covering map induces an injective map on fundamental groups, in the form transported along
an equality `p e = x` of basepoints.

Combined with `MonoidHom.ofInjective`, this exhibits the image subgroup `p_* π₁(E, e)` as a copy
of `π₁(E, e)`. -/
theorem IsCoveringMap.mapOfEq_injective (hp : _root_.IsCoveringMap p) {e : E} (he : p e = x) :
    Function.Injective (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he) :=
  (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk he)).conj.injective.comp
    (IsCoveringMap.map_injective hp e)

/-- The lifting criterion for a covering map, with the subgroup inclusion factored through an
intermediate subgroup `H ≤ π₁(X, f a₀)`.

This is the form used when a cover is known to have recovered subgroup `H`: to lift `f`, it
suffices to show that `f_* π₁(A, a₀)` lies in `H`, and that `H` is contained in the image of
`p_* π₁(E, e₀)`. -/
theorem IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le_subgroup
    (hp : _root_.IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (H : Subgroup (_root_.FundamentalGroup X (f a₀)))
    (hfH : (_root_.FundamentalGroup.map f a₀).range ≤ H)
    (hHp : H ≤ (_root_.FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he (hfH.trans hHp)

/-- The lifting criterion when the source fundamental group at `a₀` is subsingleton. In this
case the induced subgroup `f_* π₁(A, a₀)` is trivial. -/
theorem IsCoveringMap.existsUnique_continuousMap_lifts_of_subsingleton_fundamentalGroup
    (hp : _root_.IsCoveringMap p) [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E}
    [Subsingleton (_root_.FundamentalGroup A a₀)] (he : p e₀ = f a₀) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he <| by
    rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
    exact bot_le

/-- Choosing a basepoint lift `e` in the fibre over `x` identifies the fundamental group of
the base with that fibre, via `γ ↦ monodromy γ e`. -/
@[expose] noncomputable def IsCoveringMap.fundamentalGroupEquivFiber [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    FundamentalGroup X x ≃ p ⁻¹' {x} :=
  { toFun γ := hp.monodromy γ e
    invFun e' :=
      FundamentalGroup.fromPath <|
        ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (e : E) (e' : E))).map
          ⟨p, hp.continuous⟩).cast
            (Set.mem_singleton_iff.mp e.2).symm (Set.mem_singleton_iff.mp e'.2).symm
    left_inv γ := by
      set Γ : Path.Homotopic.Quotient (e : E) (hp.monodromy γ e : E) :=
        hp.liftPathQuotient γ e
      have hpath :
          Path.Homotopic.Quotient.mk
              (PathConnectedSpace.somePath (e : E) (hp.monodromy γ e : E)) = Γ :=
        Subsingleton.elim _ _
      dsimp only
      rw [hpath, hp.map_liftPathQuotient]
      erw [Path.Homotopic.Quotient.cast_cast]
      exact eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _)
    right_inv e' := by
      obtain ⟨e₀, he₀⟩ := e
      obtain ⟨e₁, he₁⟩ := e'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at he₀ he₁
      set Γ : Path.Homotopic.Quotient e₀ e₁ :=
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₀ e₁)
      dsimp only
      simpa [Γ] using
        hp.monodromy_eq_of_map_eq Γ (by
          dsimp only [Γ]
          erw [Path.Homotopic.Quotient.cast_cast]
          exact (eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _)).symm) }

/-- The general fibre equivalence sends a loop class to the monodromy translate of the chosen
lift, as an equality in the total space `E`. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (IsCoveringMap.fundamentalGroupEquivFiber hp e γ : E) = (hp.monodromy γ e : E) :=
  rfl

/-- The general fibre equivalence sends a loop class to the monodromy translate of the chosen
lift, as an equality in the fibre subtype. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    IsCoveringMap.fundamentalGroupEquivFiber hp e γ = hp.monodromy γ e :=
  rfl

/-- The inverse of the general fibre equivalence is characterized by the loop class whose
monodromy sends the chosen lift to the requested fibre point. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    hp.monodromy ((IsCoveringMap.fundamentalGroupEquivFiber hp e).symm e') e = e' := by
  have h := (IsCoveringMap.fundamentalGroupEquivFiber hp e).apply_symm_apply e'
  rw [IsCoveringMap.fundamentalGroupEquivFiber_apply] at h
  exact h

/-- On underlying points, the inverse of the general fibre equivalence is characterized by
the loop class whose monodromy sends the chosen lift to the requested fibre point. -/
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    (hp.monodromy ((IsCoveringMap.fundamentalGroupEquivFiber hp e).symm e') e : E) = e' := by
  exact congrArg Subtype.val (IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply hp e e')

end TauCeti
