/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Basic results on fundamental groupoids and fundamental groups

This file records a basic connectedness result for fundamental groupoids and when a map induced
on fundamental groups is trivial: a characterization of trivial range loop by loop, and the basic
consequences of triviality of the *source* fundamental group.

`TauCeti.FundamentalGroup.map_range_eq_bot_iff` was extracted from the proof of
`TauCeti.semilocallySimplyConnectedAt_iff` in
`TauCeti/AlgebraicTopology/SemilocallySimplyConnected/On.lean`, which is adapted from the Mathlib
drafts [#31449](https://github.com/leanprover-community/mathlib4/pull/31449),
[#31576](https://github.com/leanprover-community/mathlib4/pull/31576), and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292) by Kim Morrison, for
Stage 0.1 of the `TauCetiRoadmap/UniversalCovers` roadmap.

## Main declarations

* `FundamentalGroupoid.nonempty_hom`: the fundamental groupoid of a path-connected
  space is connected.
* `TauCeti.FundamentalGroup.map_range_eq_bot_iff`: the induced map has trivial range exactly
  when every loop at the basepoint becomes nullhomotopic in the target.
* `TauCeti.FundamentalGroup.map_range_eq_bot_of_subsingleton`: if the source fundamental group
  is subsingleton, the range of any induced map from it is trivial.
* `TauCeti.FundamentalGroup.map_range_le_of_subsingleton`: if the source fundamental group is
  subsingleton, any induced-map range lies in any target subgroup.
* `TauCeti.FundamentalGroup.map_range_le_of_simplyConnectedSpace`: a simply connected domain has
  induced-map range contained in any target subgroup.
* `TauCeti.FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton`: the same triviality for the
  basepoint-transported induced map `FundamentalGroup.mapOfEq`.
-/

public section

open CategoryTheory

namespace FundamentalGroupoid

/-- In the fundamental groupoid of a path-connected space every object receives a morphism from
every other one, so the groupoid is connected. -/
theorem nonempty_hom {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] (x y : FundamentalGroupoid Y) : Nonempty (x ⟶ y) :=
  ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)⟩

end FundamentalGroupoid

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]

/-- Mapping a loop class represented by a path is represented by mapping that path. -/
theorem FundamentalGroup.map_fromPath {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (base : X)
    (q : Path base base) :
    _root_.FundamentalGroup.map f base (_root_.FundamentalGroup.fromPath ⟦q⟧) =
      _root_.FundamentalGroup.fromPath ⟦q.map f.continuous⟧ := by
  rfl

/-- **The induced map is trivial exactly loop by loop.** The map on fundamental groups induced by
`f` has trivial range if and only if every loop at the basepoint becomes nullhomotopic after
applying `f`. -/
theorem FundamentalGroup.map_range_eq_bot_iff {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    (base : X) :
    (_root_.FundamentalGroup.map f base).range = ⊥ ↔
      ∀ γ : Path base base, (γ.map f.continuous).Homotopic (Path.refl (f base)) := by
  rw [MonoidHom.range_eq_bot_iff]
  constructor
  · intro h γ
    have h_map : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ := by
      rw [← FundamentalGroup.map_fromPath f base γ, h]
      -- the identity of the fundamental groupoid is the class of the constant path
      exact FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (f base))
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp h_map
  · intro h
    ext p
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep (_root_.FundamentalGroup.toPath p)
    have hnull : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ :=
      (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr (h γ)
    rw [FundamentalGroup.map_fromPath f base γ, hnull]
    exact (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (f base))).symm

/-- If the source fundamental group is subsingleton, the range of any induced map from it is
trivial. -/
@[simp]
theorem FundamentalGroup.map_range_eq_bot_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.map f a₀).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.map f a₀).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _

/-- A simply connected domain has trivial induced fundamental-group range. -/
theorem FundamentalGroup.map_range_eq_bot_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) : (_root_.FundamentalGroup.map f a₀).range = ⊥ :=
  FundamentalGroup.map_range_eq_bot_of_subsingleton f

/-- If the source fundamental group is subsingleton, its induced-map range lies in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X))
    (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H := by
  rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
  exact bot_le

/-- If the source fundamental group is subsingleton, the range of the induced map transported to
a prescribed target basepoint is trivial. -/
@[simp]
theorem FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton
    [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) {x : X} (h : f a₀ = x) :
    (_root_.FundamentalGroup.mapOfEq f h).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.mapOfEq f h).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.mapOfEq f h).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _

/-- A simply connected domain has induced fundamental-group range contained in any target
subgroup. -/
theorem FundamentalGroup.map_range_le_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H :=
  FundamentalGroup.map_range_le_of_subsingleton f H

end TauCeti
