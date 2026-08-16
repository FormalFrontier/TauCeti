/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Hodge.Structure
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Tate Hodge structures

The Tate structure `ℤ(m)` is the rank-one pure Hodge structure of weight `-2m` and type
`(-m,-m)`. Its complexification is `ℂ`, with the integral lattice embedded by the usual map
`ℤ → ℂ`; its decreasing filtration is the whole line through degree `-m` and zero above it.

This is the first concrete nonzero inhabitant of `TauCeti.Hodge.HodgeStructure`. Besides fixing the
weight and filtration-shift conventions needed by later Tate twists, it verifies directly that the
opposed-filtration definition has the intended rank-one objects.

The convention follows the Hodge structures roadmap and standard Hodge-theory notation; see
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.

## Main declarations

* `TauCeti.Hodge.tate`: the Tate Hodge structure `ℤ(m)` of weight `-2m`.
* `TauCeti.Hodge.tate_F`: its filtration is `⊤` exactly in degrees at most `-m`.
* `TauCeti.Hodge.tate_piece`: its only nonzero Hodge component has bidegree `(-m,-m)`.
* `TauCeti.Hodge.finrank_tate_piece`: its Hodge number there is one and all others are zero.
-/

public section

namespace TauCeti.Hodge

/-- The integral lattice map `ℤ → ℂ` used by the Tate Hodge structure. -/
abbrev tateLatticeMap : ℤ →ₗ[ℤ] ℂ :=
  Algebra.linearMap ℤ ℂ

/-- The usual inclusion `ℤ → ℂ` exhibits `ℂ` as the complexification of the rank-one lattice. -/
theorem isBaseChange_tateLatticeMap : IsBaseChange ℂ tateLatticeMap :=
  IsBaseChange.linearMap ℤ ℂ

/-- The Hodge filtration of `ℤ(m)`: the whole complex line through degree `-m`, and zero above. -/
private def tateFiltration (m p : ℤ) : Submodule ℂ ℂ :=
  if p ≤ -m then ⊤ else ⊥

/-- The Tate filtration is decreasing. -/
private theorem antitone_tateFiltration (m : ℤ) : Antitone (tateFiltration m) := by
  intro p q hpq
  by_cases hq : q ≤ -m
  · have hp : p ≤ -m := hpq.trans hq
    simp [tateFiltration, hp, hq]
  · simp [tateFiltration, hq]

/-- The filtration of `ℤ(m)` is opposed to its conjugate in weight `-2m`. -/
private theorem isCompl_tateFiltration (m p : ℤ) :
    IsCompl (tateFiltration m p)
      ((tateFiltration m (-2 * m + 1 - p)).map
        (latticeConjugation isBaseChange_tateLatticeMap).toEquiv.toLinearMap) := by
  by_cases hp : p ≤ -m
  · have hq : ¬ -2 * m + 1 - p ≤ -m := by omega
    have hleft : tateFiltration m p = (⊤ : Submodule ℂ ℂ) := by
      simp [tateFiltration, hp]
    have hright : tateFiltration m (-2 * m + 1 - p) = (⊥ : Submodule ℂ ℂ) := by
      rw [tateFiltration]
      split
      · contradiction
      · rfl
    rw [hleft, hright, Submodule.map_bot]
    exact isCompl_top_bot
  · have hq : -2 * m + 1 - p ≤ -m := by omega
    have hleft : tateFiltration m p = (⊥ : Submodule ℂ ℂ) := by
      simp [tateFiltration, hp]
    have hright : tateFiltration m (-2 * m + 1 - p) = (⊤ : Submodule ℂ ℂ) := by
      rw [tateFiltration]
      split
      · rfl
      · contradiction
    rw [hleft, hright]
    simpa using (isCompl_bot_top : IsCompl (⊥ : Submodule ℂ ℂ) ⊤)

/-- The Tate Hodge structure `ℤ(m)`, of weight `-2m` and Hodge type `(-m,-m)`. -/
noncomputable def tate (m : ℤ) :
    HodgeStructure (V := ℤ) (Vℂ := ℂ) isBaseChange_tateLatticeMap (-2 * m) where
  F := tateFiltration m
  F_antitone := antitone_tateFiltration m
  F_top := ⟨-m, by simp [tateFiltration]⟩
  opposed := isCompl_tateFiltration m

/-- The Hodge filtration of `ℤ(m)` is the whole line exactly through degree `-m`. -/
@[simp]
theorem tate_F (m p : ℤ) :
    (tate m).F p = if p ≤ -m then (⊤ : Submodule ℂ ℂ) else ⊥ :=
  (rfl)

/-- The Tate Hodge structure is effective exactly when `m ≤ 0`. -/
@[simp]
theorem tate_isEffective_iff (m : ℤ) : (tate m).IsEffective ↔ m ≤ 0 := by
  rw [HodgeStructureOn.isEffective_iff]
  simp [tate_F]

/-- The only nonzero Hodge component of `ℤ(m)` is `H^{-m,-m}`. -/
@[simp]
theorem tate_piece (m p : ℤ) :
    (tate m).piece p = if p = -m then (⊤ : Submodule ℂ ℂ) else ⊥ := by
  rw [HodgeStructureOn.piece_def, HodgeStructureOn.conjF_def]
  by_cases heq : p = -m
  · subst p
    simp [two_mul]
  · by_cases hp : p ≤ -m
    · have hq : ¬ -2 * m - p ≤ -m := by omega
      have hleft : (tate m).F p = (⊤ : Submodule ℂ ℂ) := by simp [hp]
      have hright : (tate m).F (-2 * m - p) = (⊥ : Submodule ℂ ℂ) := by
        rw [tate_F]
        split
        · contradiction
        · rfl
      rw [hleft, hright, Submodule.map_bot, top_inf_eq]
      simp [heq]
    · have hleft : (tate m).F p = (⊥ : Submodule ℂ ℂ) := by simp [hp]
      rw [hleft, bot_inf_eq]
      simp [heq]

/-- The Hodge number of `ℤ(m)` is one in bidegree `(-m,-m)` and zero elsewhere. -/
@[simp]
theorem finrank_tate_piece (m p : ℤ) :
    Module.finrank ℂ ((tate m).piece p) = if p = -m then 1 else 0 := by
  by_cases hp : p = -m
  · have hpiece : (tate m).piece p = (⊤ : Submodule ℂ ℂ) := by
      rw [tate_piece]
      simp [hp]
    rw [hpiece]
    simp [hp]
  · have hpiece : (tate m).piece p = (⊥ : Submodule ℂ ℂ) := by
      rw [tate_piece]
      simp [hp]
    rw [hpiece]
    simp [hp]

end TauCeti.Hodge
