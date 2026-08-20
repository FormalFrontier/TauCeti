/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Polarization
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Tate Hodge structures

The Tate structure `ℤ(m)` is the rank-one pure Hodge structure of weight `-2m` and type
`(-m,-m)`. Its complexification is `ℂ`, with the integral lattice embedded by the usual map
`ℤ → ℂ`; its decreasing filtration is the whole line through degree `-m` and zero above it.

This is the first concrete nonzero inhabitant of `TauCeti.Hodge.HodgeStructure`. Besides fixing the
weight and filtration-shift conventions needed by later Tate twists, it verifies directly that the
opposed-filtration definition has the intended rank-one objects. Multiplication of integers
polarizes it, so it also witnesses that the Hodge–Riemann relations are satisfiable.

The convention follows the Hodge structures roadmap and standard Hodge-theory notation; see
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.

## Main declarations

* `TauCeti.Hodge.tate`: the Tate Hodge structure `ℤ(m)` of weight `-2m`.
* `TauCeti.Hodge.tate_F`: its filtration is `⊤` exactly in degrees at most `-m`.
* `TauCeti.Hodge.tate_piece`: its only nonzero Hodge component has bidegree `(-m,-m)`.
* `TauCeti.Hodge.finrank_tate_piece`: its Hodge number there is one and all others are zero.
* `TauCeti.Hodge.isPolarization_tate`: multiplication of integers satisfies the Hodge–Riemann
  relations for it, and `TauCeti.Hodge.tatePolarization` bundles that as a polarization.
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

/-- The Tate Hodge structure is effective exactly when `m ≤ 0`. This is not a `simp` lemma: with
`HodgeStructureOn.isEffective_iff` tagged, `simp` already normalizes the left-hand side. -/
theorem tate_isEffective_iff (m : ℤ) : (tate m).IsEffective ↔ m ≤ 0 := by
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
  rw [tate_piece, apply_ite (fun S : Submodule ℂ ℂ ↦ Module.finrank ℂ S)]
  simp

/-! ### The polarization of a Tate structure -/

/-- The conjugation of the Tate complexification is complex conjugation. -/
theorem latticeConj_tateLatticeMap (z : ℂ) :
    latticeConj isBaseChange_tateLatticeMap z = starRingEnd ℂ z := by
  have huniq := latticeConj_unique isBaseChange_tateLatticeMap (starRingEnd ℂ).toSemilinearMap
    (fun v ↦ by simp)
  exact congrArg (fun f ↦ f z) huniq.symm

/-- The complexification of integer multiplication is complex multiplication. -/
theorem integralFormToComplex_tateLatticeMap_mul :
    integralFormToComplex isBaseChange_tateLatticeMap (LinearMap.mul ℤ ℤ) =
      LinearMap.mul ℂ ℂ :=
  (integralFormToComplex_unique isBaseChange_tateLatticeMap _ _ fun x y ↦ by simp).symm

/-- Multiplication of integers satisfies the Hodge–Riemann relations for `ℤ(m)`. -/
theorem isPolarization_tate (m : ℤ) :
    IsPolarization isBaseChange_tateLatticeMap (tate m) (LinearMap.mul ℤ ℤ) where
  symm_weight x y := by
    rw [Int.negOnePow_even _ ⟨-m, by ring⟩]
    simp [mul_comm]
  nondegenerate := ⟨fun x hx ↦ by simpa using hx 1, fun y hy ↦ by simpa using hy 1⟩
  orthogonal p x hx y hy := by
    by_cases hp : p ≤ -m
    · have hcond : ¬ -2 * m + 1 - p ≤ -m := by omega
      have hbot : (tate m).F (-2 * m + 1 - p) = (⊥ : Submodule ℂ ℂ) := by
        rw [tate_F]
        exact ite_eq_right hcond
      rw [hbot, Submodule.mem_bot] at hy
      simp [hy]
    · have hbot : (tate m).F p = (⊥ : Submodule ℂ ℂ) := by simp [hp]
      rw [hbot, Submodule.mem_bot] at hx
      simp [hx]
  positive p x hx hx0 := by
    by_cases hp : p = -m
    · subst hp
      have hexp : 2 * -m - -2 * m = 0 := by ring
      rw [hexp, zpow_zero, one_mul, integralFormToComplex_tateLatticeMap_mul,
        latticeConj_tateLatticeMap]
      simpa [Complex.mul_conj] using Complex.normSq_pos.mpr hx0
    · have hbot : (tate m).piece p = (⊥ : Submodule ℂ ℂ) := by simp [hp]
      rw [hbot, Submodule.mem_bot] at hx
      exact absurd hx hx0

/-- The Tate Hodge structure `ℤ(m)`, polarized by multiplication of integers. -/
def tatePolarization (m : ℤ) :
    Polarization isBaseChange_tateLatticeMap (tate m) where
  Qint := LinearMap.mul ℤ ℤ
  isPolarization := isPolarization_tate m

/-- The complex form of the Tate polarization is multiplication on the complex line. -/
@[simp]
theorem tatePolarization_Q (m : ℤ) :
    (tatePolarization m).Q = LinearMap.mul ℂ ℂ := by
  rw [Polarization.Q_def, tatePolarization, integralFormToComplex_tateLatticeMap_mul]

/-- The Tate Hodge structure is polarizable. -/
theorem isPolarizable_tate (m : ℤ) : IsPolarizable isBaseChange_tateLatticeMap (tate m) :=
  (tatePolarization m).isPolarizable

end TauCeti.Hodge
