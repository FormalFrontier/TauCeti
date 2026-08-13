/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator

/-!
# Ladder and harmonic-oscillator operators on Schwartz space

This file packages the Hermite creation and annihilation operators as continuous linear
operators on the real Schwartz space `𝓢(ℝ, ℝ)`, proves their canonical commutation relation
(CCR) `[a, a†] = id`, and establishes their spectral properties on the Hermite Schwartz basis
`TauCeti.hermiteSchwartzMap n`.

## Main declarations

* `TauCeti.hermiteAnnihilationCLM` — the annihilation operator `a = (x + d/dx) / √2`.
* `TauCeti.hermiteCreationCLM` — the creation operator `a† = (x - d/dx) / √2`.
* `TauCeti.hermiteAnnihilation_comp_hermiteCreation_sub_creation_comp_annihilation`
  — canonical commutation relation `[a, a†] = id` (`a ∘L a† - a† ∘L a = id`).
* `TauCeti.hermiteAnnihilationCLM_apply_hermiteSchwartzMap` — `a ψₙ = √n • ψ_{n-1}`.
* `TauCeti.hermiteCreationCLM_apply_hermiteSchwartzMap` — `a† ψₙ = √(n+1) • ψ_{n+1}`.
* `TauCeti.hermiteNumberCLM` — the number operator `N = a† ∘L a`.
* `TauCeti.hermiteNumberCLM_apply_hermiteSchwartzMap` — `N ψₙ = n • ψₙ`.
* `TauCeti.hermiteOscillatorCLM` — the harmonic oscillator operator `H = N + (1/2) • id`.
* `TauCeti.hermiteOscillatorCLM_apply_hermiteSchwartzMap` — `H ψₙ = (n + 1/2) • ψₙ`.

## Reference

Roadmap: `OrthogonalL2Bases`, Part A2 (ladder operators on Schwartz space / L²).
-/

public section

namespace TauCeti

open SchwartzMap ContinuousLinearMap Real

/-- The annihilation operator `a = (x + d/dx) / √2` as a continuous linear operator on the real
Schwartz space `𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteAnnihilationCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  (Real.sqrt 2)⁻¹ • (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) + SchwartzMap.derivCLM ℝ ℝ)

/-- The creation operator `a† = (x - d/dx) / √2` as a continuous linear operator on the real
Schwartz space `𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteCreationCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  (Real.sqrt 2)⁻¹ • (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) - SchwartzMap.derivCLM ℝ ℝ)

/-- Pointwise evaluation of the annihilation operator `a f`. -/
@[simp]
theorem coe_hermiteAnnihilationCLM_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    hermiteAnnihilationCLM f x = (Real.sqrt 2)⁻¹ * (x * f x + deriv f x) := by
  dsimp [hermiteAnnihilationCLM]
  simp only [smul_apply, add_apply,
    smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    derivCLM_apply, smul_eq_mul]

/-- Pointwise evaluation of the creation operator `a† f`. -/
@[simp]
theorem coe_hermiteCreationCLM_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    hermiteCreationCLM f x = (Real.sqrt 2)⁻¹ * (x * f x - deriv f x) := by
  dsimp [hermiteCreationCLM]
  simp only [smul_apply, sub_apply,
    smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    derivCLM_apply, smul_eq_mul]

/-- **Annihilation action on Hermite functions.**
`a (hermiteSchwartzMap n) = √n • hermiteSchwartzMap (n - 1)`. -/
@[simp, grind =]
theorem hermiteAnnihilationCLM_apply_hermiteSchwartzMap (n : ℕ) :
    hermiteAnnihilationCLM (hermiteSchwartzMap n) =
      Real.sqrt (n : ℝ) • hermiteSchwartzMap (n - 1) := by
  dsimp [hermiteAnnihilationCLM]
  rw [smul_apply, add_apply, mul_add_deriv_hermiteSchwartzMap, smul_smul]
  have h2 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hs2, one_mul]

/-- **Creation action on Hermite functions.**
`a† (hermiteSchwartzMap n) = √(n + 1) • hermiteSchwartzMap (n + 1)`. -/
@[simp, grind =]
theorem hermiteCreationCLM_apply_hermiteSchwartzMap (n : ℕ) :
    hermiteCreationCLM (hermiteSchwartzMap n) =
      Real.sqrt ((n : ℝ) + 1) • hermiteSchwartzMap (n + 1) := by
  dsimp [hermiteCreationCLM]
  rw [smul_apply, sub_apply, mul_sub_deriv_hermiteSchwartzMap, smul_smul]
  have h2 : Real.sqrt (2 * ((n : ℝ) + 1)) = Real.sqrt 2 * Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_mul (by norm_num) _
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hs2, one_mul]

/-- **Canonical Commutator Relation (CCR) for the Hermite ladder operators.**
`[a, a†] = a ∘L a† - a† ∘L a = id`. -/
@[simp]
theorem hermiteAnnihilation_comp_hermiteCreation_sub_creation_comp_annihilation :
    hermiteAnnihilationCLM.comp hermiteCreationCLM -
        hermiteCreationCLM.comp hermiteAnnihilationCLM =
      ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by
  ext f x
  rw [sub_apply, comp_apply, comp_apply, id_apply]
  rw [sub_apply]
  have hs2_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_eq_one_div]
  have hdiff : DifferentiableAt ℝ f x := f.differentiableAt
  have hdiff_deriv : DifferentiableAt ℝ (deriv f) x :=
    (SchwartzMap.derivCLM ℝ ℝ f).differentiableAt
  have hD_creation : deriv (fun y => (Real.sqrt 2)⁻¹ * (y * f y - deriv f y)) x
      = (Real.sqrt 2)⁻¹ * (f x + x * deriv f x - deriv (deriv f) x) := by
    have h1 : HasDerivAt (fun y => y * f y - deriv f y)
        (1 * f x + x * deriv f x - deriv (deriv f) x) x := by
      have hd1 := (hasDerivAt_id' (x := x)).mul hdiff.hasDerivAt
      have hd2 := hdiff_deriv.hasDerivAt
      exact hd1.sub hd2
    have h2 := h1.const_mul (Real.sqrt 2)⁻¹
    simp only [one_mul] at h2
    exact h2.deriv
  have hD_annihilation : deriv (fun y => (Real.sqrt 2)⁻¹ * (y * f y + deriv f y)) x
      = (Real.sqrt 2)⁻¹ * (f x + x * deriv f x + deriv (deriv f) x) := by
    have h1 : HasDerivAt (fun y => y * f y + deriv f y)
        (1 * f x + x * deriv f x + deriv (deriv f) x) x := by
      have hd1 := (hasDerivAt_id' (x := x)).mul hdiff.hasDerivAt
      have hd2 := hdiff_deriv.hasDerivAt
      exact hd1.add hd2
    have h2 := h1.const_mul (Real.sqrt 2)⁻¹
    simp only [one_mul] at h2
    exact h2.deriv
  have h_ann_apply : hermiteAnnihilationCLM f =
      fun y => (Real.sqrt 2)⁻¹ * (y * f y + deriv f y) := by
    ext y
    exact coe_hermiteAnnihilationCLM_apply f y
  have h_cre_apply : hermiteCreationCLM f =
      fun y => (Real.sqrt 2)⁻¹ * (y * f y - deriv f y) := by
    ext y
    exact coe_hermiteCreationCLM_apply f y
  have h1 : (hermiteAnnihilationCLM (hermiteCreationCLM f)) x =
      (Real.sqrt 2)⁻¹ * (x * ((Real.sqrt 2)⁻¹ * (x * f x - deriv f x)) +
        (Real.sqrt 2)⁻¹ * (f x + x * deriv f x - deriv (deriv f) x)) := by
    rw [coe_hermiteAnnihilationCLM_apply, coe_hermiteCreationCLM_apply,
      h_cre_apply, hD_creation]
  have h2 : (hermiteCreationCLM (hermiteAnnihilationCLM f)) x =
      (Real.sqrt 2)⁻¹ * (x * ((Real.sqrt 2)⁻¹ * (x * f x + deriv f x)) -
        (Real.sqrt 2)⁻¹ * (f x + x * deriv f x + deriv (deriv f) x)) := by
    rw [coe_hermiteCreationCLM_apply, coe_hermiteAnnihilationCLM_apply,
      h_ann_apply, hD_annihilation]
  set c1 := (Real.sqrt 2)⁻¹ * (x * ((Real.sqrt 2)⁻¹ * (x * f x - deriv f x)) +
    (Real.sqrt 2)⁻¹ * (f x + x * deriv f x - deriv (deriv f) x))
  set c2 := (Real.sqrt 2)⁻¹ * (x * ((Real.sqrt 2)⁻¹ * (x * f x + deriv f x)) -
    (Real.sqrt 2)⁻¹ * (f x + x * deriv f x + deriv (deriv f) x))
  have h_combine : c1 - c2 =
      ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * f x := by
    dsimp [c1, c2]
    ring
  rw [h1, h2, h_combine, hs2_sq]
  ring

/-- The Hermite number operator `N = a† ∘L a` as a continuous linear operator on `𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteNumberCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  hermiteCreationCLM.comp hermiteAnnihilationCLM

/-- **Action of the number operator on Hermite functions.**
`N (hermiteSchwartzMap n) = n • hermiteSchwartzMap n`. -/
@[simp, grind =]
theorem hermiteNumberCLM_apply_hermiteSchwartzMap (n : ℕ) :
    hermiteNumberCLM (hermiteSchwartzMap n) = (n : ℝ) • hermiteSchwartzMap n := by
  dsimp [hermiteNumberCLM]
  rw [hermiteAnnihilationCLM_apply_hermiteSchwartzMap]
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, map_smul, hermiteCreationCLM_apply_hermiteSchwartzMap,
      smul_smul, Nat.cast_add, Nat.cast_one]
    have hsq : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    rw [hsq]

/-- The harmonic oscillator operator `H = N + (1/2) • id` as a continuous linear operator on
`𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteOscillatorCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  hermiteNumberCLM + (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ)

/-- **Action of the harmonic oscillator operator on Hermite functions.**
`H (hermiteSchwartzMap n) = (n + 1/2) • hermiteSchwartzMap n`. -/
@[simp, grind =]
theorem hermiteOscillatorCLM_apply_hermiteSchwartzMap (n : ℕ) :
    hermiteOscillatorCLM (hermiteSchwartzMap n) = ((n : ℝ) + 1 / 2) • hermiteSchwartzMap n := by
  dsimp [hermiteOscillatorCLM]
  rw [add_apply, smul_apply, id_apply, hermiteNumberCLM_apply_hermiteSchwartzMap, ← add_smul]

end TauCeti
