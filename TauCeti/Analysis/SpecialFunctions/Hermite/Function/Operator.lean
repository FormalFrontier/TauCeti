/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz

/-!
# Ladder and harmonic-oscillator operators on Schwartz space

This file packages the Hermite creation and annihilation operators as continuous linear
operators on the real Schwartz space `𝓢(ℝ, ℝ)`, proves their canonical commutation relation
(CCR) `[a, a†] = id`, and establishes their spectral properties on the family of Hermite Schwartz
functions `TauCeti.hermiteSchwartzMap n`.

## Main declarations

* `TauCeti.hermiteAnnihilationCLM` — the annihilation operator `a = (x + d/dx) / √2`.
* `TauCeti.hermiteCreationCLM` — the creation operator `a† = (x - d/dx) / √2`.
* The canonical commutation relation `[a, a†] = id` (`a ∘L a† - a† ∘L a = id`).
* `TauCeti.hermiteAnnihilationCLM_apply_hermiteSchwartzMap` — `a ψₙ = √n • ψ_{n-1}`.
* `TauCeti.hermiteCreationCLM_apply_hermiteSchwartzMap` — `a† ψₙ = √(n+1) • ψ_{n+1}`.
* `TauCeti.hermiteNumberCLM` — the number operator `N = a† ∘L a`.
* `TauCeti.hermiteNumberCLM_apply_hermiteSchwartzMap` — `N ψₙ = n • ψₙ`.
* `TauCeti.hermiteOscillatorCLM` — the harmonic oscillator operator `H = N + (1/2) • id`.
* `TauCeti.hermiteOscillatorCLM_apply_apply` — the differential action of `H`.
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
theorem hermiteAnnihilationCLM_apply_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    hermiteAnnihilationCLM f x = (Real.sqrt 2)⁻¹ * (x * f x + deriv f x) := by
  dsimp [hermiteAnnihilationCLM]
  simp only [smul_apply, add_apply,
    smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    derivCLM_apply, smul_eq_mul]

/-- Pointwise evaluation of the creation operator `a† f`. -/
@[simp]
theorem hermiteCreationCLM_apply_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
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

/-- The commutator of differentiation with multiplication by the position coordinate is the
identity operator on the real Schwartz space. -/
@[simp]
private theorem derivCLM_comp_smulLeftCLM_id_sub_smulLeftCLM_id_comp_derivCLM :
    (SchwartzMap.derivCLM ℝ ℝ).comp
          (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)) -
        (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)).comp
          (SchwartzMap.derivCLM ℝ ℝ) =
      ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by
  ext f x
  simp only [sub_apply, comp_apply, id_apply, derivCLM_apply,
    smulLeftCLM_apply_apply Function.HasTemperateGrowth.id', smul_eq_mul]
  have hmul :
      SchwartzMap.smulLeftCLM ℝ (fun y : ℝ => y) f = fun y => y * f y := by
    ext y
    simp only [smulLeftCLM_apply_apply Function.HasTemperateGrowth.id', smul_eq_mul]
  rw [hmul]
  have hderiv : deriv (fun y => y * f y) x = f x + x * deriv f x := by
    have hfun : (fun y : ℝ => y * f y) = (fun y : ℝ => y) * ⇑f := by
      ext y
      simp only [Pi.mul_apply]
    rw [hfun]
    simpa using ((hasDerivAt_id' (x := x)).mul f.differentiableAt.hasDerivAt).deriv
  rw [hderiv]
  ring

/-- **Canonical Commutation Relation (CCR) for the Hermite ladder operators.**
`[a, a†] = a ∘L a† - a† ∘L a = id`. -/
@[simp]
theorem
hermiteAnnihilationCLM_comp_hermiteCreationCLM_sub_hermiteCreationCLM_comp_hermiteAnnihilationCLM :
    hermiteAnnihilationCLM.comp hermiteCreationCLM -
        hermiteCreationCLM.comp hermiteAnnihilationCLM =
      ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by
  let X := SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)
  let D := SchwartzMap.derivCLM ℝ ℝ
  let c := (Real.sqrt 2)⁻¹
  have hcomm : D.comp X - X.comp D = ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by
    simpa only [X, D] using derivCLM_comp_smulLeftCLM_id_sub_smulLeftCLM_id_comp_derivCLM
  have hc : c * c = (1 / 2 : ℝ) := by
    dsimp only [c]
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_eq_one_div]
  have hA : hermiteAnnihilationCLM = c • (X + D) := by
    simp only [hermiteAnnihilationCLM, c, X, D]
  have hC : hermiteCreationCLM = c • (X - D) := by
    simp only [hermiteCreationCLM, c, X, D]
  rw [hA, hC]
  calc
    (c • (X + D)).comp (c • (X - D)) - (c • (X - D)).comp (c • (X + D)) =
        (c * c * 2) • (D.comp X - X.comp D) := by
      simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp]
      module
    _ = ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by rw [hcomm, hc]; norm_num

/-- The Hermite number operator `N = a† ∘L a` as a continuous linear operator on `𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteNumberCLM : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) :=
  hermiteCreationCLM.comp hermiteAnnihilationCLM

/-- Pointwise differential action of the number operator:
`Nf = (x²f - f - f'') / 2`. -/
@[simp]
theorem hermiteNumberCLM_apply_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    hermiteNumberCLM f x = ((x ^ 2 - 1) * f x - deriv (deriv f) x) / 2 := by
  let X := SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)
  let D := SchwartzMap.derivCLM ℝ ℝ
  let c := (Real.sqrt 2)⁻¹
  have hcomm : D.comp X - X.comp D = ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) := by
    simpa only [X, D] using derivCLM_comp_smulLeftCLM_id_sub_smulLeftCLM_id_comp_derivCLM
  have hDX : D.comp X = X.comp D + ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ) :=
    sub_eq_iff_eq_add'.mp hcomm
  have hc : c * c = (1 / 2 : ℝ) := by
    dsimp only [c]
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_eq_one_div]
  have hA : hermiteAnnihilationCLM = c • (X + D) := by
    simp only [hermiteAnnihilationCLM, c, X, D]
  have hC : hermiteCreationCLM = c • (X - D) := by
    simp only [hermiteCreationCLM, c, X, D]
  have hnumber : hermiteNumberCLM =
      (1 / 2 : ℝ) • (X.comp X - D.comp D - ContinuousLinearMap.id ℝ 𝓢(ℝ, ℝ)) := by
    rw [hermiteNumberCLM, hA, hC]
    simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.sub_comp]
    rw [hDX, ← hc]
    module
  rw [hnumber]
  dsimp only [X, D]
  simp only [smul_apply, sub_apply, comp_apply, id_apply, derivCLM_apply,
    smulLeftCLM_apply_apply Function.HasTemperateGrowth.id', smul_eq_mul]
  have hderivCLM : ⇑(SchwartzMap.derivCLM ℝ ℝ f) = deriv f :=
    funext (SchwartzMap.derivCLM_apply ℝ f)
  rw [hderivCLM]
  ring

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

/-- Pointwise differential action of the harmonic oscillator operator:
`Hf = (-f'' + x²f) / 2`. -/
@[simp]
theorem hermiteOscillatorCLM_apply_apply (f : 𝓢(ℝ, ℝ)) (x : ℝ) :
    hermiteOscillatorCLM f x = (-deriv (deriv f) x + x ^ 2 * f x) / 2 := by
  simp only [hermiteOscillatorCLM, add_apply, smul_apply, id_apply,
    hermiteNumberCLM_apply_apply, smul_eq_mul]
  ring

/-- **Action of the harmonic oscillator operator on Hermite functions.**
`H (hermiteSchwartzMap n) = (n + 1/2) • hermiteSchwartzMap n`. -/
@[simp, grind =]
theorem hermiteOscillatorCLM_apply_hermiteSchwartzMap (n : ℕ) :
    hermiteOscillatorCLM (hermiteSchwartzMap n) = ((n : ℝ) + 1 / 2) • hermiteSchwartzMap n := by
  dsimp [hermiteOscillatorCLM]
  rw [add_apply, smul_apply, id_apply, hermiteNumberCLM_apply_hermiteSchwartzMap, ← add_smul]

end TauCeti
