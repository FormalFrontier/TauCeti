module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.MemLp

/-!
# Hermite functions as Fourier eigenfunctions

Mathlib's Fourier transform uses the character `exp (-2πixξ)`, whereas the Hermite functions
`TauCeti.hermiteFunction` use the angular-frequency normalization. This file introduces the
unitarily rescaled family

`Φₙ(x) = √(√(2π)) ψₙ(√(2π)x)`

and proves that `𝓕 Φₙ = (-i)ⁿ Φₙ`. The dilation is load-bearing: the unscaled Gaussian
`exp (-x² / 2)` is not self-dual for Mathlib's Fourier convention, while `exp (-πx²)` is.

## Main statements

* `TauCeti.twoPiHermiteFunction` is the `2π`-normalized Hermite family.
* `TauCeti.fourier_twoPiHermiteFunction` states its Fourier eigenvalue `(-i)ⁿ`.

## References

* G. B. Folland, *Harmonic Analysis in Phase Space*, §1, for the standard normalization and
  Fourier eigenvalue identity.
-/

public section

namespace TauCeti

open MeasureTheory Real
open scoped FourierTransform

/-- The Hermite function rescaled to Mathlib's `exp (-2πixξ)` Fourier convention:
`Φₙ(x) = √(√(2π)) ψₙ(√(2π)x)`. The outer factor makes the dilation unitary on `L²`. -/
noncomputable def twoPiHermiteFunction (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (2 * Real.pi)) *
    hermiteFunction n (Real.sqrt (2 * Real.pi) * x)

/-- The defining equation for the Hermite function rescaled to Mathlib's Fourier convention. -/
theorem twoPiHermiteFunction_def (n : ℕ) (x : ℝ) :
    twoPiHermiteFunction n x =
      Real.sqrt (Real.sqrt (2 * Real.pi)) *
        hermiteFunction n (Real.sqrt (2 * Real.pi) * x) :=
  twoPiHermiteFunction.eq_1 n x

private lemma hermiteFourierScale_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)

private lemma hermiteFourierScale_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
  hermiteFourierScale_pos.ne'

private lemma hermiteFourierScale_sq :
    Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
  Real.sq_sqrt (mul_nonneg (by positivity) Real.pi_pos.le)

/-- The zeroth rescaled Hermite function is a constant multiple of the self-dual Gaussian
`exp (-πx²)`. -/
@[simp]
theorem twoPiHermiteFunction_zero (x : ℝ) :
    twoPiHermiteFunction 0 x =
      (Real.sqrt (Real.sqrt (2 * Real.pi)) / Real.sqrt (Real.sqrt Real.pi)) *
        Real.exp (-Real.pi * x ^ 2) := by
  rw [twoPiHermiteFunction_def, hermiteFunction_zero]
  have hexp :
      -((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2) = -Real.pi * x ^ 2 := by
    rw [mul_pow, hermiteFourierScale_sq]
    ring
  rw [hexp]
  ring

/-- The rescaled Hermite functions are continuous. -/
@[fun_prop]
theorem continuous_twoPiHermiteFunction (n : ℕ) :
    Continuous (twoPiHermiteFunction n) := by
  unfold twoPiHermiteFunction
  exact continuous_const.mul
    ((continuous_hermiteFunction n).comp (continuous_const.mul continuous_id))

/-- The position ladder relation after the `√(2π)` dilation. -/
theorem mul_twoPiHermiteFunction (n : ℕ) (x : ℝ) :
    x * twoPiHermiteFunction n x =
      (Real.sqrt (((n : ℝ) + 1) / 2) / Real.sqrt (2 * Real.pi)) *
          twoPiHermiteFunction (n + 1) x
        + (Real.sqrt ((n : ℝ) / 2) / Real.sqrt (2 * Real.pi)) *
          twoPiHermiteFunction (n - 1) x := by
  have h := mul_hermiteFunction n (Real.sqrt (2 * Real.pi) * x)
  simp only [twoPiHermiteFunction_def]
  calc
    x * (Real.sqrt (Real.sqrt (2 * Real.pi)) *
        hermiteFunction n (Real.sqrt (2 * Real.pi) * x)) =
        (Real.sqrt (Real.sqrt (2 * Real.pi)) / Real.sqrt (2 * Real.pi)) *
          (Real.sqrt (2 * Real.pi) * x *
            hermiteFunction n (Real.sqrt (2 * Real.pi) * x)) := by
              field_simp [hermiteFourierScale_ne_zero]
    _ = (Real.sqrt (Real.sqrt (2 * Real.pi)) / Real.sqrt (2 * Real.pi)) *
        (Real.sqrt (((n : ℝ) + 1) / 2) *
            hermiteFunction (n + 1) (Real.sqrt (2 * Real.pi) * x)
          + Real.sqrt ((n : ℝ) / 2) *
            hermiteFunction (n - 1) (Real.sqrt (2 * Real.pi) * x)) := by rw [h]
    _ = (Real.sqrt (((n : ℝ) + 1) / 2) / Real.sqrt (2 * Real.pi)) *
          (Real.sqrt (Real.sqrt (2 * Real.pi)) *
            hermiteFunction (n + 1) (Real.sqrt (2 * Real.pi) * x))
        + (Real.sqrt ((n : ℝ) / 2) / Real.sqrt (2 * Real.pi)) *
          (Real.sqrt (Real.sqrt (2 * Real.pi)) *
            hermiteFunction (n - 1) (Real.sqrt (2 * Real.pi) * x)) := by ring

/-- The derivative ladder relation after the `√(2π)` dilation. -/
theorem hasDerivAt_twoPiHermiteFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (twoPiHermiteFunction n)
      (Real.sqrt (2 * Real.pi) *
        (Real.sqrt ((n : ℝ) / 2) * twoPiHermiteFunction (n - 1) x
          - Real.sqrt (((n : ℝ) + 1) / 2) * twoPiHermiteFunction (n + 1) x)) x := by
  have hcomp := (hasDerivAt_hermiteFunction n (Real.sqrt (2 * Real.pi) * x)).comp x
    ((hasDerivAt_const x (Real.sqrt (2 * Real.pi))).mul (hasDerivAt_id x))
  have h := hcomp.const_mul (Real.sqrt (Real.sqrt (2 * Real.pi)))
  have hsimp : HasDerivAt
      (fun y => Real.sqrt (Real.sqrt (2 * Real.pi)) *
        hermiteFunction n (Real.sqrt (2 * Real.pi) * y))
      (Real.sqrt (Real.sqrt (2 * Real.pi)) *
        ((Real.sqrt ((n : ℝ) / 2) *
              hermiteFunction (n - 1) (Real.sqrt (2 * Real.pi) * x)
            - Real.sqrt (((n : ℝ) + 1) / 2) *
              hermiteFunction (n + 1) (Real.sqrt (2 * Real.pi) * x)) *
          Real.sqrt (2 * Real.pi))) x := by
    simpa only [Function.comp_apply, zero_mul, add_mul, zero_add, one_mul, mul_one] using h
  have h' : HasDerivAt (twoPiHermiteFunction n)
      (Real.sqrt (Real.sqrt (2 * Real.pi)) *
        ((Real.sqrt ((n : ℝ) / 2) *
              hermiteFunction (n - 1) (Real.sqrt (2 * Real.pi) * x)
            - Real.sqrt (((n : ℝ) + 1) / 2) *
              hermiteFunction (n + 1) (Real.sqrt (2 * Real.pi) * x)) *
          Real.sqrt (2 * Real.pi))) x := by
    apply hsimp.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => (twoPiHermiteFunction_def n y).symm
  have hval :
      Real.sqrt (Real.sqrt (2 * Real.pi)) *
          ((Real.sqrt ((n : ℝ) / 2) *
                hermiteFunction (n - 1) (Real.sqrt (2 * Real.pi) * x)
              - Real.sqrt (((n : ℝ) + 1) / 2) *
                hermiteFunction (n + 1) (Real.sqrt (2 * Real.pi) * x)) *
            Real.sqrt (2 * Real.pi))
        = Real.sqrt (2 * Real.pi) *
          (Real.sqrt ((n : ℝ) / 2) * twoPiHermiteFunction (n - 1) x
            - Real.sqrt (((n : ℝ) + 1) / 2) * twoPiHermiteFunction (n + 1) x) := by
    simp only [twoPiHermiteFunction_def]
    ring
  exact hval ▸ h'

/-- The derivative form of `hasDerivAt_twoPiHermiteFunction`. -/
@[simp]
theorem deriv_twoPiHermiteFunction (n : ℕ) (x : ℝ) :
    deriv (twoPiHermiteFunction n) x =
      Real.sqrt (2 * Real.pi) *
        (Real.sqrt ((n : ℝ) / 2) * twoPiHermiteFunction (n - 1) x
          - Real.sqrt (((n : ℝ) + 1) / 2) * twoPiHermiteFunction (n + 1) x) :=
  (hasDerivAt_twoPiHermiteFunction n x).deriv

/-- The creation relation for the rescaled family. -/
theorem mul_sub_invScale_deriv_twoPiHermiteFunction (n : ℕ) (x : ℝ) :
    Real.sqrt (2 * Real.pi) * x * twoPiHermiteFunction n x
        - (Real.sqrt (2 * Real.pi))⁻¹ * deriv (twoPiHermiteFunction n) x
      = Real.sqrt (2 * ((n : ℝ) + 1)) * twoPiHermiteFunction (n + 1) x := by
  have h := mul_sub_deriv_hermiteFunction n (Real.sqrt (2 * Real.pi) * x)
  have hderiv := deriv_hermiteFunction n (Real.sqrt (2 * Real.pi) * x)
  rw [deriv_twoPiHermiteFunction]
  simp only [twoPiHermiteFunction_def]
  rw [← mul_assoc (Real.sqrt (2 * Real.pi))⁻¹, inv_mul_cancel₀ hermiteFourierScale_ne_zero,
    one_mul]
  linear_combination
    Real.sqrt (Real.sqrt (2 * Real.pi)) * h +
    Real.sqrt (Real.sqrt (2 * Real.pi)) * hderiv

/-- Every rescaled Hermite function is integrable. -/
theorem integrable_twoPiHermiteFunction (n : ℕ) :
    Integrable (twoPiHermiteFunction n) volume := by
  have h :=
    ((integrable_hermiteFunction n).comp_mul_left' hermiteFourierScale_ne_zero).const_mul
      (Real.sqrt (Real.sqrt (2 * Real.pi)))
  exact h.congr (Filter.Eventually.of_forall fun x => (twoPiHermiteFunction_def n x).symm)

private theorem integrable_mul_twoPiHermiteFunction (n : ℕ) :
    Integrable (fun x : ℝ => x * twoPiHermiteFunction n x) volume := by
  have hfun : (fun x : ℝ => x * twoPiHermiteFunction n x) =
      fun x =>
        (Real.sqrt (((n : ℝ) + 1) / 2) / Real.sqrt (2 * Real.pi)) *
            twoPiHermiteFunction (n + 1) x
          + (Real.sqrt ((n : ℝ) / 2) / Real.sqrt (2 * Real.pi)) *
            twoPiHermiteFunction (n - 1) x := by
    funext x
    exact mul_twoPiHermiteFunction n x
  rw [hfun]
  exact
    ((integrable_twoPiHermiteFunction (n + 1)).const_mul _).add
      ((integrable_twoPiHermiteFunction (n - 1)).const_mul _)

private theorem integrable_deriv_twoPiHermiteFunction (n : ℕ) :
    Integrable (deriv (twoPiHermiteFunction n)) volume := by
  have hfun : deriv (twoPiHermiteFunction n) = fun x =>
      Real.sqrt (2 * Real.pi) * Real.sqrt ((n : ℝ) / 2) *
          twoPiHermiteFunction (n - 1) x
        - Real.sqrt (2 * Real.pi) * Real.sqrt (((n : ℝ) + 1) / 2) *
          twoPiHermiteFunction (n + 1) x := by
    funext x
    rw [deriv_twoPiHermiteFunction]
    ring
  rw [hfun]
  exact
    ((integrable_twoPiHermiteFunction (n - 1)).const_mul _).sub
      ((integrable_twoPiHermiteFunction (n + 1)).const_mul _)

private theorem integrable_twoPiHermiteFunction_complex (n : ℕ) :
    Integrable (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) volume :=
  (integrable_twoPiHermiteFunction n).ofReal

private theorem integrable_mul_twoPiHermiteFunction_complex (n : ℕ) :
    Integrable (fun x : ℝ => x • (twoPiHermiteFunction n x : ℂ)) volume := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x • (twoPiHermiteFunction n x : ℂ)) volume :=
    (continuous_id.smul
      (Complex.continuous_ofReal.comp (continuous_twoPiHermiteFunction n))).aestronglyMeasurable
  refine (MeasureTheory.integrable_norm_iff hmeas).1 ?_
  simpa only [norm_smul, Real.norm_eq_abs, Complex.norm_real, abs_mul] using
    (integrable_mul_twoPiHermiteFunction n).norm

private theorem hasDerivAt_twoPiHermiteFunction_complex (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (twoPiHermiteFunction n y : ℂ))
      ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ) x := by
  simpa only [deriv_twoPiHermiteFunction] using
    (hasDerivAt_twoPiHermiteFunction n x).ofReal_comp

private theorem differentiable_twoPiHermiteFunction_complex (n : ℕ) :
    Differentiable ℝ fun x : ℝ => (twoPiHermiteFunction n x : ℂ) :=
  fun x => (hasDerivAt_twoPiHermiteFunction_complex n x).differentiableAt

private theorem deriv_twoPiHermiteFunction_complex (n : ℕ) :
    deriv (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) =
      fun x => ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ) := by
  funext x
  exact (hasDerivAt_twoPiHermiteFunction_complex n x).deriv

private theorem integrable_deriv_twoPiHermiteFunction_complex (n : ℕ) :
    Integrable (deriv fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) volume := by
  rw [deriv_twoPiHermiteFunction_complex]
  exact (integrable_deriv_twoPiHermiteFunction n).ofReal

private theorem fourier_const_smul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (c • f) = c • 𝓕 f := by
  funext w
  simp only [Pi.smul_apply]
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  exact smul_comm (𝐞 (-(v * w))) c (f v)

private theorem fourier_twoPiHermiteFunction_zero :
    𝓕 (fun x : ℝ => (twoPiHermiteFunction 0 x : ℂ)) =
      fun x : ℝ => (twoPiHermiteFunction 0 x : ℂ) := by
  have hgauss :
      𝓕 (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
        fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ) := by
    have hg := fourier_gaussian_pi (b := 1) zero_lt_one
    simp only [Complex.one_cpow, one_div, one_mul, mul_one, div_one] at hg
    have hexp :
        (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) =
          fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ) := by
      funext x
      calc
        Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) =
            Complex.exp ((-Real.pi * x ^ 2 : ℝ) : ℂ) := by
              congr 1
              push_cast
              ring
        _ = (Real.exp (-Real.pi * x ^ 2) : ℂ) := (Complex.ofReal_exp _).symm
    rw [hexp] at hg
    exact hg
  have hfun :
      (fun x : ℝ => (twoPiHermiteFunction 0 x : ℂ)) =
        (Real.sqrt (Real.sqrt (2 * Real.pi)) / Real.sqrt (Real.sqrt Real.pi) : ℂ) •
          fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    exact_mod_cast twoPiHermiteFunction_zero x
  let c : ℂ :=
    (Real.sqrt (Real.sqrt (2 * Real.pi)) / Real.sqrt (Real.sqrt Real.pi) : ℂ)
  let g : ℝ → ℂ := fun x => (Real.exp (-Real.pi * x ^ 2) : ℂ)
  calc
    𝓕 (fun x : ℝ => (twoPiHermiteFunction 0 x : ℂ)) = 𝓕 (c • g) := by rw [hfun]
    _ = c • 𝓕 g := fourier_const_smul c g
    _ = c • g := by rw [hgauss]
    _ = fun x : ℝ => (twoPiHermiteFunction 0 x : ℂ) := hfun.symm

private theorem twoPiHermiteFunction_succ_complex (n : ℕ) :
    (fun x : ℝ => (twoPiHermiteFunction (n + 1) x : ℂ)) =
      (Real.sqrt (2 * ((n : ℝ) + 1)) : ℂ)⁻¹ •
        ((Real.sqrt (2 * Real.pi) : ℂ) •
            (fun x : ℝ => x • (twoPiHermiteFunction n x : ℂ))
          + (-(Real.sqrt (2 * Real.pi) : ℂ)⁻¹) •
            (fun x : ℝ => ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ))) := by
  funext x
  have ha : Real.sqrt (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hr := mul_sub_invScale_deriv_twoPiHermiteFunction n x
  have hr' :
      twoPiHermiteFunction (n + 1) x =
        (Real.sqrt (2 * ((n : ℝ) + 1)))⁻¹ *
          (Real.sqrt (2 * Real.pi) * x * twoPiHermiteFunction n x
            - (Real.sqrt (2 * Real.pi))⁻¹ * deriv (twoPiHermiteFunction n) x) := by
    rw [hr]
    field_simp [ha]
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hr'
  calc
    (twoPiHermiteFunction (n + 1) x : ℂ) =
        ((Real.sqrt (2 * ((n : ℝ) + 1)))⁻¹ *
          (Real.sqrt (2 * Real.pi) * x * twoPiHermiteFunction n x
            - (Real.sqrt (2 * Real.pi))⁻¹ *
              deriv (twoPiHermiteFunction n) x) : ℝ) := hc
    _ = (Real.sqrt (2 * ((n : ℝ) + 1)) : ℂ)⁻¹ *
        ((Real.sqrt (2 * Real.pi) : ℂ) * (x • (twoPiHermiteFunction n x : ℂ))
          + (-(Real.sqrt (2 * Real.pi) : ℂ)⁻¹) *
            ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ)) := by
      push_cast
      rw [Complex.real_smul]
      ring

private theorem fourier_mul_twoPiHermiteFunction_of_eigen (n : ℕ) (eigen : ℂ)
    (hfourier :
      𝓕 (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) =
        fun x => eigen * twoPiHermiteFunction n x) :
    𝓕 (fun x : ℝ => x • (twoPiHermiteFunction n x : ℂ)) =
      fun w => Complex.I / (2 * Real.pi) * eigen *
        ((deriv (twoPiHermiteFunction n) w : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x => (twoPiHermiteFunction n x : ℂ)
  let xf : ℝ → ℂ := fun x => x • f x
  funext w
  have hd := congrFun (Real.deriv_fourier
    (integrable_twoPiHermiteFunction_complex n)
    (integrable_mul_twoPiHermiteFunction_complex n)) w
  have hleft : deriv (𝓕 f) w =
      eigen * ((deriv (twoPiHermiteFunction n) w : ℝ) : ℂ) := by
    rw [hfourier]
    exact ((hasDerivAt_twoPiHermiteFunction_complex n w).const_mul eigen).deriv
  have hweighted :
      (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • f x) =
        (-2 * Real.pi * Complex.I) • xf := by
    funext x
    dsimp only [xf]
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  rw [hleft, hweighted, fourier_const_smul, Pi.smul_apply, smul_eq_mul] at hd
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [mul_assoc (Complex.I / (2 * Real.pi)) eigen, hd]
  field_simp [hpi]
  rw [pow_two, Complex.I_mul_I]
  ring

private theorem fourier_deriv_twoPiHermiteFunction_of_eigen (n : ℕ) (eigen : ℂ)
    (hfourier :
      𝓕 (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) =
        fun x => eigen * twoPiHermiteFunction n x) :
    𝓕 (fun x : ℝ => ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ)) =
      fun w => (2 * Real.pi * Complex.I * w) * eigen * twoPiHermiteFunction n w := by
  have hd := Real.fourier_deriv
    (integrable_twoPiHermiteFunction_complex n)
    (differentiable_twoPiHermiteFunction_complex n)
    (integrable_deriv_twoPiHermiteFunction_complex n)
  rw [deriv_twoPiHermiteFunction_complex, hfourier] at hd
  simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hd

/-- The Fourier transform of the successor, in terms of the transforms of `x ↦ x · hₙ x` and of
`hₙ'`: the raising relation `twoPiHermiteFunction_succ_complex` pushed through linearity of the
transform. No eigenfunction hypothesis is involved, so this holds for every `n`. -/
private theorem fourier_twoPiHermiteFunction_succ_eq (n : ℕ) (w : ℝ) :
    𝓕 (fun x : ℝ => (twoPiHermiteFunction (n + 1) x : ℂ)) w =
      (Real.sqrt (2 * ((n : ℝ) + 1)) : ℂ)⁻¹ *
        ((Real.sqrt (2 * Real.pi) : ℂ) *
            𝓕 (fun x : ℝ => x • (twoPiHermiteFunction n x : ℂ)) w
          + (-(Real.sqrt (2 * Real.pi) : ℂ)⁻¹) *
            𝓕 (fun x : ℝ => ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ)) w) := by
  let s : ℂ := Real.sqrt (2 * Real.pi)
  let xf : ℝ → ℂ := fun x => x • (twoPiHermiteFunction n x : ℂ)
  let df : ℝ → ℂ := fun x => ((deriv (twoPiHermiteFunction n) x : ℝ) : ℂ)
  -- Each summand of the raising relation is integrable, which is what linearity needs.
  have hsxf : Integrable (s • xf) volume := by
    apply ((integrable_mul_twoPiHermiteFunction_complex n).const_mul s).congr
    exact Filter.Eventually.of_forall fun x => by rw [Pi.smul_apply, smul_eq_mul]
  have hinvdf : Integrable ((-s⁻¹) • df) volume := by
    dsimp only [df]
    apply ((integrable_deriv_twoPiHermiteFunction n).ofReal.const_mul (-s⁻¹)).congr
    exact Filter.Eventually.of_forall fun _ => rfl
  have hadd : 𝓕 (s • xf + (-s⁻¹) • df) w = (𝓕 (s • xf) + 𝓕 ((-s⁻¹) • df)) w :=
    congrFun (VectorFourier.fourierIntegral_add
      (e := 𝐞) (L := innerₗ ℝ) (by fun_prop) (by fun_prop) hsxf hinvdf) w
  rw [congrArg (fun g : ℝ → ℂ => 𝓕 g w) (twoPiHermiteFunction_succ_complex n),
    congrFun (fourier_const_smul _ (s • xf + (-s⁻¹) • df)) w, Pi.smul_apply, smul_eq_mul,
    hadd, Pi.add_apply, fourier_const_smul, fourier_const_smul, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]

private theorem fourier_twoPiHermiteFunction_succ (n : ℕ) (eigen : ℂ)
    (hfourier :
      𝓕 (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) =
        fun x => eigen * twoPiHermiteFunction n x) :
    𝓕 (fun x : ℝ => (twoPiHermiteFunction (n + 1) x : ℂ)) =
      fun x => (-Complex.I * eigen) * twoPiHermiteFunction (n + 1) x := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hermiteFourierScale_ne_zero
  have ha : (Real.sqrt (2 * ((n : ℝ) + 1)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hs_sq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * Real.pi := by
    rw [← Complex.ofReal_pow, hermiteFourierScale_sq]
    norm_num
  funext w
  -- Expand both sides by the raising relation, then substitute the transforms of the two
  -- creation-operator terms, which the eigenfunction hypothesis pins down.
  rw [fourier_twoPiHermiteFunction_succ_eq n w,
    fourier_mul_twoPiHermiteFunction_of_eigen n eigen hfourier,
    fourier_deriv_twoPiHermiteFunction_of_eigen n eigen hfourier,
    congrFun (twoPiHermiteFunction_succ_complex n) w]
  -- What is left is scalar, and turns on the normalization `√(2π)² = 2π`.
  rw [← hs_sq]
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  field_simp [ha, hs]
  ring_nf

/-- **Fourier eigenfunction theorem.** For Mathlib's `exp (-2πixξ)` convention, the rescaled
Hermite function `Φₙ(x) = √(√(2π)) ψₙ(√(2π)x)` has eigenvalue `(-i)ⁿ`. -/
theorem fourier_twoPiHermiteFunction (n : ℕ) :
    𝓕 (fun x : ℝ => (twoPiHermiteFunction n x : ℂ)) =
      fun x : ℝ => (-Complex.I) ^ n * twoPiHermiteFunction n x := by
  induction n with
  | zero =>
      simpa only [pow_zero, one_mul] using fourier_twoPiHermiteFunction_zero
  | succ n ih =>
      rw [pow_succ]
      simpa only [mul_comm ((-Complex.I) ^ n)] using
        fourier_twoPiHermiteFunction_succ n ((-Complex.I) ^ n) ih

end TauCeti
