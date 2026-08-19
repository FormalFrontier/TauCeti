/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.Basic
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# The Hermite functions diagonalize the Fourier transform of `L²(ℝ)`

`TauCeti.fourier_twoPiHermiteFunction` computes the Fourier *integral* of the rescaled Hermite
function `Φₙ(x) = √(√(2π)) ψₙ(√(2π)x)`, the family adapted to Mathlib's `e^{-2πixξ}` convention:
`𝓕 Φₙ = (-i)ⁿ Φₙ`. That is a statement about one function at a time. This file turns it into a
statement about the *operator*: `Φₙ` is a Hilbert basis of `L²(ℝ)`, and Mathlib's unitary Fourier
transform `MeasureTheory.Lp.fourierTransformₗᵢ` is diagonal in it, with eigenvalue `(-i)ⁿ` on the
`n`-th vector. Every `L²` function therefore has its Fourier transform given by the termwise
rescaling of its Hermite expansion, and the fourth iterate of the transform is the identity.

The basis is assembled by the roadmap's family-agnostic bridge
`TauCeti.hilbertBasisOfOrthogonalSystem`, exactly as `TauCeti.hermiteHilbertBasis` is, but at the
Fourier-adapted data: the weight `w(x) = e^{-2πx²}`, whose envelope `√w(x) = e^{-πx²}` is the
self-dual Gaussian of Mathlib's convention, the exact-degree polynomials `Hₙ(2√π·x)`, and the
normalization `cₙ = n!√π/√(2π)`. Completeness is the same moment-determinacy mechanism, since a
Gaussian weight of any width has finite exponential moments.

## Main statements

* `TauCeti.twoPiHermiteHilbertBasis` — the rescaled Hermite functions as a `HilbertBasis ℕ 𝕜` of
  `L²(ℝ)`, for every `RCLike` scalar field `𝕜`, with the element-level
  `TauCeti.coe_twoPiHermiteHilbertBasis`.
* `TauCeti.fourier_twoPiHermiteFunctionLp` — the eigenrelation `𝓕 Φₙ = (-i)ⁿ Φₙ` for the unitary
  Fourier transform of `L²(ℝ; ℂ)`.
* `TauCeti.hasSum_fourier_twoPiHermiteFunctionLp` — the diagonalization: the Fourier transform of
  an arbitrary `f ∈ L²(ℝ; ℂ)` is its Hermite expansion with the `n`-th coefficient multiplied
  by `(-i)ⁿ`; `TauCeti.repr_fourier_twoPiHermiteHilbertBasis` is the same fact read on the
  coefficients.
* `TauCeti.fourier_fourier_fourier_fourier` — the fourth iterate of the Fourier transform of
  `L²(ℝ; ℂ)` is the identity.

## References

* G. B. Folland, *Harmonic Analysis in Phase Space*, §1.
-/

public section

namespace TauCeti

open FourierTransform MeasureTheory Polynomial Real
open scoped SchwartzMap

private lemma twoPiScale_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.2 (by positivity)

private lemma twoPiScale_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 := twoPiScale_pos.ne'

private lemma twoPiScale_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
  Real.sq_sqrt (by positivity)

/-! ## The Fourier-adapted Hermite system -/

/-- The Hermite polynomial dilated to Mathlib's Fourier convention, `Hₙ(2√π · X)`. Its Gaussian
envelope `e^{-πx²}` is the self-dual Gaussian of the `e^{-2πixξ}` convention, so the resulting
`√w`-normalized functions are the `TauCeti.twoPiHermiteFunction`. -/
noncomputable def twoPiHermiteDilated (n : ℕ) : Polynomial ℝ :=
  (hermiteDilated n).comp (Polynomial.C (Real.sqrt (2 * Real.pi)) * Polynomial.X)

/-- Evaluating `TauCeti.twoPiHermiteDilated` is evaluating `TauCeti.hermiteDilated` at the
rescaled argument `√(2π)·x`. -/
theorem eval_twoPiHermiteDilated (n : ℕ) (x : ℝ) :
    (twoPiHermiteDilated n).eval x
      = (hermiteDilated n).eval (Real.sqrt (2 * Real.pi) * x) := by
  rw [twoPiHermiteDilated, eval_comp, eval_mul, eval_C, eval_X]

/-- The Fourier dilation preserves degrees, the input the completeness argument needs. -/
theorem degree_twoPiHermiteDilated (n : ℕ) :
    (twoPiHermiteDilated n).degree = (n : WithBot ℕ) := by
  have hq : (Polynomial.C (Real.sqrt (2 * Real.pi)) * Polynomial.X).degree = 1 :=
    Polynomial.degree_C_mul_X twoPiScale_ne_zero
  rw [twoPiHermiteDilated, Polynomial.degree_comp (by rw [hq]; norm_num), hq,
    degree_hermiteDilated, mul_one]

/-- The normalization `cₙ = n!√π/√(2π)` of the Fourier-adapted Hermite system: it is the Hermite
normalization `n!√π` divided by the Jacobian `√(2π)` of the dilation `u = √(2π)·x`. -/
noncomputable def twoPiHermiteNormalization (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * Real.sqrt Real.pi / Real.sqrt (2 * Real.pi)

/-- The Fourier-adapted normalization is positive, as the bridge requires. -/
theorem twoPiHermiteNormalization_pos (n : ℕ) : 0 < twoPiHermiteNormalization n :=
  div_pos (hermiteNormalization_pos n) twoPiScale_pos

private lemma sqrt_twoPiHermiteNormalization (n : ℕ) :
    Real.sqrt (twoPiHermiteNormalization n)
      = Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
        / Real.sqrt (Real.sqrt (2 * Real.pi)) := by
  rw [twoPiHermiteNormalization, Real.sqrt_div (hermiteNormalization_pos n).le]

/-- **The rescaled Hermite function is the `√w`-envelope of `Hₙ(2√π·x)`.** This is the identity
that makes the general bridge produce `TauCeti.twoPiHermiteFunction` rather than some other
normalization: `Φₙ(x) = Hₙ(2√π·x)·e^{-πx²}/√cₙ`. -/
theorem twoPiHermiteFunction_eq_eval_mul_exp (n : ℕ) (x : ℝ) :
    twoPiHermiteFunction n x
      = (twoPiHermiteDilated n).eval x * Real.exp (-(Real.pi * x ^ 2))
        / Real.sqrt (twoPiHermiteNormalization n) := by
  have hexp : Real.exp (-((Real.sqrt (2 * Real.pi) * x) ^ 2 / 2))
      = Real.exp (-(Real.pi * x ^ 2)) := by
    congr 1
    rw [mul_pow, twoPiScale_sq]
    ring
  have hnorm : Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
    sqrt_factorial_mul_sqrt_pi_ne_zero n
  have hscale : Real.sqrt (Real.sqrt (2 * Real.pi)) ≠ 0 :=
    (Real.sqrt_pos.2 twoPiScale_pos).ne'
  rw [twoPiHermiteFunction_def, hermiteFunction_def, eval_twoPiHermiteDilated,
    eval_hermiteDilated, hexp, sqrt_twoPiHermiteNormalization]
  field_simp

/-- **Orthonormality of the rescaled family.** The dilation `u = √(2π)·x` is unitary on `L²(ℝ)`
by construction of the outer factor `√(√(2π))`, so the rescaled Hermite functions inherit the
pointwise orthonormality of the `ψₙ`. -/
theorem integral_twoPiHermiteFunction_mul_twoPiHermiteFunction (m n : ℕ) :
    ∫ x : ℝ, twoPiHermiteFunction m x * twoPiHermiteFunction n x = if m = n then 1 else 0 := by
  have hfun : (fun x : ℝ => twoPiHermiteFunction m x * twoPiHermiteFunction n x)
      = fun x : ℝ => Real.sqrt (2 * Real.pi) *
          (hermiteFunction m (Real.sqrt (2 * Real.pi) * x)
            * hermiteFunction n (Real.sqrt (2 * Real.pi) * x)) := by
    funext x
    have hsq : Real.sqrt (Real.sqrt (2 * Real.pi)) * Real.sqrt (Real.sqrt (2 * Real.pi))
        = Real.sqrt (2 * Real.pi) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
    rw [twoPiHermiteFunction_def, twoPiHermiteFunction_def]
    linear_combination
      (hermiteFunction m (Real.sqrt (2 * Real.pi) * x)
        * hermiteFunction n (Real.sqrt (2 * Real.pi) * x)) * hsq
  -- The dilation contributes the Jacobian `√(2π)⁻¹`, which the outer factor `√(√(2π))²` cancels.
  have hcv := Measure.integral_comp_mul_left
    (fun y : ℝ => hermiteFunction m y * hermiteFunction n y) (Real.sqrt (2 * Real.pi))
  rw [hfun, integral_const_mul, hcv, integral_hermiteFunction_mul_hermiteFunction,
    abs_of_pos (inv_pos.2 twoPiScale_pos), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ twoPiScale_ne_zero, one_mul]

/-- **The orthogonality relation of the Fourier-adapted system.**
`∫ Hₘ(2√π·x)Hₙ(2√π·x)e^{-2πx²} = δₘₙ·cₙ` with `cₙ = n!√π/√(2π)`; this is the input the bridge
`TauCeti.hilbertBasisOfOrthogonalSystem` consumes. -/
theorem integral_twoPiHermiteDilated_mul_twoPiHermiteDilated_mul_gaussianWeight (m n : ℕ) :
    (∫ x : ℝ, (twoPiHermiteDilated m).eval x * (twoPiHermiteDilated n).eval x
        * Real.exp (-(2 * Real.pi * x ^ 2)))
      = if m = n then twoPiHermiteNormalization n else 0 := by
  have hpt : ∀ x : ℝ, (twoPiHermiteDilated m).eval x * (twoPiHermiteDilated n).eval x
      * Real.exp (-(2 * Real.pi * x ^ 2))
      = (Real.sqrt (twoPiHermiteNormalization m) * Real.sqrt (twoPiHermiteNormalization n))
        * (twoPiHermiteFunction m x * twoPiHermiteFunction n x) := by
    intro x
    have he : Real.exp (-(Real.pi * x ^ 2)) * Real.exp (-(Real.pi * x ^ 2))
        = Real.exp (-(2 * Real.pi * x ^ 2)) := by
      rw [← Real.exp_add]
      ring_nf
    have hm : Real.sqrt (twoPiHermiteNormalization m) ≠ 0 :=
      (Real.sqrt_pos.2 (twoPiHermiteNormalization_pos m)).ne'
    have hn : Real.sqrt (twoPiHermiteNormalization n) ≠ 0 :=
      (Real.sqrt_pos.2 (twoPiHermiteNormalization_pos n)).ne'
    rw [twoPiHermiteFunction_eq_eval_mul_exp, twoPiHermiteFunction_eq_eval_mul_exp, ← he]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, integral_twoPiHermiteFunction_mul_twoPiHermiteFunction]
  by_cases hmn : m = n
  · subst hmn
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one,
      Real.mul_self_sqrt (twoPiHermiteNormalization_pos m).le]
  · rw [ite_eq_right hmn, ite_eq_right hmn, mul_zero]

/-- The exponential-moment hypothesis of the completeness theorem, at the Gaussian weight
`e^{-2πx²}` of the Fourier-adapted system. -/
private theorem exp_moment_twoPiGaussianWeight :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-(2 * Real.pi * x ^ 2)))) :=
  ⟨1, one_pos, integrable_exp_mul_abs_gaussianWeight (by positivity) 1⟩

/-! ## `L²` packaging -/

/-- The rescaled Hermite functions lie in `L²(ℝ)`: they are the image of the `ψₙ` under a
dilation, which preserves square-integrability. -/
theorem memLp_two_twoPiHermiteFunction (n : ℕ) :
    MemLp (twoPiHermiteFunction n) 2 volume := by
  rw [memLp_two_iff_integrable_sq (continuous_twoPiHermiteFunction n).aestronglyMeasurable]
  have hsq : Integrable (fun y : ℝ => hermiteFunction n y ^ 2) volume := by
    rw [← memLp_two_iff_integrable_sq (continuous_hermiteFunction n).aestronglyMeasurable]
    exact memLp_two_hermiteFunction n
  have hdil := (hsq.comp_mul_left' twoPiScale_ne_zero).const_mul (Real.sqrt (2 * Real.pi))
  refine hdil.congr (Filter.Eventually.of_forall fun x => ?_)
  have hs : Real.sqrt (Real.sqrt (2 * Real.pi)) ^ 2 = Real.sqrt (2 * Real.pi) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  simp only [twoPiHermiteFunction_def, mul_pow, hs]

section Basis

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The scalar cast of a rescaled Hermite function lies in `L²(ℝ; 𝕜)`. -/
theorem memLp_two_algebraMap_twoPiHermiteFunction (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (twoPiHermiteFunction n x)) 2 volume := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_twoPiHermiteFunction n).ofReal (K := 𝕜)

/-- The `n`-th rescaled Hermite function as a vector of `L²(ℝ, volume; 𝕜)`. -/
noncomputable def twoPiHermiteFunctionLp (n : ℕ) : Lp 𝕜 2 (volume : Measure ℝ) :=
  (memLp_two_algebraMap_twoPiHermiteFunction (𝕜 := 𝕜) n).toLp _

/-- The `Lp` representative of `TauCeti.twoPiHermiteFunctionLp` is the scalar cast of the
pointwise rescaled Hermite function. -/
lemma coeFn_twoPiHermiteFunctionLp (n : ℕ) :
    ⇑(twoPiHermiteFunctionLp 𝕜 n) =ᵐ[volume]
      fun x : ℝ => (algebraMap ℝ 𝕜) (twoPiHermiteFunction n x) :=
  MemLp.coeFn_toLp _

/-- The `MemLp` obligation of the bridge for the Fourier-adapted family. -/
private theorem memLp_twoPiHermiteDilated_normalized (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((twoPiHermiteDilated n).eval x / Real.sqrt (twoPiHermiteNormalization n))) 2
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-(2 * Real.pi * x ^ 2)))) :=
  memLp_two_bareNormalized (𝕜 := 𝕜) exp_moment_twoPiGaussianWeight
    twoPiHermiteDilated twoPiHermiteNormalization n

/-- **The rescaled Hermite functions are a Hilbert basis of `L²(ℝ)`.** This is the roadmap's
Hermite basis in the normalization Mathlib's `e^{-2πixξ}` Fourier convention forces: the same
bridge `TauCeti.hilbertBasisOfOrthogonalSystem`, run at the weight `e^{-2πx²}` and the
polynomials `Hₙ(2√π·x)`. -/
noncomputable def twoPiHermiteHilbertBasis : HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume : Measure ℝ)) :=
  hilbertBasisOfOrthogonalSystem (𝕜 := 𝕜) (fun n x => (twoPiHermiteDilated n).eval x)
    (fun x => Real.exp (-(2 * Real.pi * x ^ 2))) twoPiHermiteNormalization
    (Filter.Eventually.of_forall fun x => Real.exp_pos _) (by fun_prop)
    twoPiHermiteNormalization_pos
    (fun m n => by
      simpa using integral_twoPiHermiteDilated_mul_twoPiHermiteDilated_mul_gaussianWeight m n)
    (memLp_twoPiHermiteDilated_normalized 𝕜)
    (orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) twoPiHermiteDilated
      (fun x => Real.exp (-(2 * Real.pi * x ^ 2))) twoPiHermiteNormalization
      degree_twoPiHermiteDilated twoPiHermiteNormalization_pos exp_moment_twoPiGaussianWeight
      (memLp_twoPiHermiteDilated_normalized 𝕜))

/-- **The basis vectors are the rescaled Hermite functions.** Without this the construction would
only exhibit *some* Hilbert basis of `L²(ℝ)`; here the `√w`-envelope of `Hₙ(2√π·x)/√cₙ` is
identified with `Φₙ`. -/
@[simp]
theorem coe_twoPiHermiteHilbertBasis :
    ⇑(twoPiHermiteHilbertBasis 𝕜) = twoPiHermiteFunctionLp 𝕜 := by
  funext n
  rw [twoPiHermiteHilbertBasis]
  refine Lp.ext ((coeFn_hilbertBasisOfOrthogonalSystem _ _ _ _ _ _ _ _ _ n).trans ?_)
  filter_upwards [coeFn_twoPiHermiteFunctionLp (𝕜 := 𝕜) n] with x hx
  -- `√w` is the self-dual Gaussian: `√(e^{-2πx²}) = e^{-πx²}`.
  have hsplit : (-(2 * Real.pi * x ^ 2) : ℝ)
      = -(Real.pi * x ^ 2) + -(Real.pi * x ^ 2) := by ring
  have hs : Real.sqrt (Real.exp (-(2 * Real.pi * x ^ 2))) = Real.exp (-(Real.pi * x ^ 2)) := by
    rw [hsplit, Real.exp_add]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  rw [hx, twoPiHermiteFunction_eq_eval_mul_exp, hs]

/-- The rescaled Hermite functions are orthonormal in `L²(ℝ; 𝕜)`. -/
theorem orthonormal_twoPiHermiteFunctionLp : Orthonormal 𝕜 (twoPiHermiteFunctionLp 𝕜) := by
  simpa using (twoPiHermiteHilbertBasis 𝕜).orthonormal

end Basis

/-! ## Diagonalization of the Fourier transform -/

/-- The `n`-th rescaled Hermite function as a complex Schwartz function. It is built from
`TauCeti.hermiteSchwartzMap` by the linear dilation `x ↦ √(2π)·x` and the inclusion `ℝ → ℂ`, both
continuous linear operations on Schwartz space; this is what lets Mathlib's
`SchwartzMap.toLp_fourier_eq` transfer the pointwise Fourier eigenrelation to `L²`. -/
noncomputable def twoPiHermiteSchwartzMap (n : ℕ) : 𝓢(ℝ, ℂ) :=
  Real.sqrt (Real.sqrt (2 * Real.pi)) •
    SchwartzMap.postcompCLM Complex.ofRealCLM
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (ContinuousLinearEquiv.unitsEquivAut ℝ
          (Units.mk0 (Real.sqrt (2 * Real.pi)) twoPiScale_ne_zero))
        (hermiteSchwartzMap n))

/-- The underlying function of `TauCeti.twoPiHermiteSchwartzMap` is the rescaled Hermite
function. -/
@[simp]
theorem twoPiHermiteSchwartzMap_apply (n : ℕ) (x : ℝ) :
    twoPiHermiteSchwartzMap n x = (twoPiHermiteFunction n x : ℂ) := by
  have hx : (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (ContinuousLinearEquiv.unitsEquivAut ℝ
          (Units.mk0 (Real.sqrt (2 * Real.pi)) twoPiScale_ne_zero))
        (hermiteSchwartzMap n)) x
      = hermiteFunction n (Real.sqrt (2 * Real.pi) * x) := by
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, hermiteSchwartzMap_apply,
      mul_comm]
  rw [twoPiHermiteSchwartzMap, smul_apply, SchwartzMap.postcompCLM_apply, hx,
    twoPiHermiteFunction_def]
  simp [Complex.real_smul]

/-- The coercion of `TauCeti.twoPiHermiteSchwartzMap` is the complexified rescaled Hermite
function. -/
@[simp]
theorem coe_twoPiHermiteSchwartzMap (n : ℕ) :
    ⇑(twoPiHermiteSchwartzMap n) = fun x : ℝ => (twoPiHermiteFunction n x : ℂ) :=
  funext (twoPiHermiteSchwartzMap_apply n)

/-- The Schwartz function and the `L²` vector describe the same element of `L²(ℝ; ℂ)`. -/
theorem toLp_twoPiHermiteSchwartzMap (n : ℕ) :
    (twoPiHermiteSchwartzMap n).toLp 2 = twoPiHermiteFunctionLp ℂ n := by
  refine Lp.ext ?_
  filter_upwards [(twoPiHermiteSchwartzMap n).coeFn_toLp 2 volume,
    coeFn_twoPiHermiteFunctionLp (𝕜 := ℂ) n] with x hx hy
  rw [hx, hy, twoPiHermiteSchwartzMap_apply]
  simp

/-- **The Fourier eigenrelation in Schwartz space.** This is the pointwise
`TauCeti.fourier_twoPiHermiteFunction` read as an identity between Schwartz functions. -/
@[simp]
theorem fourier_twoPiHermiteSchwartzMap (n : ℕ) :
    𝓕 (twoPiHermiteSchwartzMap n) = (-Complex.I) ^ n • twoPiHermiteSchwartzMap n := by
  refine SchwartzMap.ext fun x => ?_
  have h := congrFun (fourier_twoPiHermiteFunction n) x
  calc (𝓕 (twoPiHermiteSchwartzMap n)) x
      = 𝓕 (⇑(twoPiHermiteSchwartzMap n)) x := by rw [SchwartzMap.fourier_coe]
    _ = 𝓕 (fun y : ℝ => (twoPiHermiteFunction n y : ℂ)) x := by
        rw [coe_twoPiHermiteSchwartzMap]
    _ = (-Complex.I) ^ n * twoPiHermiteFunction n x := h
    _ = ((-Complex.I) ^ n • twoPiHermiteSchwartzMap n) x := by
        rw [smul_apply, twoPiHermiteSchwartzMap_apply, smul_eq_mul]

/-- **The Fourier eigenrelation for the unitary Fourier transform of `L²(ℝ; ℂ)`.** The `n`-th
rescaled Hermite function is an eigenvector of `MeasureTheory.Lp.fourierTransformₗᵢ` with
eigenvalue `(-i)ⁿ`. -/
@[simp]
theorem fourier_twoPiHermiteFunctionLp (n : ℕ) :
    𝓕 (twoPiHermiteFunctionLp ℂ n) = (-Complex.I) ^ n • twoPiHermiteFunctionLp ℂ n := by
  rw [← toLp_twoPiHermiteSchwartzMap, SchwartzMap.toLp_fourier_eq,
    fourier_twoPiHermiteSchwartzMap, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ),
    map_smul, SchwartzMap.toLpCLM_apply]

/-- The inverse Fourier transform of `L²(ℝ; ℂ)` acts on the same eigenvectors with the conjugate
eigenvalue `iⁿ`. -/
@[simp]
theorem fourierInv_twoPiHermiteFunctionLp (n : ℕ) :
    𝓕⁻ (twoPiHermiteFunctionLp ℂ n) = Complex.I ^ n • twoPiHermiteFunctionLp ℂ n := by
  have hmul : Complex.I ^ n * (-Complex.I) ^ n = 1 := by
    rw [← mul_pow]
    simp [Complex.I_mul_I]
  have h : (𝓕⁻ (𝓕 (twoPiHermiteFunctionLp ℂ n)) : Lp ℂ 2 (volume : Measure ℝ))
      = twoPiHermiteFunctionLp ℂ n := fourierInv_fourier_eq _
  rw [fourier_twoPiHermiteFunctionLp, fourierInv_smul] at h
  calc 𝓕⁻ (twoPiHermiteFunctionLp ℂ n)
      = Complex.I ^ n • ((-Complex.I) ^ n • 𝓕⁻ (twoPiHermiteFunctionLp ℂ n)) := by
        rw [smul_smul, hmul, one_smul]
    _ = Complex.I ^ n • twoPiHermiteFunctionLp ℂ n := by rw [h]

/-- **Diagonalization.** The Fourier transform of an arbitrary `f ∈ L²(ℝ; ℂ)` is its expansion in
the rescaled Hermite basis with the `n`-th coefficient multiplied by `(-i)ⁿ`. -/
theorem hasSum_fourier_twoPiHermiteFunctionLp (f : Lp ℂ 2 (volume : Measure ℝ)) :
    HasSum (fun n : ℕ => ((-Complex.I) ^ n * (twoPiHermiteHilbertBasis ℂ).repr f n) •
      twoPiHermiteFunctionLp ℂ n) (𝓕 f) := by
  have h := ContinuousLinearMap.hasSum (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    ((twoPiHermiteHilbertBasis ℂ).hasSum_repr f)
  simp only [fourierCLM_apply, fourier_smul, coe_twoPiHermiteHilbertBasis,
    fourier_twoPiHermiteFunctionLp, smul_smul] at h
  have heq : (fun n : ℕ => ((-Complex.I) ^ n * (twoPiHermiteHilbertBasis ℂ).repr f n) •
      twoPiHermiteFunctionLp ℂ n)
      = fun n : ℕ => ((twoPiHermiteHilbertBasis ℂ).repr f n * (-Complex.I) ^ n) •
        twoPiHermiteFunctionLp ℂ n := by
    funext n
    rw [mul_comm]
  rw [heq]
  exact h

/-- **Diagonalization, coefficient form.** Passing to the Fourier transform multiplies the `n`-th
Hermite coefficient by `(-i)ⁿ`. This is the statement that the matrix of the Fourier transform in
the rescaled Hermite basis is the diagonal matrix `diag((-i)ⁿ)`. -/
@[simp]
theorem repr_fourier_twoPiHermiteHilbertBasis (f : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    (twoPiHermiteHilbertBasis ℂ).repr (𝓕 f) n
      = (-Complex.I) ^ n * (twoPiHermiteHilbertBasis ℂ).repr f n := by
  have hmul : Complex.I ^ n * (-Complex.I) ^ n = 1 := by
    rw [← mul_pow]
    simp [Complex.I_mul_I]
  -- Unitarity of the transform turns the pairing against `Φₙ` into the pairing against `𝓕 Φₙ`.
  have hinner := MeasureTheory.Lp.inner_fourier_eq (twoPiHermiteFunctionLp ℂ n) f
  rw [fourier_twoPiHermiteFunctionLp, inner_smul_left, map_pow, map_neg, Complex.conj_I,
    neg_neg] at hinner
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    coe_twoPiHermiteHilbertBasis, ← hinner, ← mul_assoc, mul_comm ((-Complex.I) ^ n),
    hmul, one_mul]

/-- **The fourth iterate of the Fourier transform of `L²(ℝ; ℂ)` is the identity.** Each eigenvalue
`(-i)ⁿ` is a fourth root of unity, so the fourth iterate fixes every basis vector, hence all of
`L²(ℝ)`. -/
@[simp]
theorem fourier_fourier_fourier_fourier (f : Lp ℂ 2 (volume : Measure ℝ)) :
    𝓕 (𝓕 (𝓕 (𝓕 f))) = f := by
  have hI : (-Complex.I) ^ 4 = 1 := by
    have h2 : (-Complex.I) ^ 2 = -1 := by
      rw [neg_pow]
      simp [Complex.I_sq]
    have hfour : (4 : ℕ) = 2 * 2 := by norm_num
    rw [hfour, pow_mul, h2]
    norm_num
  have hstep : ∀ (a : ℂ) (n : ℕ), 𝓕 (a • twoPiHermiteFunctionLp ℂ n)
      = (a * (-Complex.I) ^ n) • twoPiHermiteFunctionLp ℂ n := by
    intro a n
    rw [fourier_smul, fourier_twoPiHermiteFunctionLp, smul_smul]
  have hbasis : ∀ n : ℕ, 𝓕 (𝓕 (𝓕 (𝓕 (twoPiHermiteFunctionLp ℂ n))))
      = twoPiHermiteFunctionLp ℂ n := by
    intro n
    have hpow : (-Complex.I) ^ n * (-Complex.I) ^ n * (-Complex.I) ^ n * (-Complex.I) ^ n = 1 := by
      have hadd : n + n + n + n = 4 * n := by omega
      rw [← pow_add, ← pow_add, ← pow_add, hadd, pow_mul, hI, one_pow]
    calc 𝓕 (𝓕 (𝓕 (𝓕 (twoPiHermiteFunctionLp ℂ n))))
        = 𝓕 (𝓕 (𝓕 ((-Complex.I) ^ n • twoPiHermiteFunctionLp ℂ n))) := by
          rw [fourier_twoPiHermiteFunctionLp]
      _ = 𝓕 (𝓕 (((-Complex.I) ^ n * (-Complex.I) ^ n) • twoPiHermiteFunctionLp ℂ n)) := by
          rw [hstep]
      _ = 𝓕 (((-Complex.I) ^ n * (-Complex.I) ^ n * (-Complex.I) ^ n) •
            twoPiHermiteFunctionLp ℂ n) := by rw [hstep]
      _ = ((-Complex.I) ^ n * (-Complex.I) ^ n * (-Complex.I) ^ n * (-Complex.I) ^ n) •
            twoPiHermiteFunctionLp ℂ n := by rw [hstep]
      _ = twoPiHermiteFunctionLp ℂ n := by rw [hpow, one_smul]
  have hsum := ContinuousLinearMap.hasSum (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (ContinuousLinearMap.hasSum (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      (ContinuousLinearMap.hasSum (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ)))
        (ContinuousLinearMap.hasSum (fourierCLM ℂ (Lp ℂ 2 (volume : Measure ℝ)))
          ((twoPiHermiteHilbertBasis ℂ).hasSum_repr f))))
  simp only [fourierCLM_apply, fourier_smul, coe_twoPiHermiteHilbertBasis, hbasis] at hsum
  exact hsum.unique (by simpa using (twoPiHermiteHilbertBasis ℂ).hasSum_repr f)

end TauCeti
