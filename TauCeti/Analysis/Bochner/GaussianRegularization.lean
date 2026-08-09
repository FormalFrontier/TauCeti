/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
-- The remaining imports are proof-only: Fourier inversion and the Gaussian Fourier transform,
-- negation invariance of Haar measure, the `withDensity` Bochner-integral formula, the
-- nonnegativity of the Fourier transform of a positive-definite function, the Gaussian kernel,
-- and the kernel Cauchy–Schwarz bound.
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Bochner.FourierNonneg
import TauCeti.Analysis.Bochner.Gaussian
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Gaussian regularization of positive-definite functions

The Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)` of a positive-definite function `φ` on a
finite-dimensional real inner-product space is again positive definite (a Schur product with the
Gaussian kernel), integrable, and converges to `φ` pointwise as `ε → 0⁺`. This is the
approximation device of the second step of Bochner's theorem: it replaces a merely bounded
positive-definite function by an integrable one to which Fourier inversion applies.

The analytic payoff recorded here is twofold. First, the Fourier transform of *any* continuous
integrable function with positive-definite subtraction kernel is itself integrable: testing
against a shrinking family of Gaussians and using the Parseval/Fubini identity bounds
`∫ (𝓕 F) · exp (-t‖·‖²)` by `(F 0).re` uniformly in `t`, and Fatou's lemma passes to the limit.
In particular this applies to every Gaussian regularization. Second, for such a function the
finite measure with density `(𝓕⁻ F).re` against Lebesgue measure recovers `F` as the
Fourier-convention transform `∫ q, fourierAtom · q` of the measure, by Fourier inversion. This
is the L¹ case of Bochner's theorem, with the representing measure given explicitly.

Adapted from the Bochner–Minlos formalization (`Bochner/Main.lean` in our bochner project);
the positive-definiteness hypotheses are restated through `TauCeti.IsPositiveDefiniteKernel`,
and the recovered identity is stated in the `fourierAtom` convention rather than through
`MeasureTheory.charFun`, which removes the `2π`-rescaling of the source.

## Main declarations

* `TauCeti.gaussianRegularize`: the Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)`.
* `TauCeti.isPositiveDefiniteKernel_gaussianRegularize`: `φ_ε` has a positive-definite
  subtraction kernel whenever `φ` does.
* `TauCeti.continuous_gaussianRegularize`, `TauCeti.integrable_gaussianRegularize`,
  `TauCeti.gaussianRegularize_zero`, `TauCeti.tendsto_gaussianRegularize`: the basic analytic
  facts about `φ_ε`.
* `TauCeti.integrable_fourierIntegral_of_isPositiveDefiniteKernel`: the Fourier transform of a
  continuous integrable positive-definite function is integrable.
* `TauCeti.integrable_fourierIntegral_gaussianRegularize`: the specialization to `φ_ε`.
* `TauCeti.isFiniteMeasure_withDensity_re_fourierIntegralInv` and
  `TauCeti.integral_fourierAtom_withDensity_re_fourierIntegralInv`: the measure
  `volume.withDensity (ENNReal.ofReal (𝓕⁻ F ·).re)` is finite and recovers `F` through the
  Fourier atom.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), §1.4.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti

/-! ### The Gaussian regularization and its elementary properties -/

section Regularize

variable {V : Type*} [NormedAddCommGroup V]

/-- The Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)` of a function `φ`. For `ε > 0` it
decays like a Gaussian, and as `ε → 0⁺` it recovers `φ` pointwise. -/
noncomputable def gaussianRegularize (φ : V → ℂ) (ε : ℝ) : V → ℂ :=
  fun x => φ x * Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ))

/-- The defining formula of the Gaussian regularization. -/
@[simp]
theorem gaussianRegularize_apply (φ : V → ℂ) (ε : ℝ) (x : V) :
    gaussianRegularize φ ε x = φ x * Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) := by
  simp [gaussianRegularize]

/-- The Gaussian regularization agrees with `φ` at the origin. -/
theorem gaussianRegularize_zero (φ : V → ℂ) (ε : ℝ) : gaussianRegularize φ ε 0 = φ 0 := by
  simp

/-- The Gaussian regularization is continuous when `φ` is. -/
theorem continuous_gaussianRegularize {φ : V → ℂ} (hcont : Continuous φ) (ε : ℝ) :
    Continuous (gaussianRegularize φ ε) :=
  hcont.mul (continuous_cexp_neg_mul_sq_norm ε)

/-- The Gaussian regularization converges to `φ` pointwise as `ε → 0⁺`. -/
theorem tendsto_gaussianRegularize (φ : V → ℂ) (x : V) :
    Tendsto (fun ε : ℝ => gaussianRegularize φ ε x) (𝓝[>] 0) (𝓝 (φ x)) := by
  have hc : Continuous fun ε : ℝ => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) := by fun_prop
  have h1 : Tendsto (fun ε : ℝ => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ))) (𝓝 0) (𝓝 1) := by
    simpa using hc.tendsto 0
  simpa using tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds h1)

end Regularize

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Fourier-analytic helper lemmas -/

/-- The Fourier transform of an integrable function is continuous. -/
private theorem continuous_fourierIntegral (f : V → ℂ) (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (show Continuous fun p : V × V => (innerₗ V) p.1 p.2 from continuous_inner) hf

/-- The `L¹` Parseval/Fubini identity `∫ (𝓕 f) · g = ∫ f · (𝓕 g)`, the self-adjointness of the
Fourier transform for the symmetric inner-product pairing. -/
private theorem integral_fourierIntegral_mul (f g : V → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
    Real.continuous_fourierChar
    (show Continuous fun p : V × V => (innerₗ V) p.1 p.2 from continuous_inner) hf hg
  have hL : ∀ (f : V → ℂ) (ξ : V),
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f ξ = 𝓕 f ξ := fun f ξ => rfl
  simp only [flip_innerₗ, smul_eq_mul, hL] at h
  exact h

/-! ### Gaussian Fourier facts -/

/-- The Gaussian `x ↦ exp (-t‖x‖²)` is integrable for `t > 0`. -/
private theorem integrable_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
    (show 0 < ((t : ℂ)).re by simpa using ht) 0 (0 : V)
  simp only [zero_mul, add_zero] at h
  refine h.congr (ae_of_all _ fun x => ?_)
  push_cast
  ring_nf

/-- The Fourier transform of a Gaussian is integrable (it is again a Gaussian). -/
private theorem integrable_fourierIntegral_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable (𝓕 fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) := by
  have htre : 0 < ((t : ℂ)).re := by simpa using ht
  have heq : (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)))
      = fun v : V => Complex.exp (-(t : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v
    push_cast
    ring_nf
  rw [heq, funext fun w : V => fourier_gaussian_innerProductSpace htre w]
  refine Integrable.const_mul ?_ _
  have hint : Integrable fun w : V => Complex.exp (-(Real.pi ^ 2 / t * ‖w‖ ^ 2 : ℝ)) :=
    integrable_gaussian (by positivity)
  refine hint.congr (ae_of_all _ fun w => ?_)
  push_cast
  ring_nf

/-- The Fourier transform of a Gaussian integrates to `1`, by Fourier inversion at `0`. -/
private theorem integral_fourierIntegral_gaussian_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ ξ : V, 𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ = 1 := by
  have hg_int : Integrable fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    integrable_gaussian ht
  have hg_cont : Continuous fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    continuous_cexp_neg_mul_sq_norm t
  have hft_int := integrable_fourierIntegral_gaussian (V := V) ht
  have h0 := congrFun (hg_cont.fourierInv_fourier_eq hg_int hft_int) 0
  rw [Real.fourierInv_eq] at h0
  simpa using h0

/-- The `L¹` norm of the Fourier transform of a Gaussian is `1`: the transform is real and
nonnegative because the Gaussian has a positive-definite subtraction kernel. -/
private theorem integral_norm_fourierIntegral_gaussian_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖ = 1 := by
  have hg_pd : IsPositiveDefiniteKernel
      fun a b : V => Complex.exp (-(t * ‖a - b‖ ^ 2 : ℝ)) :=
    isPositiveDefiniteKernel_cexp_neg_mul_sq_norm ht.le
  have hg_int : Integrable fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    integrable_gaussian ht
  have hg_cont : Continuous fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    continuous_cexp_neg_mul_sq_norm t
  have hft_int := integrable_fourierIntegral_gaussian (V := V) ht
  have hnorm : ∀ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖ =
      (𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re := by
    intro ξ
    have hre := fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel _ hg_pd hg_int hg_cont ξ
    rw [fourierIntegral_eq_re_of_isPositiveDefiniteKernel _ hg_pd ξ, Complex.norm_real,
      Complex.ofReal_re, Real.norm_of_nonneg hre]
  calc ∫ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖
      = ∫ ξ : V, (𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re :=
        integral_congr_ae (ae_of_all _ hnorm)
    _ = (∫ ξ : V, 𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re := by
        simpa only [RCLike.re_to_complex] using integral_re hft_int
    _ = 1 := by rw [integral_fourierIntegral_gaussian_eq_one ht, Complex.one_re]

/-! ### Positive definiteness and integrability of the regularization -/

/-- The Gaussian regularization of a function with positive-definite subtraction kernel again
has a positive-definite subtraction kernel: it is the Schur product of the original kernel with
the Gaussian kernel `(a, b) ↦ exp (-ε‖a - b‖²)`. -/
theorem isPositiveDefiniteKernel_gaussianRegularize {φ : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => φ (a - b)) {ε : ℝ} (hε : 0 ≤ ε) :
    IsPositiveDefiniteKernel fun a b : V => gaussianRegularize φ ε (a - b) :=
  isPositiveDefiniteKernel_mul hpd (isPositiveDefiniteKernel_cexp_neg_mul_sq_norm hε)

/-- The Gaussian regularization of a continuous function with positive-definite subtraction
kernel is integrable for every `ε > 0`: the function is bounded by `(φ 0).re` and the Gaussian
factor is integrable. -/
theorem integrable_gaussianRegularize {φ : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => φ (a - b))
    (hcont : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianRegularize φ ε) := by
  have hgauss : Integrable fun x : V => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) :=
    integrable_gaussian hε
  refine (hgauss.norm.const_mul (φ 0).re).mono
    ((hcont.mul (continuous_cexp_neg_mul_sq_norm ε)).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp only [gaussianRegularize_apply, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (re_map_zero_nonneg_of_isPositiveDefiniteKernel hpd), abs_norm]
  exact mul_le_mul_of_nonneg_right
    (norm_le_re_map_zero_of_isPositiveDefiniteKernel hpd x) (norm_nonneg _)

/-! ### Integrability of the Fourier transform of a positive-definite function -/

/-- For a continuous integrable positive-definite `F` and `t > 0`, the Gaussian-tested integral
of `𝓕 F` is at most `(F 0).re`, by the Parseval/Fubini identity and the `L¹` bound on the
Fourier transform of the Gaussian. -/
private theorem re_integral_fourierIntegral_mul_gaussian_le (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) {t : ℝ} (ht : 0 < t) :
    (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re ≤ (F 0).re := by
  have hgt_int : Integrable fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)) :=
    integrable_gaussian ht
  have hft_gt_int := integrable_fourierIntegral_gaussian (V := V) ht
  have hFbound : ∀ x, ‖F x‖ ≤ (F 0).re := norm_le_re_map_zero_of_isPositiveDefiniteKernel hpd
  have hprod_int : Integrable fun x : V =>
      F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x :=
    hft_gt_int.bdd_mul hcont.aestronglyMeasurable (ae_of_all _ hFbound)
  have hpars : (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) =
      ∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x :=
    integral_fourierIntegral_mul F _ hint hgt_int
  rw [hpars]
  calc (∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x).re
      ≤ ‖∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ x, ‖F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, (F 0).re * ‖𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ := by
        refine integral_mono hprod_int.norm ((hft_gt_int.norm).const_mul _) fun x => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hFbound x) (norm_nonneg _)
    _ = (F 0).re * ∫ x, ‖𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        integral_const_mul _ _
    _ = (F 0).re := by rw [integral_norm_fourierIntegral_gaussian_eq_one ht, mul_one]

/-- The Gaussian-damped lower integral of `‖𝓕 F‖ₑ` is bounded by `(F 0).re`, uniformly in the
damping parameter: the damped transform is real and nonnegative, so its `L¹` norm equals the
Gaussian-tested integral bounded by `re_integral_fourierIntegral_mul_gaussian_le`. -/
private theorem lintegral_enorm_fourierIntegral_mul_gaussian_le (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ξ, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖ₑ ≤ ENNReal.ofReal (F 0).re := by
  have hbound : ∀ ξ : V, ‖𝓕 F ξ‖ ≤ ∫ x, ‖F x‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ V) F ξ
  have hft_cont : Continuous (𝓕 F) := continuous_fourierIntegral F hint
  have hprod_int : Integrable fun ξ : V => 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)) :=
    (integrable_gaussian ht).bdd_mul hft_cont.aestronglyMeasurable
      (ae_of_all _ fun ξ => hbound ξ)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hprod_int]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm_eq : ∀ ξ : V, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖ =
      (𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re := by
    intro ξ
    rw [fourierIntegral_eq_re_of_isPositiveDefiniteKernel F hpd ξ, ← Complex.ofReal_neg,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.norm_real, Complex.ofReal_re,
      Real.norm_of_nonneg (mul_nonneg
        (fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel F hpd hint hcont ξ)
        (Real.exp_nonneg _))]
  calc ∫ ξ, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖
      = ∫ ξ, (𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re :=
        integral_congr_ae (ae_of_all _ hnorm_eq)
    _ = (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re := by
        simpa only [RCLike.re_to_complex] using integral_re hprod_int
    _ ≤ (F 0).re := re_integral_fourierIntegral_mul_gaussian_le F hpd hint hcont ht

/-- The Fourier transform of a continuous integrable positive-definite function is integrable.

Testing `𝓕 F` against the Gaussians `exp (-‖·‖²/(n+1))` gives integrals uniformly bounded by
`(F 0).re`, and Fatou's lemma passes the bound to `∫⁻ ‖𝓕 F‖ₑ`. Folland, *A Course in Abstract
Harmonic Analysis*, §4.2. -/
theorem integrable_fourierIntegral_of_isPositiveDefiniteKernel (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) :
    Integrable (𝓕 F) := by
  have hft_cont : Continuous (𝓕 F) := continuous_fourierIntegral F hint
  set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with htn_def
  have htn_pos : ∀ n, 0 < tn n := fun n => by positivity
  have htn_lim : Tendsto tn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hf_meas : ∀ n : ℕ, Measurable fun ξ : V =>
      ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ := fun n =>
    ((hft_cont.mul (continuous_cexp_neg_mul_sq_norm (tn n))).measurable).enorm
  have hf_tendsto : ∀ ξ : V, Tendsto
      (fun n : ℕ => ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ)
      atTop (𝓝 ‖𝓕 F ξ‖ₑ) := by
    intro ξ
    have hc : Continuous fun s : ℝ => Complex.exp (-(s * ‖ξ‖ ^ 2 : ℝ)) := by fun_prop
    have h1 : Tendsto (fun s : ℝ => Complex.exp (-(s * ‖ξ‖ ^ 2 : ℝ))) (𝓝 0) (𝓝 1) := by
      simpa using hc.tendsto 0
    have h2 : Tendsto (fun n : ℕ => Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))) atTop (𝓝 1) :=
      h1.comp htn_lim
    have h3 : Tendsto (fun n : ℕ => 𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ)))
        atTop (𝓝 (𝓕 F ξ)) := by
      simpa using tendsto_const_nhds.mul h2
    exact h3.enorm
  have hbound : ∫⁻ ξ, ‖𝓕 F ξ‖ₑ ≤ ENNReal.ofReal (F 0).re := by
    calc ∫⁻ ξ, ‖𝓕 F ξ‖ₑ
        = ∫⁻ ξ, liminf
            (fun n : ℕ => ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ) atTop :=
          lintegral_congr fun ξ => ((hf_tendsto ξ).liminf_eq).symm
      _ ≤ liminf
            (fun n : ℕ => ∫⁻ ξ, ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ) atTop :=
          lintegral_liminf_le hf_meas
      _ ≤ ENNReal.ofReal (F 0).re := by
          apply liminf_le_of_le (h := fun b hb => ?_)
          obtain ⟨n, hn⟩ := hb.exists
          exact hn.trans
            (lintegral_enorm_fourierIntegral_mul_gaussian_le F hpd hint hcont (htn_pos n))
  exact ⟨hft_cont.aestronglyMeasurable, hbound.trans_lt ENNReal.ofReal_lt_top⟩

/-- The Fourier transform of a Gaussian regularization of a continuous positive-definite
function is integrable, for every `ε > 0`. -/
theorem integrable_fourierIntegral_gaussianRegularize {φ : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => φ (a - b))
    (hcont : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (𝓕 (gaussianRegularize φ ε)) :=
  integrable_fourierIntegral_of_isPositiveDefiniteKernel _
    (isPositiveDefiniteKernel_gaussianRegularize hpd hε.le)
    (integrable_gaussianRegularize hpd hcont hε)
    (continuous_gaussianRegularize hcont ε)

/-! ### The representing measure of an integrable positive-definite function -/

/-- The measure with density `(𝓕⁻ F).re` against Lebesgue measure is finite whenever `𝓕 F` is
integrable. This is the total-mass half of the `L¹` case of Bochner's theorem. -/
theorem isFiniteMeasure_withDensity_re_fourierIntegralInv (F : V → ℂ)
    (hint_ft : Integrable (𝓕 F)) :
    IsFiniteMeasure (volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ F ξ).re) := by
  have hinv_int : Integrable (𝓕⁻ F) := by
    rw [show 𝓕⁻ F = fun ξ : V => 𝓕 F (-ξ) from
      funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
    exact hint_ft.comp_neg
  exact isFiniteMeasure_withDensity_ofReal hinv_int.re.2

/-- **Bochner recovery for `L¹` positive-definite functions.** A continuous integrable function
`F` with positive-definite subtraction kernel is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of the finite measure `μ` with density `(𝓕⁻ F).re` against
Lebesgue measure. The identity is Fourier inversion `𝓕 (𝓕⁻ F) = F`, using that `𝓕⁻ F` is real
and nonnegative. Rudin, *Fourier Analysis on Groups*, §1.4; Folland, §4.2. -/
theorem integral_fourierAtom_withDensity_re_fourierIntegralInv (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (v : V) :
    ∫ q, fourierAtom v q ∂(volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ F ξ).re) = F v := by
  have hft_int : Integrable (𝓕 F) :=
    integrable_fourierIntegral_of_isPositiveDefiniteKernel F hpd hint hcont
  have hinv_cont : Continuous (𝓕⁻ F) := by
    rw [show 𝓕⁻ F = fun ξ : V => 𝓕 F (-ξ) from
      funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
    exact (continuous_fourierIntegral F hint).comp continuous_neg
  have hre : ∀ ξ, 0 ≤ (𝓕⁻ F ξ).re := fun ξ => by
    rw [Real.fourierInv_eq_fourier_neg]
    exact fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel F hpd hint hcont (-ξ)
  have hreal : ∀ ξ, 𝓕⁻ F ξ = ((𝓕⁻ F ξ).re : ℂ) := fun ξ => by
    rw [Real.fourierInv_eq_fourier_neg]
    exact fourierIntegral_eq_re_of_isPositiveDefiniteKernel F hpd (-ξ)
  have hmeas : Measurable fun ξ : V => ENNReal.ofReal (𝓕⁻ F ξ).re :=
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hinv_cont.measurable)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas.aemeasurable
    (ae_of_all _ fun ξ => ENNReal.ofReal_lt_top) _]
  calc ∫ q, (ENNReal.ofReal (𝓕⁻ F q).re).toReal • fourierAtom v q
      = ∫ q, fourierAtom v q * 𝓕⁻ F q := by
        refine integral_congr_ae (ae_of_all _ fun q => ?_)
        change (ENNReal.ofReal (𝓕⁻ F q).re).toReal • fourierAtom v q = fourierAtom v q * 𝓕⁻ F q
        rw [ENNReal.toReal_ofReal (hre q), Complex.real_smul, ← hreal q, mul_comm]
    _ = 𝓕 (𝓕⁻ F) v := (fourierIntegral_eq_integral_fourierAtom_mul (𝓕⁻ F) v).symm
    _ = F v := by rw [hcont.fourier_fourierInv_eq hint hft_int]

end TauCeti
