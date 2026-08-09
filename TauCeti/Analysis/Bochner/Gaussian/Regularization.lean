/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic
-- The remaining imports are proof-only: the integrability of the Fourier transform of a
-- positive-definite function, the Gaussian kernel, and the kernel Cauchy–Schwarz bounds.
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Bochner.Gaussian.Basic
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Gaussian regularization of positive-definite functions

The Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)` of a positive-definite function `φ` on a
finite-dimensional real inner-product space is again positive definite (a Schur product with the
Gaussian kernel), integrable, and converges to `φ` pointwise as `ε → 0`. This is the
approximation device of the second step of Bochner's theorem: it replaces a merely bounded
positive-definite function by an integrable one to which Fourier inversion applies. Its Fourier
transform is integrable by `integrable_fourierIntegral_of_isPositiveDefiniteKernel`.

Adapted from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source file `Bochner/Main.lean`;
the positive-definiteness hypotheses are restated through `TauCeti.IsPositiveDefiniteKernel`.

## Main declarations

* `TauCeti.gaussianRegularize`: the Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)`.
* `TauCeti.isPositiveDefiniteKernel_gaussianRegularize`: `φ_ε` has a positive-definite
  subtraction kernel whenever `φ` does.
* `TauCeti.continuous_gaussianRegularize`, `TauCeti.integrable_gaussianRegularize`,
  `TauCeti.tendsto_gaussianRegularize`: the basic analytic facts about `φ_ε`.
* `TauCeti.integrable_fourierIntegral_gaussianRegularize`: the Fourier transform of `φ_ε` is
  integrable.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), §1.4.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Filter MeasureTheory
open scoped FourierTransform Topology

namespace TauCeti

/-! ### The Gaussian regularization and its elementary properties -/

section Regularize

variable {V : Type*} [NormedAddCommGroup V]

/-- The Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)` of a function `φ`. For `ε > 0` and
bounded `φ` — in particular when `φ` has a positive-definite subtraction kernel — it decays
like a Gaussian, and as `ε → 0⁺` it recovers `φ` pointwise. -/
noncomputable def gaussianRegularize (φ : V → ℂ) (ε : ℝ) : V → ℂ :=
  fun x => φ x * Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ))

/-- The defining formula of the Gaussian regularization. -/
@[simp]
theorem gaussianRegularize_apply (φ : V → ℂ) (ε : ℝ) (x : V) :
    gaussianRegularize φ ε x = φ x * Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) := by
  simp [gaussianRegularize]

/-- The Gaussian regularization is continuous when `φ` is. -/
theorem continuous_gaussianRegularize {φ : V → ℂ} (hcont : Continuous φ) (ε : ℝ) :
    Continuous (gaussianRegularize φ ε) :=
  hcont.mul (continuous_cexp_neg_mul_sq_norm ε)

/-- The Gaussian regularization converges to `φ` pointwise as `ε → 0`. -/
theorem tendsto_gaussianRegularize (φ : V → ℂ) (x : V) :
    Tendsto (fun ε : ℝ => gaussianRegularize φ ε x) (𝓝 0) (𝓝 (φ x)) := by
  have hc : Continuous fun ε : ℝ => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) := by fun_prop
  have h1 : Tendsto (fun ε : ℝ => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ))) (𝓝 0) (𝓝 1) := by
    simpa using hc.tendsto 0
  simpa using tendsto_const_nhds.mul h1

end Regularize

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Positive definiteness and integrability of the regularization -/

/-- The Gaussian regularization of a function with positive-definite subtraction kernel again
has a positive-definite subtraction kernel: it is the Schur product of the original kernel with
the Gaussian kernel `(a, b) ↦ exp (-ε‖a - b‖²)`. -/
theorem isPositiveDefiniteKernel_gaussianRegularize {φ : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => φ (a - b)) {ε : ℝ} (hε : 0 ≤ ε) :
    IsPositiveDefiniteKernel fun a b : V => gaussianRegularize φ ε (a - b) :=
  isPositiveDefiniteKernel_mul hpd (isPositiveDefiniteKernel_cexp_neg_mul_sq_norm hε)

/-- The Gaussian regularization of a bounded a.e. strongly measurable function is integrable
for every `ε > 0`: the Gaussian factor is integrable and dominates. In particular this applies
to a continuous function with positive-definite subtraction kernel, which is bounded by
`(φ 0).re`. -/
theorem integrable_gaussianRegularize {φ : V → ℂ} {C : ℝ} (hb : ∀ x, ‖φ x‖ ≤ C)
    (hm : AEStronglyMeasurable φ volume) {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianRegularize φ ε) := by
  have hgauss : Integrable fun x : V => Complex.exp (-(ε * ‖x‖ ^ 2 : ℝ)) :=
    integrable_cexp_neg_mul_sq_norm hε
  refine (hgauss.norm.const_mul C).mono
    (hm.mul (continuous_cexp_neg_mul_sq_norm ε).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp only [gaussianRegularize_apply, norm_mul, Real.norm_eq_abs, abs_norm]
  exact mul_le_mul_of_nonneg_right ((hb x).trans (le_abs_self C)) (norm_nonneg _)

/-- The Fourier transform of a Gaussian regularization of a continuous positive-definite
function is integrable, for every `ε > 0`. -/
theorem integrable_fourierIntegral_gaussianRegularize {φ : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => φ (a - b))
    (hcont : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (𝓕 (gaussianRegularize φ ε)) :=
  integrable_fourierIntegral_of_isPositiveDefiniteKernel _
    (isPositiveDefiniteKernel_gaussianRegularize hpd hε.le)
    (integrable_gaussianRegularize (norm_apply_le_map_zero_re_of_isPositiveDefiniteKernel hpd)
      hcont.aestronglyMeasurable hε)
    (continuous_gaussianRegularize hcont ε)

end TauCeti
