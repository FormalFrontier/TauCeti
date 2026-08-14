/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.PosDef
-- The remaining import is proof-only: the analytic and positive-definiteness facts about the
-- Gaussian factor.
import TauCeti.Analysis.Bochner.Gaussian.Basic

/-!
# Gaussian regularization of positive-definite functions

The Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)` of a positive-definite function `φ` on a
real inner-product space is again positive definite (a Schur product with the Gaussian kernel)
and converges to `φ` pointwise as `ε → 0`. On a finite-dimensional space and for `ε > 0` it is
integrable whenever `φ` is bounded and almost-everywhere strongly measurable — in particular
whenever `φ` has a positive-definite subtraction kernel and is continuous. This is the
approximation device of the second step of Bochner's theorem: it replaces a bounded
positive-definite function by an integrable one to which Fourier inversion applies.

Adapted (Apache 2.0) from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source file `Bochner/Main.lean`;
the positive-definiteness hypotheses are restated through `Matrix.PosSemidef`.

## Main declarations

* `TauCeti.gaussianRegularize`: the Gaussian regularization `φ_ε = φ · exp (-ε‖·‖²)`.
* `TauCeti.posSemidef_gaussianRegularize`: `φ_ε` has a positive-definite
  subtraction kernel whenever `φ` does.
* `TauCeti.gaussianRegularize_apply_zero`: regularization preserves the value at the origin.
* `TauCeti.continuous_gaussianRegularize`, `TauCeti.integrable_gaussianRegularize`,
  `TauCeti.tendsto_gaussianRegularize`: the basic analytic facts about `φ_ε`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), §1.4.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder Topology

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

/-- The Gaussian regularization preserves the value at the origin: the Gaussian factor is `1`
there. This is what makes the regularized representing measures probability measures.

Not a `@[simp]` lemma: `simp` already proves it through `gaussianRegularize_apply`, and the
simpNF linter reports the tagged form as a duplicate. -/
theorem gaussianRegularize_apply_zero (φ : V → ℂ) (ε : ℝ) :
    gaussianRegularize φ ε 0 = φ 0 := by
  simp [gaussianRegularize]

/-- The Gaussian regularization is continuous when `φ` is. -/
theorem continuous_gaussianRegularize {φ : V → ℂ} (hcont : Continuous φ) (ε : ℝ) :
    Continuous (gaussianRegularize φ ε) :=
  hcont.mul (continuous_cexp_neg_mul_sq_norm ε)

/-- The Gaussian regularization converges to `φ` pointwise as `ε → 0`. -/
theorem tendsto_gaussianRegularize (φ : V → ℂ) (x : V) :
    Tendsto (fun ε : ℝ => gaussianRegularize φ ε x) (𝓝 0) (𝓝 (φ x)) := by
  simpa using tendsto_const_nhds.mul (tendsto_cexp_neg_mul_sq_norm x)

end Regularize

/-! ### Positive definiteness of the regularization -/

section PositiveDefinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian regularization of a function with positive-definite subtraction kernel again
has a positive-definite subtraction kernel: it is the Schur product of the original kernel with
the Gaussian kernel `(a, b) ↦ exp (-ε‖a - b‖²)`. -/
theorem posSemidef_gaussianRegularize {φ : V → ℂ}
    (hpd : Matrix.PosSemidef fun a b : V => φ (a - b)) {ε : ℝ} (hε : 0 ≤ ε) :
    Matrix.PosSemidef fun a b : V => gaussianRegularize φ ε (a - b) :=
  hpd.hadamard (posSemidef_cexp_neg_mul_sq_norm hε)

end PositiveDefinite

/-! ### Integrability of the regularization -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

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

end TauCeti
