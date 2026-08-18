/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Analysis.Bochner.CharFun.PosDef
public import TauCeti.Analysis.PositiveDefinite.Function.Kernel
-- The remaining import is proof-only: the integrability of the complex Gaussian.
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian is a positive-definite function

The Gaussian `a ↦ exp (-c‖a‖²)` on a real inner-product space `V` is continuous, and its
subtraction kernel `(a, b) ↦ exp (-c‖a - b‖²)` is positive definite, for every `c ≥ 0`. This
supplies the positive-definiteness half of the Gaussian acceptance example requested in Part C of
the `OneParameterSemigroups` roadmap in TauCetiRoadmap ("positive-definite functions and
Bochner's theorem"); the representing-measure half is supplied by `TauCeti.bochner` in
`TauCeti/Analysis/Bochner/BochnerTheorem.lean`.

The positive-definiteness is not proved from scratch: Mathlib's
`ProbabilityTheory.charFun_stdGaussian` computes the characteristic function of the standard
Gaussian measure on `V` to be `t ↦ exp (-‖t‖²/2)`, and
`TauCeti.posSemidef_charFun` (the finite-measure Fourier-transform correspondence)
already records that a characteristic function has a positive-definite kernel. Rescaling the
argument by `√(2c)` turns `exp (-‖·‖²/2)` into `exp (-c‖·‖²)`. The standard Gaussian measure
needs a finite-dimensional space, but the kernel form transfers to an arbitrary real
inner-product space: positive definiteness constrains only finite families of points, and those
span a finite-dimensional subspace on which the norm — hence the kernel — restricts. The function
form then follows on that same generality through
`isPositiveDefinite_iff_posSemidef_sub`.

## Main declarations

* `TauCeti.charFun_stdGaussian_sqrt_smul`: on a finite-dimensional space,
  `charFun (stdGaussian V) (√(2c) • a) = exp (-c‖a‖²)`.
* `TauCeti.isPositiveDefinite_cexp_neg_mul_sq_norm`: on any real inner-product space,
  `a ↦ exp (-c‖a‖²)` is positive definite for `c ≥ 0` under the negation involution.
* `TauCeti.posSemidef_cexp_neg_mul_sq_norm`: the involution-free kernel form,
  `(a, b) ↦ exp (-c‖a - b‖²)` is a positive-definite kernel on any real inner-product space.
* `TauCeti.continuous_cexp_neg_mul_sq_norm`: `a ↦ exp (-c‖a‖²)` is continuous.
* `TauCeti.tendsto_cexp_neg_mul_sq_norm`: `exp (-c‖a‖²) → 1` as `c → 0`.
* `TauCeti.integrable_cexp_neg_mul_sq_norm`: `a ↦ exp (-c‖a‖²)` is integrable for `c > 0`.
* `TauCeti.isPositiveDefinite_cexp_neg_sq_norm`: the positive-definiteness half of the Gaussian
  acceptance example (`c = 1`), `a ↦ exp (-‖a‖²)`.
* `TauCeti.posSemidef_cexp_neg_sq_norm`: the involution-free kernel form of the
  `c = 1` acceptance example, `(a, b) ↦ exp (-‖a - b‖²)`.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962) — Bochner's theorem and positive-definite
  functions.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ComplexOrder Topology

namespace TauCeti

/-! ### The Gaussian factor -/

section Elementary

variable {V : Type*} [NormedAddCommGroup V]

/-- The Gaussian `a ↦ exp (-c‖a‖²)` is continuous on `V` for every real `c`. -/
theorem continuous_cexp_neg_mul_sq_norm (c : ℝ) :
    Continuous fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  fun_prop

/-- The Gaussian factor `exp (-c‖a‖²)` tends to `1` as the width parameter `c` tends to `0`.
This is the pointwise convergence underlying Gaussian regularization. -/
theorem tendsto_cexp_neg_mul_sq_norm (a : V) :
    Filter.Tendsto (fun c : ℝ => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ))) (𝓝 0) (𝓝 1) := by
  have hc : Continuous fun c : ℝ => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by fun_prop
  simpa using hc.tendsto 0

end Elementary

/-! ### The finite-dimensional case -/

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian `a ↦ exp (-c‖a‖²)` is integrable on `V` for every `c > 0`. -/
theorem integrable_cexp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  have hre : 0 < (c : ℂ).re := by simpa using hc
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hre 0 (0 : V)
  simp only [zero_mul, add_zero] at h
  refine h.congr (ae_of_all _ fun a => ?_)
  push_cast
  ring_nf

/-- The characteristic function of the standard Gaussian measure on `V`, with its argument
rescaled by `√(2c)`, is the Gaussian `a ↦ exp (-c‖a‖²)`. -/
theorem charFun_stdGaussian_sqrt_smul {c : ℝ} (hc : 0 ≤ c) (a : V) :
    charFun (stdGaussian V) (Real.sqrt (2 * c) • a) = Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) := by
  have hsq : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (by positivity)
  have hn : ‖(Real.sqrt (2 * c)) • a‖ ^ 2 = 2 * c * ‖a‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsq]
  rw [charFun_stdGaussian, ← Complex.ofReal_pow, hn]
  congr 1
  push_cast
  ring

/-- The Gaussian kernel `(a, b) ↦ exp (-c‖a - b‖²)` is positive definite on a finite-dimensional
space: it is the pullback of the characteristic function of the standard Gaussian measure along
the rescaling `√(2c) • ·`. The general case, `posSemidef_cexp_neg_mul_sq_norm`,
reduces to this one on the span of a finite family of points. -/
private theorem posSemidef_cexp_neg_mul_sq_norm_of_finiteDimensional {c : ℝ}
    (hc : 0 ≤ c) :
    Matrix.PosSemidef fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ)) := by
  have h := (posSemidef_charFun (μ := stdGaussian V)).submatrix
    (fun a : V => Real.sqrt (2 * c) • a)
  have heq : Matrix.submatrix
      (Matrix.of fun x y : V => charFun (stdGaussian V) (x - y))
      (fun a : V => Real.sqrt (2 * c) • a) (fun a => Real.sqrt (2 * c) • a) =
      fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ)) := by
    apply Matrix.ext
    intro a b
    rw [Matrix.submatrix_apply, Matrix.of_apply, ← smul_sub,
      charFun_stdGaussian_sqrt_smul hc]
  exact heq ▸ h

end FiniteDimensional

/-! ### Positive definiteness on an arbitrary inner-product space -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The translation-invariant kernel attached to the Gaussian, `(a, b) ↦ exp (-c‖a - b‖²)`, is
positive definite for every `c ≥ 0`, on any real inner-product space. This is the kernel form of
`isPositiveDefinite_cexp_neg_mul_sq_norm`, avoiding any explicit choice of involution on the
domain.

Positive definiteness constrains only finite families of points, and any finite family spans a
finite-dimensional subspace on which the kernel restricts to the Gaussian kernel of that
subspace; so the statement follows from the finite-dimensional case, where the Gaussian is the
characteristic function of the standard Gaussian measure. -/
theorem posSemidef_cexp_neg_mul_sq_norm {c : ℝ} (hc : 0 ≤ c) :
    Matrix.PosSemidef fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ)) := by
  refine posSemidef_iff_finite_sum.mpr ⟨fun a b => ?_, fun {ι : Type} _ v x => ?_⟩
  · rw [RCLike.star_def, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, norm_sub_rev]
  · -- Restrict to the span of the finite family, a finite-dimensional inner-product space.
    let W := Submodule.span ℝ (Set.range v)
    have : FiniteDimensional ℝ W := .span_of_finite ℝ (Set.finite_range v)
    let _mW : MeasurableSpace W := borel W
    have : BorelSpace W := ⟨rfl⟩
    let w : ι → W := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hnorm : ∀ i j, ‖w i - w j‖ = ‖v i - v j‖ := fun i j => by
      simp [w, Submodule.coe_norm]
    have h := (posSemidef_iff_finite_sum.mp
      (posSemidef_cexp_neg_mul_sq_norm_of_finiteDimensional (V := W) hc)).2 w x
    simpa only [hnorm] using h

/-- The Gaussian `a ↦ exp (-c‖a‖²)` on a real inner-product space is positive definite for every
`c ≥ 0`, under the negation involution `a⋆ = -a`. This is the function form of
`posSemidef_cexp_neg_mul_sq_norm`. -/
theorem isPositiveDefinite_cexp_neg_mul_sq_norm [StarAddMonoid V]
    (hstar : ∀ x : V, star x = -x) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveDefinite fun a : V => Complex.exp (-(c * ‖a‖ ^ 2 : ℝ)) :=
  (isPositiveDefinite_iff_posSemidef_sub hstar).mpr
    (posSemidef_cexp_neg_mul_sq_norm hc)

/-- The positive-definiteness half of the Gaussian acceptance example (`c = 1`):
`a ↦ exp (-‖a‖²)` is positive definite under the negation involution. -/
theorem isPositiveDefinite_cexp_neg_sq_norm [StarAddMonoid V] (hstar : ∀ x : V, star x = -x) :
    IsPositiveDefinite fun a : V => Complex.exp (-(‖a‖ ^ 2 : ℝ)) := by
  simpa only [one_mul] using
    isPositiveDefinite_cexp_neg_mul_sq_norm hstar (V := V) (c := 1) zero_le_one

/-- The involution-free kernel form of the Gaussian acceptance example (`c = 1`):
`(a, b) ↦ exp (-‖a - b‖²)` is a positive-definite kernel. Unlike
`isPositiveDefinite_cexp_neg_sq_norm`, this requires no choice of involution on `V`. -/
theorem posSemidef_cexp_neg_sq_norm :
    Matrix.PosSemidef fun a b : V => Complex.exp (-(‖a - b‖ ^ 2 : ℝ)) := by
  simpa only [one_mul] using
    posSemidef_cexp_neg_mul_sq_norm (V := V) (c := 1) zero_le_one

end General

end TauCeti
