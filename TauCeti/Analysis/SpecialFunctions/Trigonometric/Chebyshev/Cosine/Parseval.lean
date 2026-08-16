/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Cosine.HilbertBasis
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Parseval

/-!
# Parseval and expansions for the Chebyshev cosine Hilbert basis

`TauCeti.chebyshevCosineHilbertBasis` exhibits the normalized cosines
`cos (nθ) / √cₙ` (where `c₀ = π` and `cₙ = π / 2` for `n ≠ 0`) as a Hilbert basis of
`L²((0, π]; dθ)` on the angular interval `TauCeti.chebyshevAngleMeasure`, obtained by transporting
`TauCeti.chebyshevTHilbertBasis` along the cosine isometry `TauCeti.chebyshevCosineL2Equiv`.

This file supplies the coefficient, Parseval, and Fourier cosine series reconstruction API for that
basis. It identifies the abstract coordinates `HilbertBasis.repr` with both the measure and
interval integrals against the normalized cosines, proves Parseval in polarized and norm-square
forms, and gives the explicit integral consequence of coordinate transfer across the
Chebyshev-to-cosine equivalence.

## Main declarations

* `TauCeti.chebyshevCosineHilbertBasis_repr_apply` — identifies coordinates with measure integrals.
* `TauCeti.chebyshevCosineHilbertBasis_repr_apply_interval` — identifies coordinates with interval
  integrals `∫ θ in (0)..π, …`.
* `TauCeti.tsum_norm_sq_integral_normalizedChebyshevCosine_mul` — Parseval's identity in norm-square
  form.
* `TauCeti.tsum_star_integral_normalizedChebyshevCosine_mul_mul_integral` — Parseval's identity in
  polarized form.
* `TauCeti.hasSum_chebyshevCosine_expansion` — reconstruction of every `L²` function from its
  Fourier cosine series.
* `TauCeti.integral_normalizedChebyshevCosine_mul_chebyshevCosineL2Equiv` — identifies the explicit
  cosine and Chebyshev integral coefficients across the cosine equivalence.

All statements hold for an arbitrary `RCLike` scalar field `𝕜`, simultaneously covering real- and
complex-valued functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Coordinate representation -/

/-- The `n`-th coordinate of `f` in the Chebyshev cosine Hilbert basis is the integral of `f`
against the normalized cosine mode with respect to `chebyshevAngleMeasure`. -/
@[simp]
theorem chebyshevCosineHilbertBasis_repr_apply
    (f : Lp 𝕜 2 chebyshevAngleMeasure) (n : ℕ) :
    (chebyshevCosineHilbertBasis 𝕜).repr f n =
      ∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ ∂chebyshevAngleMeasure := by
  rw [(chebyshevCosineHilbertBasis 𝕜).repr_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_chebyshevCosineHilbertBasis 𝕜 n] with θ hθ
  rw [hθ]
  simp only [RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, mul_comm]

/-- The `n`-th coordinate of `f` in the Chebyshev cosine Hilbert basis as an interval integral
over `(0, π]`. -/
theorem chebyshevCosineHilbertBasis_repr_apply_interval
    (f : Lp 𝕜 2 chebyshevAngleMeasure) (n : ℕ) :
    (chebyshevCosineHilbertBasis 𝕜).repr f n =
      ∫ θ in (0)..Real.pi, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ := by
  rw [chebyshevCosineHilbertBasis_repr_apply, integral_chebyshevAngleMeasure]


/-! ## Parseval identities -/

/-- **Parseval's identity for the Chebyshev cosine basis** (norm-square form): the squared norms
of the explicit cosine integral coefficients of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_integral_normalizedChebyshevCosine_mul
    (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    ∑' n : ℕ, ‖∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ
        ∂chebyshevAngleMeasure‖ ^ 2 = ‖f‖ ^ 2 := by
  have h := (chebyshevCosineHilbertBasis 𝕜).tsum_norm_sq_inner f
  simp_rw [← (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    chebyshevCosineHilbertBasis_repr_apply] at h
  exact h

/-- **Parseval's identity for the Chebyshev cosine basis** (interval-integral form): the squared
norms of the interval-integral cosine coefficients of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_intervalIntegral_normalizedChebyshevCosine_mul
    (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    ∑' n : ℕ, ‖∫ θ in (0)..Real.pi, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ‖ ^ 2 =
      ‖f‖ ^ 2 := by
  have h := (chebyshevCosineHilbertBasis 𝕜).tsum_norm_sq_inner f
  simp_rw [← (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    chebyshevCosineHilbertBasis_repr_apply_interval] at h
  exact h

/-- **Parseval's identity for the Chebyshev cosine basis** (polarized form): the inner product of
`f` and `g` is the sum of the conjugated measure-integral coefficients of `f` times the
measure-integral coefficients of `g`. -/
theorem tsum_star_integral_normalizedChebyshevCosine_mul_mul_integral
    (f g : Lp 𝕜 2 chebyshevAngleMeasure) :
    ∑' n : ℕ,
        star (∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ
          ∂chebyshevAngleMeasure) *
          ∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * g θ
            ∂chebyshevAngleMeasure =
      inner 𝕜 f g := by
  have hfirst (n : ℕ) :
      inner 𝕜 f (chebyshevCosineHilbertBasis 𝕜 n) =
        star ((chebyshevCosineHilbertBasis 𝕜).repr f n) := by
    rw [← inner_conj_symm, (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
      starRingEnd_apply]
  simpa only [hfirst, ← (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    chebyshevCosineHilbertBasis_repr_apply] using
    (chebyshevCosineHilbertBasis 𝕜).tsum_inner_mul_inner f g

/-- **Parseval's identity for the Chebyshev cosine basis** (polarized interval-integral form): the
inner product of `f` and `g` is the sum of the conjugated interval-integral coefficients of `f`
times the interval-integral coefficients of `g`. -/
theorem tsum_star_intervalIntegral_normalizedChebyshevCosine_mul_mul_intervalIntegral
    (f g : Lp 𝕜 2 chebyshevAngleMeasure) :
    ∑' n : ℕ,
        star (∫ θ in (0)..Real.pi,
          (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ) *
          ∫ θ in (0)..Real.pi,
            (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * g θ =
      inner 𝕜 f g := by
  simpa only [integral_chebyshevAngleMeasure] using
    tsum_star_integral_normalizedChebyshevCosine_mul_mul_integral f g


/-- The squared norms of the cosine integral coefficients of an `L²` function are summable. -/
theorem summable_norm_sq_integral_normalizedChebyshevCosine_mul
    (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    Summable fun n : ℕ =>
      ‖∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ
        ∂chebyshevAngleMeasure‖ ^ 2 := by
  have h := (chebyshevCosineHilbertBasis 𝕜).summable_norm_sq_inner f
  simp_rw [← (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    chebyshevCosineHilbertBasis_repr_apply] at h
  exact h

/-- The squared norms of the interval-integral cosine coefficients of an `L²` function are
summable. -/
theorem summable_norm_sq_intervalIntegral_normalizedChebyshevCosine_mul
    (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    Summable fun n : ℕ =>
      ‖∫ θ in (0)..Real.pi, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ‖ ^ 2 := by
  have h := (chebyshevCosineHilbertBasis 𝕜).summable_norm_sq_inner f
  simp_rw [← (chebyshevCosineHilbertBasis 𝕜).repr_apply_apply,
    chebyshevCosineHilbertBasis_repr_apply_interval] at h
  exact h

/-! ## Series expansion -/

/-- **The Fourier cosine expansion.** Every `f ∈ L²((0, π]; dθ)` is the sum of its normalized
cosine series with respect to `chebyshevAngleMeasure`. -/
theorem hasSum_chebyshevCosine_expansion (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    HasSum (fun n : ℕ =>
      (∫ θ : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ
        ∂chebyshevAngleMeasure) • chebyshevCosineHilbertBasis 𝕜 n) f := by
  simpa only [chebyshevCosineHilbertBasis_repr_apply, Function.comp_apply] using
    (chebyshevCosineHilbertBasis 𝕜).hasSum_repr f

/-- **The Fourier cosine expansion** (interval-integral form). Every `f ∈ L²((0, π]; dθ)` is the
sum of its normalized cosine series with explicit interval integrals over `(0, π]`. -/
theorem hasSum_intervalIntegral_chebyshevCosine_expansion
    (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    HasSum (fun n : ℕ =>
      (∫ θ in (0)..Real.pi, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) * f θ) •
        chebyshevCosineHilbertBasis 𝕜 n) f := by
  simpa only [chebyshevCosineHilbertBasis_repr_apply_interval, Function.comp_apply] using
    (chebyshevCosineHilbertBasis 𝕜).hasSum_repr f

/-! ## Explicit transfer consequence -/

/-- **Integral form of coordinate preservation.** The angular cosine integral of `f ∘ cos` over
`(0, π]` equals the Chebyshev-weighted integral of `f` against `Tₙ / √cₙ`. -/
theorem integral_normalizedChebyshevCosine_mul_chebyshevCosineL2Equiv
    (n : ℕ) (g : Lp 𝕜 2 (measureT : Measure ℝ)) :
    (∫ θ in (0)..Real.pi, (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) *
        (chebyshevCosineL2Equiv 𝕜 g) θ) =
      ∫ x : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) * g x ∂measureT := by
  rw [← chebyshevCosineHilbertBasis_repr_apply_interval,
    chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv,
    chebyshevTHilbertBasis_repr_apply]

end TauCeti
