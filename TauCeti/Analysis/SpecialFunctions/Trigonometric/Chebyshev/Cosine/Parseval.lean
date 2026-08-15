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
forms, and establishes the transfer of coordinates and inner products across the
Chebyshev-to-cosine equivalence.

## Main declarations

* `TauCeti.chebyshevCosineHilbertBasis_repr_apply` — identifies coordinates with measure integrals.
* `TauCeti.chebyshevCosineHilbertBasis_repr_apply_interval` — identifies coordinates with interval
  integrals `∫ θ in (0)..π, …`.
* `TauCeti.tsum_norm_sq_integral_normalizedChebyshevCosine_mul` — Parseval's identity in norm-square
  form.
* `TauCeti.tsum_inner_mul_inner_chebyshevCosineHilbertBasis` — Parseval's identity in polarized
  form.
* `TauCeti.hasSum_chebyshevCosine_expansion` — reconstruction of every `L²` function from its
  Fourier cosine series.
* `TauCeti.chebyshevCosineL2Equiv_normalizedChebyshevTLp` — the cosine equivalence maps the
  normalized Chebyshev polynomial mode `Tₙ / √cₙ` to the normalized cosine mode.
* `TauCeti.chebyshevTHilbertBasis_mapₗᵢ_chebyshevCosineL2Equiv` — the Chebyshev cosine basis is the
  `mapₗᵢ` image of the Chebyshev polynomial basis under the cosine equivalence.
* `TauCeti.chebyshevCosineHilbertBasis_mapₗᵢ_symm` — reverse transport along the inverse cosine
  equivalence returns the Chebyshev polynomial basis.
* `TauCeti.chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv` — the cosine coordinate of
  `f ∘ cos` equals the Chebyshev polynomial coordinate of `f`.

All statements hold for an arbitrary `RCLike` scalar field `𝕜`, simultaneously covering real- and
complex-valued functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable (𝕜 : Type*) [RCLike 𝕜]

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

/-- The coordinates of the `n`-th normalized cosine mode are a single `1` in position `n`. -/
@[simp]
theorem chebyshevCosineHilbertBasis_repr_self (n : ℕ) :
    (chebyshevCosineHilbertBasis 𝕜).repr (chebyshevCosineHilbertBasis 𝕜 n) =
      lp.single 2 n (1 : 𝕜) := by
  classical
  exact (chebyshevCosineHilbertBasis 𝕜).repr_self n

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

/-- **Parseval's identity for the Chebyshev cosine basis** (polarized form): the inner product
of `f` and `g` is the sum of products of their cosine coefficients. -/
theorem tsum_inner_mul_inner_chebyshevCosineHilbertBasis
    (f g : Lp 𝕜 2 chebyshevAngleMeasure) :
    ∑' n : ℕ, inner 𝕜 f (chebyshevCosineHilbertBasis 𝕜 n) *
        inner 𝕜 (chebyshevCosineHilbertBasis 𝕜 n) g = inner 𝕜 f g :=
  (chebyshevCosineHilbertBasis 𝕜).tsum_inner_mul_inner f g

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

/-! ## Transfer across the cosine change of variables -/

/-- **The cosine change of variables carries Chebyshev polynomial modes to cosine modes.**
`chebyshevCosineL2Equiv` maps the normalized Chebyshev mode `Tₙ / √cₙ` in `L²(measureT)` to the
normalized angular cosine mode `cos (nθ) / √cₙ` in `L²(chebyshevAngleMeasure)`. -/
@[simp]
theorem chebyshevCosineL2Equiv_normalizedChebyshevTLp (n : ℕ) :
    chebyshevCosineL2Equiv 𝕜 (normalizedChebyshevTLp 𝕜 n) =
      chebyshevCosineHilbertBasis 𝕜 n := by
  refine Lp.ext ?_
  filter_upwards [chebyshevCosineL2Equiv_apply 𝕜 (normalizedChebyshevTLp 𝕜 n),
    measurePreserving_cos_chebyshev.quasiMeasurePreserving.ae_eq
      (coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n),
    coeFn_chebyshevCosineHilbertBasis 𝕜 n] with θ hcos hmode hcosmode
  rw [hcos, hcosmode]
  exact hmode.trans (congrArg (algebraMap ℝ 𝕜) (by
    rw [normalizedChebyshevT_def, normalized_eval_T_real_cos_eq_normalizedChebyshevCosine]))

/-- The inverse cosine equivalence maps the normalized cosine mode back to the normalized Chebyshev
polynomial mode. -/
@[simp]
theorem chebyshevCosineL2Equiv_symm_chebyshevCosineHilbertBasis (n : ℕ) :
    (chebyshevCosineL2Equiv 𝕜).symm (chebyshevCosineHilbertBasis 𝕜 n) =
      normalizedChebyshevTLp 𝕜 n := by
  rw [← chebyshevCosineL2Equiv_normalizedChebyshevTLp, LinearIsometryEquiv.symm_apply_apply]

/-- **The Chebyshev cosine Hilbert basis is the transported Chebyshev polynomial basis.**
Transporting `TauCeti.chebyshevTHilbertBasis` across `TauCeti.chebyshevCosineL2Equiv` equals
`TauCeti.chebyshevCosineHilbertBasis`. -/
@[simp]
theorem chebyshevTHilbertBasis_mapₗᵢ_chebyshevCosineL2Equiv :
    (chebyshevTHilbertBasis 𝕜).mapₗᵢ (chebyshevCosineL2Equiv 𝕜) =
      chebyshevCosineHilbertBasis 𝕜 := by
  refine DFunLike.coe_injective ?_
  rw [HilbertBasis.coe_mapₗᵢ, coe_chebyshevTHilbertBasis]
  exact funext fun n => chebyshevCosineL2Equiv_normalizedChebyshevTLp 𝕜 n

/-- The reverse transport: transporting `TauCeti.chebyshevCosineHilbertBasis` across the inverse
cosine equivalence returns the Chebyshev polynomial basis `TauCeti.chebyshevTHilbertBasis`. -/
@[simp]
theorem chebyshevCosineHilbertBasis_mapₗᵢ_symm :
    (chebyshevCosineHilbertBasis 𝕜).mapₗᵢ (chebyshevCosineL2Equiv 𝕜).symm =
      chebyshevTHilbertBasis 𝕜 := by
  rw [← chebyshevTHilbertBasis_mapₗᵢ_chebyshevCosineL2Equiv, HilbertBasis.mapₗᵢ_symm]

/-- **Coordinates are preserved under the cosine change of variables.** The `n`-th coordinate of
`f ∘ cos` in the Chebyshev cosine basis equals the `n`-th coordinate of `f` in the Chebyshev
polynomial basis. -/
theorem chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv
    (g : Lp 𝕜 2 (measureT : Measure ℝ)) (n : ℕ) :
    (chebyshevCosineHilbertBasis 𝕜).repr (chebyshevCosineL2Equiv 𝕜 g) n =
      (chebyshevTHilbertBasis 𝕜).repr g n := by
  rw [← chebyshevTHilbertBasis_mapₗᵢ_chebyshevCosineL2Equiv, HilbertBasis.repr_mapₗᵢ,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The inverse coordinate identification: the Chebyshev polynomial coordinate of `f ∘ arccos`
equals the cosine coordinate of `f`. -/
theorem chebyshevTHilbertBasis_repr_chebyshevCosineL2Equiv_symm
    (f : Lp 𝕜 2 chebyshevAngleMeasure) (n : ℕ) :
    (chebyshevTHilbertBasis 𝕜).repr ((chebyshevCosineL2Equiv 𝕜).symm f) n =
      (chebyshevCosineHilbertBasis 𝕜).repr f n := by
  rw [← chebyshevCosineHilbertBasis_repr_chebyshevCosineL2Equiv,
    LinearIsometryEquiv.apply_symm_apply]

/-- Pairing against the normalized cosine mode in `L²(chebyshevAngleMeasure)` is pairing against
the normalized Chebyshev polynomial mode in `L²(measureT)`. -/
theorem inner_chebyshevCosineHilbertBasis_chebyshevCosineL2Equiv
    (n : ℕ) (g : Lp 𝕜 2 (measureT : Measure ℝ)) :
    inner 𝕜 (chebyshevCosineHilbertBasis 𝕜 n) (chebyshevCosineL2Equiv 𝕜 g) =
      inner 𝕜 (normalizedChebyshevTLp 𝕜 n) g := by
  rw [← chebyshevCosineL2Equiv_normalizedChebyshevTLp, LinearIsometryEquiv.inner_map_map]

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
