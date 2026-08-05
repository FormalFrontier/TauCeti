/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure

/-!
# The Chebyshev envelope functions as a Hilbert basis of `L²((-1, 1])`

`TauCeti.chebyshevTHilbertBasis` carries the Chebyshev weight `(1-x²)^{-1/2}` in the *measure*: the
bare normalized polynomials `Tₙ/√cₙ` are an orthonormal basis of `L²(measureT)`. This file supplies
the other normalization, with the weight in the *function*: the envelope functions

`τₙ(x) = Tₙ(x)·(1-x²)^{-1/4}/√cₙ`,  `c₀ = π`, `cₙ = π/2` for `n ≠ 0`,

are an orthonormal basis of `L²((-1, 1]; dx)` for plain Lebesgue measure on the Chebyshev interval.
That is the basis a Chebyshev expansion taken in an *unweighted* `L²` runs against.

Both normalizations come out of the same family-agnostic bridge. The basis here is
`TauCeti.hilbertBasisOfOrthogonalSystem` at `μ = volume.restrict (Set.Ioc (-1) 1)`,
`w x = (1-x²)^{-1/2}`, `f n = (T ℝ n).eval` and `c = TauCeti.chebyshevTNormSq`, so it exercises that
bridge on a compact weighted measure rather than on the Gaussian. Its orthogonality input is
Mathlib's, read off `measureT` through `Polynomial.Chebyshev.integral_measureT`; its completeness
input is `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`, whose one analytic hypothesis — a
finite exponential moment — is free on a bounded interval.

The reference measure is `volume.restrict (Set.Ioc (-1) 1)` rather than Mathlib's `measureT`
itself. The two are related by `measureT = w · (volume.restrict (Set.Ioc (-1) 1))`, but `measureT`
does not expose its body outside the module that defines it, so that identity is not available
here; the orthogonality relation is transported instead through the public integral formula, which
is all the bridge needs.

## Main statements

* `TauCeti.integral_eval_T_real_mul_eval_T_real_mul_chebyshevWeight` — the Chebyshev orthogonality
  relation re-keyed to Lebesgue measure on `(-1, 1]`, with the weight in the integrand.
* `TauCeti.integrable_exp_mul_abs_chebyshevWeight` — the weighted measure has every exponential
  moment finite, the hypothesis the completeness theorem needs.
* `TauCeti.integral_chebyshevTEnvelope_mul_chebyshevTEnvelope` — the envelope functions are
  orthonormal for `dx` on `(-1, 1]`.
* `TauCeti.chebyshevTEnvelopeHilbertBasis` — the basis itself.
* `TauCeti.coeFn_chebyshevTEnvelopeHilbertBasis`, `TauCeti.coe_chebyshevTEnvelopeHilbertBasis` —
  the anti-vacuity pins: the `n`-th basis vector really is `τₙ`, almost everywhere and as an `Lp`
  vector.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Polynomial.Chebyshev

/-! ## The weight and its moments -/

/-- The Chebyshev weight `(1-x²)^{-1/2}` is measurable. -/
theorem measurable_chebyshevWeight : Measurable fun x : ℝ => √(1 - x ^ 2)⁻¹ := by
  fun_prop

/-- The Chebyshev weight is almost everywhere positive on `(-1, 1]`: the endpoint `1`, where
`1 - x²` vanishes, is a Lebesgue null set, so the interior bound `x² < 1` holds almost
everywhere. -/
theorem ae_zero_lt_chebyshevWeight :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)), 0 < √(1 - x ^ 2)⁻¹ := by
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (-1 : ℝ)) (b := 1))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  refine Real.sqrt_pos.mpr (inv_pos.mpr ?_)
  nlinarith [hx.1, hx.2]

/-- **Finite exponential moments of the Chebyshev weight.** For every rate `a` the function
`e^{a|x|}` is integrable against the weighted measure `w·(volume|_{(-1,1]})`. On a bounded interval
`e^{a|x|} ≤ e^{|a|}`, so the statement reduces to integrability of the weight itself, which is
Mathlib's `Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv`.

This is the single analytic hypothesis behind both the `L²` membership of the polynomials and the
completeness of the family. -/
theorem integrable_exp_mul_abs_chebyshevWeight (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|))
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (√(1 - x ^ 2)⁻¹)) := by
  rw [integrable_withDensity_iff_integrable_smul' measurable_chebyshevWeight.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul]
  have hw : Integrable (fun x : ℝ => √(1 - x ^ 2)⁻¹) (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    intervalIntegrable_sqrt_one_sub_sq_inv.1
  refine Integrable.mono' (hw.const_mul (Real.exp |a|)) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2⟩
  have hexp : Real.exp (a * |x|) ≤ Real.exp |a| :=
    Real.exp_le_exp.mpr <| by nlinarith [le_abs_self a, abs_nonneg a, abs_nonneg x]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm (Real.exp |a|)]
  exact mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)

/-- **The Chebyshev orthogonality relation on Lebesgue measure.** Mathlib's relation is stated
against `measureT`; `Polynomial.Chebyshev.integral_measureT` rewrites it as an interval integral,
which is exactly an integral against `volume.restrict (Set.Ioc (-1) 1)` with the weight moved into
the integrand — the shape `TauCeti.hilbertBasisOfOrthogonalSystem` consumes. -/
theorem integral_eval_T_real_mul_eval_T_real_mul_chebyshevWeight (m n : ℕ) :
    (∫ x, (T ℝ m).eval x * (T ℝ n).eval x * √(1 - x ^ 2)⁻¹
        ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = if m = n then chebyshevTNormSq n else 0 := by
  rw [← integral_eval_T_real_mul_eval_T_real_measureT_eq_ite m n,
    integral_measureT fun x => (T ℝ m).eval x * (T ℝ n).eval x,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-! ## The envelope functions -/

/-- The `n`-th **Chebyshev envelope function** `τₙ(x) = Tₙ(x)·(1-x²)^{-1/4}/√cₙ`: the normalized
Chebyshev mode `TauCeti.normalizedChebyshevT` multiplied by the square root of the Chebyshev
weight, which is the weight-in-the-function counterpart of that mode. -/
noncomputable def chebyshevTEnvelope (n : ℕ) (x : ℝ) : ℝ :=
  normalizedChebyshevT n x * √(√(1 - x ^ 2)⁻¹)

/-- The defining equation for the Chebyshev envelope function. -/
@[simp]
theorem chebyshevTEnvelope_def (n : ℕ) (x : ℝ) :
    chebyshevTEnvelope n x = normalizedChebyshevT n x * √(√(1 - x ^ 2)⁻¹) :=
  chebyshevTEnvelope.eq_1 n x

/-- The zeroth envelope function is the bare square root of the weight, normalized by `√π`. -/
theorem chebyshevTEnvelope_zero (x : ℝ) :
    chebyshevTEnvelope 0 x = √(√(1 - x ^ 2)⁻¹) / √Real.pi := by
  have h0 : (T ℝ (0 : ℕ)).eval x = 1 := by simp
  rw [chebyshevTEnvelope_def, normalizedChebyshevT_def, chebyshevTNormSq_zero, h0]
  ring

/-- **The envelope functions are orthonormal for Lebesgue measure on `(-1, 1]`.** Multiplying two
envelope functions restores the full weight, `√w·√w = w`, which returns the integral to the
weighted orthogonality relation. -/
theorem integral_chebyshevTEnvelope_mul_chebyshevTEnvelope (m n : ℕ) :
    (∫ x, chebyshevTEnvelope m x * chebyshevTEnvelope n x
        ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = if m = n then 1 else 0 := by
  have hm := chebyshevTNormSq_pos m
  have hkey : (∫ x, chebyshevTEnvelope m x * chebyshevTEnvelope n x
      ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = (√(chebyshevTNormSq m) * √(chebyshevTNormSq n))⁻¹ *
        ∫ x, (T ℝ m).eval x * (T ℝ n).eval x * √(1 - x ^ 2)⁻¹
          ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hsq : √(√(1 - x ^ 2)⁻¹) * √(√(1 - x ^ 2)⁻¹) = √(1 - x ^ 2)⁻¹ :=
      Real.mul_self_sqrt (Real.sqrt_nonneg _)
    simp only [chebyshevTEnvelope_def, normalizedChebyshevT_def]
    linear_combination ((√(chebyshevTNormSq m) * √(chebyshevTNormSq n))⁻¹ *
      ((T ℝ m).eval x * (T ℝ n).eval x)) * hsq
  rw [hkey, integral_eval_T_real_mul_eval_T_real_mul_chebyshevWeight]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl, if_pos rfl, Real.mul_self_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  · rw [if_neg hmn, if_neg hmn, mul_zero]

/-! ## The Hilbert basis -/

section Basis

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `MemLp` obligation for the Chebyshev family against its weight: the generic
`TauCeti.memLp_two_bareNormalized` at `p n = Tₙ`, `c = TauCeti.chebyshevTNormSq`. -/
private theorem memLp_normalizedChebyshevT_weighted (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜)
        ((T ℝ n).eval x / √(chebyshevTNormSq n))) 2
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (√(1 - x ^ 2)⁻¹)) :=
  memLp_two_bareNormalized (𝕜 := 𝕜) ⟨1, one_pos, integrable_exp_mul_abs_chebyshevWeight 1⟩
    (fun n => T ℝ n) chebyshevTNormSq n

/-- **The Chebyshev envelope functions are a Hilbert basis of `L²((-1, 1]; dx)`.** The
weight-in-the-function normalization of Part C of the `OrthogonalL2Bases` roadmap, assembled from
the same bridge as the weight-in-the-measure basis `TauCeti.chebyshevTHilbertBasis`: orthonormality
from the Chebyshev orthogonality relation, completeness from moment determinacy applied to the
exact-degree family `Tₙ`. -/
noncomputable def chebyshevTEnvelopeHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume.restrict (Set.Ioc (-1 : ℝ) 1))) :=
  hilbertBasisOfOrthogonalSystem (𝕜 := 𝕜) (fun n x => (T ℝ n).eval x)
    (fun x => √(1 - x ^ 2)⁻¹) chebyshevTNormSq
    ae_zero_lt_chebyshevWeight measurable_chebyshevWeight.aemeasurable chebyshevTNormSq_pos
    integral_eval_T_real_mul_eval_T_real_mul_chebyshevWeight
    (memLp_normalizedChebyshevT_weighted 𝕜)
    (orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) (fun n => T ℝ n)
      (fun x => √(1 - x ^ 2)⁻¹) chebyshevTNormSq (fun n => by simp [degree_T])
      chebyshevTNormSq_pos ⟨1, one_pos, integrable_exp_mul_abs_chebyshevWeight 1⟩
      (memLp_normalizedChebyshevT_weighted 𝕜))

/-- **The basis vectors are the envelope functions.** Without this the construction would only
exhibit *some* Hilbert basis of `L²((-1, 1])`; here each vector is pinned to `τₙ`. -/
theorem coeFn_chebyshevTEnvelopeHilbertBasis (n : ℕ) :
    ⇑(chebyshevTEnvelopeHilbertBasis 𝕜 n)
      =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)]
        fun x => (algebraMap ℝ 𝕜) (chebyshevTEnvelope n x) := by
  rw [chebyshevTEnvelopeHilbertBasis]
  filter_upwards [coeFn_hilbertBasisOfOrthogonalSystem (𝕜 := 𝕜) _ _ _ _ _ _ _ _ _ n] with x hx
  rw [hx, chebyshevTEnvelope_def, normalizedChebyshevT_def]
  congr 1
  ring

/-- Each envelope function lies in `L²((-1, 1]; dx)`. It is the representative of a basis vector,
so this is read off the basis rather than re-proved: the `L²` membership is exactly what the
weighted `MemLp` obligation of the bridge already established, transported by
`TauCeti.coeFn_chebyshevTEnvelopeHilbertBasis`. -/
theorem memLp_two_algebraMap_chebyshevTEnvelope (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (chebyshevTEnvelope n x)) 2
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
  MemLp.ae_eq (coeFn_chebyshevTEnvelopeHilbertBasis 𝕜 n)
    (Lp.memLp (chebyshevTEnvelopeHilbertBasis 𝕜 n))

/-- The `n`-th envelope function as a vector of `L²((-1, 1]; dx)`. -/
noncomputable def chebyshevTEnvelopeLp (n : ℕ) :
    Lp 𝕜 2 (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
  (memLp_two_algebraMap_chebyshevTEnvelope 𝕜 n).toLp _

/-- The `Lp` representative of `TauCeti.chebyshevTEnvelopeLp` is the expected scalar-cast envelope
function. -/
theorem coeFn_chebyshevTEnvelopeLp (n : ℕ) :
    ⇑(chebyshevTEnvelopeLp 𝕜 n) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)]
      fun x => (algebraMap ℝ 𝕜) (chebyshevTEnvelope n x) :=
  MemLp.coeFn_toLp _

/-- **The basis is the envelope family, as an equality of `ℕ`-indexed families of `L²` vectors.**
This is the shape the roadmap's element-level export asks for; it upgrades the almost-everywhere
`TauCeti.coeFn_chebyshevTEnvelopeHilbertBasis` to an identity of `Lp` vectors. -/
@[simp]
theorem coe_chebyshevTEnvelopeHilbertBasis :
    ⇑(chebyshevTEnvelopeHilbertBasis 𝕜) = chebyshevTEnvelopeLp 𝕜 := by
  funext n
  exact Lp.ext ((coeFn_chebyshevTEnvelopeHilbertBasis 𝕜 n).trans
    (coeFn_chebyshevTEnvelopeLp 𝕜 n).symm)

/-- The envelope functions are orthonormal in `L²((-1, 1]; dx)`. -/
theorem orthonormal_chebyshevTEnvelopeLp : Orthonormal 𝕜 (chebyshevTEnvelopeLp 𝕜) := by
  rw [← coe_chebyshevTEnvelopeHilbertBasis]
  exact (chebyshevTEnvelopeHilbertBasis 𝕜).orthonormal

end Basis

end TauCeti
