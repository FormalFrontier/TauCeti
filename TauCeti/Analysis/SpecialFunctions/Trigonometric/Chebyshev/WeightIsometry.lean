/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasisMap
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Envelope
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
public import TauCeti.MeasureTheory.Function.WeightL2Isometry

/-!
# The two Chebyshev normalizations are images of one another

The `OrthogonalL2Bases` roadmap ships each orthogonal family in two normalizations: the bare
polynomials as a basis of the *weighted measure*, and their `√w`-envelopes as a basis of the
*reference measure*. For Chebyshev these are `TauCeti.chebyshevTHilbertBasis` on
`Polynomial.Chebyshev.measureT` and `TauCeti.chebyshevTEnvelopeHilbertBasis` on
`volume.restrict (Set.Ioc (-1) 1)`. Both were assembled separately from the same bridge; nothing so
far said they are the *same* basis seen through the weight-change isometry.

This file says it. The Gaussian instance of the same statement
(`TauCeti.weightL2Isometry_gaussianHermiteHilbertBasis`) has to carry the dilation `u = x√2`,
because the Hermite functions are built on a rescaled argument; the Chebyshev `Tₙ` are not, so here
the identification is exact and can be stated at the level of bases rather than of individual
vectors.

The one thing standing in the way was that `Polynomial.Chebyshev.measureT` is not reducible outside
the module defining it, so the identity `measureT = w · (volume|_{(-1,1]})` was not available and
`TauCeti.weightL2Isometry` could not be pointed at it. That identity is
`TauCeti.chebyshevMeasureT_eq_withDensity`, recorded with the rest of the Chebyshev measure API in
`TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure`.

## Main statements

* `TauCeti.chebyshevWeightL2Isometry` — the resulting isometry
  `L²(measureT) ≃ₗᵢ[𝕜] L²((-1, 1]; dx)`, multiplication by `√w`.
* `TauCeti.chebyshevWeightL2Isometry_normalizedChebyshevTLp` — it carries the normalized mode
  `Tₙ/√cₙ` to the envelope function `τₙ`, with no dilation and no change of normalization.
* `TauCeti.chebyshevTHilbertBasis_mapₗᵢ` and
  `TauCeti.chebyshevTEnvelopeHilbertBasis_mapₗᵢ_symm` — the two named Chebyshev Hilbert bases are
  `HilbertBasis.mapₗᵢ`-images of one another under that isometry.
* `TauCeti.repr_chebyshevWeightL2Isometry` — hence a function and its `√w`-envelope have
  the *same* Chebyshev coefficients, so a Chebyshev expansion may be computed in whichever
  normalization is convenient.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-! ## The weight-change isometry for the Chebyshev interval -/

section Isometry

variable (𝕜 : Type*) [RCLike 𝕜]

/-- **The Chebyshev weight-change isometry** `L²(measureT) ≃ₗᵢ[𝕜] L²((-1, 1]; dx)`: multiplication
by `√w = (1-x²)^{-1/4}`.

This is `TauCeti.weightL2Isometry` at `μ = volume.restrict (Set.Ioc (-1) 1)` and
`w x = (1-x²)^{-1/2}`, precomposed with the transport of `L²(measureT)` along
`TauCeti.chebyshevMeasureT_eq_withDensity`. It is an equivalence, rather than merely an isometric
embedding, because the weight is almost everywhere positive on `(-1, 1]`. -/
noncomputable def chebyshevWeightL2Isometry :
    Lp 𝕜 2 (measureT : Measure ℝ) ≃ₗᵢ[𝕜] Lp 𝕜 2 (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
  (castLpₗᵢ (𝕜 := 𝕜) chebyshevMeasureT_eq_withDensity).trans
    (weightL2Isometry (volume.restrict (Set.Ioc (-1 : ℝ) 1)) (fun x => √(1 - x ^ 2)⁻¹)
      ae_zero_lt_chebyshevWeight measurable_chebyshevWeight.aemeasurable)

/-- The forward isometry multiplies a representative by `√w = (1-x²)^{-1/4}`. Without this pin the
definition would only assert that the two `L²` spaces are abstractly isometric. -/
theorem chebyshevWeightL2Isometry_apply (f : Lp 𝕜 2 (measureT : Measure ℝ)) :
    ⇑(chebyshevWeightL2Isometry 𝕜 f) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)]
      fun x => √(√(1 - x ^ 2)⁻¹) • (f : ℝ → 𝕜) x := by
  have happ : chebyshevWeightL2Isometry 𝕜 f
      = weightL2Isometry (volume.restrict (Set.Ioc (-1 : ℝ) 1)) (fun x => √(1 - x ^ 2)⁻¹)
          ae_zero_lt_chebyshevWeight measurable_chebyshevWeight.aemeasurable
          (castLpₗᵢ (𝕜 := 𝕜) chebyshevMeasureT_eq_withDensity f) := rfl
  rw [happ]
  refine (weightL2Isometry_apply _ _ _ _ _).trans (Filter.Eventually.of_forall fun x => ?_)
  simp only [coeFn_castLpₗᵢ]

/-- The inverse isometry divides a representative by `√w`. -/
theorem chebyshevWeightL2Isometry_symm_apply (g : Lp 𝕜 2 (volume.restrict (Set.Ioc (-1 : ℝ) 1))) :
    ⇑((chebyshevWeightL2Isometry 𝕜).symm g) =ᵐ[volume.restrict (Set.Ioc (-1 : ℝ) 1)]
      fun x => (√(√(1 - x ^ 2)⁻¹))⁻¹ • (g : ℝ → 𝕜) x := by
  have hsymm : (chebyshevWeightL2Isometry 𝕜).symm g
      = (castLpₗᵢ (𝕜 := 𝕜) chebyshevMeasureT_eq_withDensity).symm
          ((weightL2Isometry (volume.restrict (Set.Ioc (-1 : ℝ) 1)) (fun x => √(1 - x ^ 2)⁻¹)
            ae_zero_lt_chebyshevWeight measurable_chebyshevWeight.aemeasurable).symm g) := rfl
  rw [hsymm, castLpₗᵢ_symm]
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_)
    (weightL2Isometry_symm_apply _ _ ae_zero_lt_chebyshevWeight
      measurable_chebyshevWeight.aemeasurable g)
  simp only [coeFn_castLpₗᵢ]

/-! ## The two bases -/

/-- **The isometry carries the normalized Chebyshev mode to the envelope function.**
`√w · (Tₙ/√cₙ) = τₙ`: the weight moves from the measure into the function, and nothing else
changes — no dilation of the argument and no change of normalizing constant. -/
@[simp]
theorem chebyshevWeightL2Isometry_normalizedChebyshevTLp (n : ℕ) :
    chebyshevWeightL2Isometry 𝕜 (normalizedChebyshevTLp 𝕜 n) = chebyshevTEnvelopeLp 𝕜 n := by
  refine Lp.ext ?_
  filter_upwards [chebyshevWeightL2Isometry_apply 𝕜 (normalizedChebyshevTLp 𝕜 n),
    (coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n).filter_mono
      volume_restrict_absolutelyContinuous_measureT.ae_le,
    coeFn_chebyshevTEnvelopeLp 𝕜 n] with x hiso hmode henv
  rw [hiso, hmode, henv, Algebra.smul_def, ← map_mul, chebyshevTEnvelope_def, mul_comm]

/-- **The two Chebyshev bases are the same basis in two normalizations.** Transporting the
bare-polynomial basis of `L²(measureT)` across the weight-change isometry gives exactly the envelope
basis of `L²((-1, 1]; dx)`.

This is the Chebyshev instance of the roadmap's claim that a family's weighted-measure and
`√w`-envelope bases are `HilbertBasis.mapₗᵢ`-images of one another; unlike the Gaussian instance it
needs no dilation, so it is an equality of bases rather than of individual vectors up to a change of
variables. -/
@[simp]
theorem chebyshevTHilbertBasis_mapₗᵢ :
    (chebyshevTHilbertBasis 𝕜).mapₗᵢ (chebyshevWeightL2Isometry 𝕜)
      = chebyshevTEnvelopeHilbertBasis 𝕜 := by
  refine DFunLike.coe_injective ?_
  rw [HilbertBasis.coe_mapₗᵢ, coe_chebyshevTHilbertBasis, coe_chebyshevTEnvelopeHilbertBasis]
  exact funext fun n => chebyshevWeightL2Isometry_normalizedChebyshevTLp 𝕜 n

/-- The reverse transport: dividing the envelope basis by `√w` returns the bare-polynomial basis of
`L²(measureT)`. -/
@[simp]
theorem chebyshevTEnvelopeHilbertBasis_mapₗᵢ_symm :
    (chebyshevTEnvelopeHilbertBasis 𝕜).mapₗᵢ (chebyshevWeightL2Isometry 𝕜).symm
      = chebyshevTHilbertBasis 𝕜 := by
  rw [← chebyshevTHilbertBasis_mapₗᵢ, HilbertBasis.mapₗᵢ_symm]

/-! ## Consequences for coefficients -/

/-- **A function and its `√w`-envelope have the same Chebyshev coefficients.** The coordinates of
`√w · f` in the envelope basis of `L²((-1, 1]; dx)` are the coordinates of `f` in the
bare-polynomial basis of `L²(measureT)`, so a Chebyshev expansion may be computed in whichever
normalization is convenient. -/
theorem repr_chebyshevWeightL2Isometry (f : Lp 𝕜 2 (measureT : Measure ℝ)) :
    (chebyshevTEnvelopeHilbertBasis 𝕜).repr (chebyshevWeightL2Isometry 𝕜 f)
      = (chebyshevTHilbertBasis 𝕜).repr f := by
  rw [← chebyshevTHilbertBasis_mapₗᵢ, HilbertBasis.repr_mapₗᵢ,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The individual coefficient form of `TauCeti.repr_chebyshevWeightL2Isometry`: pairing
the envelope function `τₙ` against `√w · f` in `L²(dx)` is pairing the normalized mode `Tₙ/√cₙ`
against `f` in `L²(measureT)`. -/
theorem inner_chebyshevTEnvelopeLp_chebyshevWeightL2Isometry (n : ℕ)
    (f : Lp 𝕜 2 (measureT : Measure ℝ)) :
    inner 𝕜 (chebyshevTEnvelopeLp 𝕜 n) (chebyshevWeightL2Isometry 𝕜 f)
      = inner 𝕜 (normalizedChebyshevTLp 𝕜 n) f := by
  rw [← chebyshevWeightL2Isometry_normalizedChebyshevTLp 𝕜 n,
    LinearIsometryEquiv.inner_map_map]

end Isometry

end TauCeti
