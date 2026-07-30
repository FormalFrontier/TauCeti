/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasisMap
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Cosine.Transfer
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The Chebyshev basis as a cosine basis

The substitution `x = cos θ` sends Lebesgue measure on `(0, π]` to Mathlib's Chebyshev
orthogonality measure `Polynomial.Chebyshev.measureT`. This file upgrades the integral identity
`Polynomial.Chebyshev.integral_measureT_eq_integral_cos` to a linear isometric equivalence between
the corresponding `L²` spaces.

Transporting `TauCeti.chebyshevTHilbertBasis` across this equivalence gives a Hilbert basis on the
angular interval. Its `n`th vector is the normalized cosine
`cos (nθ) / √cₙ`, where `c₀ = π` and `cₙ = π / 2` for `n > 0`. This is the unitary-transfer
statement required by Part C of the `OrthogonalL2Bases` roadmap.

## Main declarations

* `TauCeti.chebyshevAngleMeasure` is Lebesgue measure restricted to `(0, π]`.
* `TauCeti.chebyshevCosineL2Equiv` pulls an `L²(measureT)` function back along `Real.cos`.
* `TauCeti.chebyshevCosineHilbertBasis` is the transported Chebyshev basis.
* `TauCeti.coeFn_chebyshevCosineHilbertBasis` identifies its vectors with the normalized cosines.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- Lebesgue measure on the angular interval `(0, π]`. The choice of half-open endpoints matches
`intervalIntegral.integral_of_le`; changing either endpoint does not change the measure. -/
noncomputable def chebyshevAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc 0 Real.pi)

/-- Integrating against `chebyshevAngleMeasure` is interval integration from `0` to `π`. -/
theorem integral_chebyshevAngleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ θ, f θ ∂chebyshevAngleMeasure = ∫ θ in (0)..Real.pi, f θ := by
  rw [chebyshevAngleMeasure, intervalIntegral.integral_of_le Real.pi_nonneg]

/-- The pushforward of angular Lebesgue measure under `cos` is the Chebyshev measure. -/
theorem map_cos_chebyshevAngleMeasure :
    Measure.map Real.cos chebyshevAngleMeasure = measureT := by
  letI : IsFiniteMeasure chebyshevAngleMeasure := by
    rw [chebyshevAngleMeasure]
    infer_instance
  letI : Measure.InnerRegular chebyshevAngleMeasure := by
    rw [chebyshevAngleMeasure]
    infer_instance
  letI : Measure.InnerRegular (Measure.map Real.cos chebyshevAngleMeasure) :=
    Measure.InnerRegular.map_of_continuous Real.continuous_cos
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂Measure.map Real.cos chebyshevAngleMeasure) =
    ∫ x, f.toContinuousMap x ∂measureT
  rw [integral_map_of_stronglyMeasurable Real.continuous_cos.measurable
      f.toContinuousMap.continuous.stronglyMeasurable,
    integral_chebyshevAngleMeasure, integral_measureT_eq_integral_cos]

/-- The cosine change of variables preserves `chebyshevAngleMeasure` and `measureT`. -/
theorem measurePreserving_cos_chebyshev :
    MeasurePreserving Real.cos chebyshevAngleMeasure measureT where
  measurable := Real.continuous_cos.measurable
  map_eq := map_cos_chebyshevAngleMeasure

/-- The Chebyshev measure is concentrated on `[-1, 1]`, so `cos (arccos x) = x` almost
everywhere. -/
private theorem cos_comp_arccos_ae :
    Real.cos ∘ Real.arccos =ᵐ[measureT] id := by
  filter_upwards [ae_mem_Icc_measureT] with x hx
  exact Real.cos_arccos hx.1 hx.2

/-- Angular Lebesgue measure is concentrated on `(0, π]`, so `arccos (cos θ) = θ` almost
everywhere. -/
private theorem arccos_comp_cos_ae :
    Real.arccos ∘ Real.cos =ᵐ[chebyshevAngleMeasure] id := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  exact Real.arccos_cos hθ.1.le hθ.2

/-- The inverse change of variables `arccos` preserves the Chebyshev and angular measures. -/
theorem measurePreserving_arccos_chebyshev :
    MeasurePreserving Real.arccos measureT chebyshevAngleMeasure where
  measurable := Real.continuous_arccos.measurable
  map_eq := by
    calc
      Measure.map Real.arccos measureT
          = Measure.map Real.arccos (Measure.map Real.cos chebyshevAngleMeasure) := by
              rw [map_cos_chebyshevAngleMeasure]
      _ = Measure.map (Real.arccos ∘ Real.cos) chebyshevAngleMeasure := by
            rw [Measure.map_map Real.continuous_arccos.measurable Real.continuous_cos.measurable]
      _ = Measure.map id chebyshevAngleMeasure :=
            Measure.map_congr arccos_comp_cos_ae
      _ = chebyshevAngleMeasure := Measure.map_id

section L2

variable (𝕜 : Type*) [RCLike 𝕜]

private noncomputable def chebyshevCosineL2Isometry :
    Lp 𝕜 2 measureT →ₗᵢ[𝕜] Lp 𝕜 2 chebyshevAngleMeasure :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Real.cos measurePreserving_cos_chebyshev

private noncomputable def chebyshevArccosL2LinearMap :
    Lp 𝕜 2 chebyshevAngleMeasure →ₗ[𝕜] Lp 𝕜 2 measureT :=
  Lp.compMeasurePreservingₗ 𝕜 Real.arccos measurePreserving_arccos_chebyshev

private theorem chebyshevCosineL2Isometry_comp_arccos :
    (chebyshevCosineL2Isometry 𝕜).toLinearMap.comp (chebyshevArccosL2LinearMap 𝕜) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  change Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev
      (Lp.compMeasurePreserving Real.arccos measurePreserving_arccos_chebyshev f) = f
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving Real.arccos measurePreserving_arccos_chebyshev f)
      measurePreserving_cos_chebyshev,
    measurePreserving_cos_chebyshev.quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f measurePreserving_arccos_chebyshev),
    arccos_comp_cos_ae] with θ hcos harccos hinv
  rw [hcos, harccos]
  change f (Real.arccos (Real.cos θ)) = f θ
  change Real.arccos (Real.cos θ) = θ at hinv
  rw [hinv]

private theorem chebyshevArccosL2LinearMap_comp_cosine :
    (chebyshevArccosL2LinearMap 𝕜).comp (chebyshevCosineL2Isometry 𝕜).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  change Lp.compMeasurePreserving Real.arccos measurePreserving_arccos_chebyshev
      (Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev f) = f
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev f)
      measurePreserving_arccos_chebyshev,
    measurePreserving_arccos_chebyshev.quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f measurePreserving_cos_chebyshev),
    cos_comp_arccos_ae] with x harccos hcos hinv
  rw [harccos, hcos]
  change f (Real.cos (Real.arccos x)) = f x
  change Real.cos (Real.arccos x) = x at hinv
  rw [hinv]

/-- **The Chebyshev-to-cosine `L²` equivalence.** It pulls a function on `[-1,1]` back along
`x = cos θ`; its inverse pulls an angular function back along `θ = arccos x`. -/
noncomputable def chebyshevCosineL2Equiv :
    Lp 𝕜 2 measureT ≃ₗᵢ[𝕜] Lp 𝕜 2 chebyshevAngleMeasure :=
  LinearIsometryEquiv.ofLinearIsometry (chebyshevCosineL2Isometry 𝕜)
    (chebyshevArccosL2LinearMap 𝕜)
    (chebyshevCosineL2Isometry_comp_arccos 𝕜)
    (chebyshevArccosL2LinearMap_comp_cosine 𝕜)

/-- The forward Chebyshev-to-cosine equivalence is composition with `Real.cos`. -/
theorem chebyshevCosineL2Equiv_apply (f : Lp 𝕜 2 measureT) :
    ⇑(chebyshevCosineL2Equiv 𝕜 f) =ᵐ[chebyshevAngleMeasure] fun θ => f (Real.cos θ) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_cos_chebyshev

/-- The inverse Chebyshev-to-cosine equivalence is composition with `Real.arccos`. -/
theorem chebyshevCosineL2Equiv_symm_apply (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    ⇑((chebyshevCosineL2Equiv 𝕜).symm f) =ᵐ[measureT] fun x => f (Real.arccos x) := by
  exact Lp.coeFn_compMeasurePreserving f measurePreserving_arccos_chebyshev

/-- The normalized cosine Hilbert basis of `L²((0, π])`, obtained by transporting the normalized
Chebyshev `T` basis under `x = cos θ`. -/
noncomputable def chebyshevCosineHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 chebyshevAngleMeasure) :=
  (chebyshevTHilbertBasis 𝕜).mapₗᵢ (chebyshevCosineL2Equiv 𝕜)

/-- **Chebyshev-cosine basis correspondence.** The `n`th vector of the transported Chebyshev basis
is almost everywhere the scalar-cast normalized cosine `cos (nθ) / √cₙ`. -/
theorem coeFn_chebyshevCosineHilbertBasis (n : ℕ) :
    ⇑(chebyshevCosineHilbertBasis 𝕜 n) =ᵐ[chebyshevAngleMeasure]
      fun θ => (algebraMap ℝ 𝕜) (normalizedChebyshevCosine n θ) := by
  rw [chebyshevCosineHilbertBasis, HilbertBasis.mapₗᵢ_apply]
  filter_upwards [
    chebyshevCosineL2Equiv_apply 𝕜 (chebyshevTHilbertBasis 𝕜 n),
    measurePreserving_cos_chebyshev.quasiMeasurePreserving.ae_eq
      (coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n)] with θ hcos hmode
  change normalizedChebyshevTLp 𝕜 n (Real.cos θ) =
    (algebraMap ℝ 𝕜) (normalizedChebyshevT n (Real.cos θ)) at hmode
  rw [hcos, coe_chebyshevTHilbertBasis, hmode, normalizedChebyshevT_def,
    normalized_eval_T_real_cos_eq_normalizedChebyshevCosine]

end L2

end TauCeti
