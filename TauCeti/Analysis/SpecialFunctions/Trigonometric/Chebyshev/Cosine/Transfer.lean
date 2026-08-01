/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Chebyshev `T` transfer to the cosine side

This file packages the cosine-side consequences of Mathlib's change-of-variables identity
`Polynomial.Chebyshev.integral_measureT_eq_integral_cos`. It provides the one-dimensional
integral API, the equivalence between the Chebyshev and angular measures, and the induced
`L²` equivalence under `x = cos θ`. The roadmap's Chebyshev Hilbert-basis target uses this
infrastructure to identify the normalized Chebyshev functions on `measureT` with the cosine basis.

## Main declarations

* `TauCeti.chebyshevAngleMeasure` is Lebesgue measure restricted to `(0, π]`.
* `TauCeti.chebyshevCosineL2Equiv` pulls an `L²(measureT)` function back along `Real.cos`.
* `TauCeti.normalizedChebyshevCosine` is the normalized angular cosine mode.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

/-- Lebesgue measure on the angular interval `(0, π]`. The choice of half-open endpoints matches
`intervalIntegral.integral_of_le`; changing either endpoint does not change the measure. -/
noncomputable def chebyshevAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc 0 Real.pi)

/-- The angular Chebyshev measure is Lebesgue measure restricted to `(0, π]`. -/
theorem chebyshevAngleMeasure_def :
    chebyshevAngleMeasure = volume.restrict (Set.Ioc 0 Real.pi) :=
  chebyshevAngleMeasure.eq_1

/-- Integrating against `chebyshevAngleMeasure` is interval integration from `0` to `π`. -/
theorem integral_chebyshevAngleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ θ, f θ ∂chebyshevAngleMeasure = ∫ θ in (0)..Real.pi, f θ := by
  rw [chebyshevAngleMeasure_def, intervalIntegral.integral_of_le Real.pi_nonneg]

/-- The pushforward of angular Lebesgue measure under `cos` is the Chebyshev measure. -/
theorem map_cos_chebyshevAngleMeasure :
    Measure.map Real.cos chebyshevAngleMeasure = measureT := by
  letI : IsFiniteMeasure chebyshevAngleMeasure := by
    rw [chebyshevAngleMeasure_def]
    infer_instance
  letI : Measure.InnerRegular chebyshevAngleMeasure := by
    rw [chebyshevAngleMeasure_def]
    infer_instance
  letI : Measure.InnerRegular (Measure.map Real.cos chebyshevAngleMeasure) :=
    Measure.InnerRegular.map_of_continuous Real.continuous_cos
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  -- Riesz--Markov extensionality presents `f` as a compactly supported map; exposing its
  -- underlying continuous map lets the standard integral-map and Chebyshev identities rewrite.
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

variable (𝕜 : Type*) [NormedRing 𝕜]

private noncomputable def chebyshevCosineL2Isometry :
    Lp 𝕜 2 measureT →ₗᵢ[𝕜] Lp 𝕜 2 chebyshevAngleMeasure :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Real.cos measurePreserving_cos_chebyshev

private noncomputable def chebyshevArccosL2LinearMap :
    Lp 𝕜 2 chebyshevAngleMeasure →ₗ[𝕜] Lp 𝕜 2 measureT :=
  Lp.compMeasurePreservingₗ 𝕜 Real.arccos measurePreserving_arccos_chebyshev

private theorem chebyshevCosineL2Isometry_toLinearMap_apply (f : Lp 𝕜 2 measureT) :
    (chebyshevCosineL2Isometry 𝕜).toLinearMap f =
      Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev f := by
  -- Mathlib has no application lemma for `compMeasurePreservingₗᵢ`; its stored linear map is
  -- definitionally `compMeasurePreservingₗ`, whose generated application lemma is stable.
  change Lp.compMeasurePreservingₗ 𝕜 Real.cos measurePreserving_cos_chebyshev f =
    Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev f
  rw [Lp.compMeasurePreservingₗ_apply]
  exact congrFun
    (AddHom.toFun_eq_coe
      (Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev).toAddHom) f

private theorem chebyshevCosineL2Isometry_apply (f : Lp 𝕜 2 measureT) :
    chebyshevCosineL2Isometry 𝕜 f =
      Lp.compMeasurePreserving Real.cos measurePreserving_cos_chebyshev f :=
  chebyshevCosineL2Isometry_toLinearMap_apply 𝕜 f

private theorem chebyshevArccosL2LinearMap_apply (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    chebyshevArccosL2LinearMap 𝕜 f =
      Lp.compMeasurePreserving Real.arccos measurePreserving_arccos_chebyshev f := by
  rw [chebyshevArccosL2LinearMap, Lp.compMeasurePreservingₗ_apply]
  exact congrFun
    (AddHom.toFun_eq_coe
      (Lp.compMeasurePreserving Real.arccos measurePreserving_arccos_chebyshev).toAddHom) f

private theorem chebyshevCosineL2Isometry_comp_arccos :
    (chebyshevCosineL2Isometry 𝕜).toLinearMap.comp (chebyshevArccosL2LinearMap 𝕜) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [chebyshevCosineL2Isometry_toLinearMap_apply, chebyshevArccosL2LinearMap_apply]
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_arccos_chebyshev
    measurePreserving_cos_chebyshev]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving f
      (measurePreserving_arccos_chebyshev.comp measurePreserving_cos_chebyshev),
    arccos_comp_cos_ae] with θ hcomp hinv
  exact hcomp.trans (by
    simpa only [Function.comp_apply, id_eq] using congrArg (fun x => f x) hinv)

private theorem chebyshevArccosL2LinearMap_comp_cosine :
    (chebyshevArccosL2LinearMap 𝕜).comp (chebyshevCosineL2Isometry 𝕜).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [chebyshevArccosL2LinearMap_apply, chebyshevCosineL2Isometry_toLinearMap_apply]
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_cos_chebyshev
    measurePreserving_arccos_chebyshev]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving f
      (measurePreserving_cos_chebyshev.comp measurePreserving_arccos_chebyshev),
    cos_comp_arccos_ae] with x hcomp hinv
  exact hcomp.trans (by
    simpa only [Function.comp_apply, id_eq] using congrArg (fun y => f y) hinv)

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
  by
    rw [chebyshevCosineL2Equiv, LinearIsometryEquiv.coe_ofLinearIsometry,
      chebyshevCosineL2Isometry_apply]
    exact Lp.coeFn_compMeasurePreserving f measurePreserving_cos_chebyshev

/-- The inverse Chebyshev-to-cosine equivalence is composition with `Real.arccos`. -/
theorem chebyshevCosineL2Equiv_symm_apply (f : Lp 𝕜 2 chebyshevAngleMeasure) :
    ⇑((chebyshevCosineL2Equiv 𝕜).symm f) =ᵐ[measureT] fun x => f (Real.arccos x) :=
  by
    rw [chebyshevCosineL2Equiv, LinearIsometryEquiv.coe_ofLinearIsometry_symm,
      chebyshevArccosL2LinearMap_apply]
    exact Lp.coeFn_compMeasurePreserving f measurePreserving_arccos_chebyshev

end L2

/-- The cosine-side representative corresponding to the Chebyshev polynomial `Tₙ`. -/
noncomputable def chebyshevCosine (n : ℕ) (θ : ℝ) : ℝ :=
  Real.cos (n * θ)

/-- The defining equation for the cosine-side Chebyshev representative. -/
lemma chebyshevCosine_def (n : ℕ) (θ : ℝ) : chebyshevCosine n θ = Real.cos (n * θ) :=
  chebyshevCosine.eq_1 n θ

@[simp]
lemma chebyshevCosine_zero (θ : ℝ) : chebyshevCosine 0 θ = 1 := by
  simp [chebyshevCosine_def]

@[simp]
lemma chebyshevCosine_one (θ : ℝ) : chebyshevCosine 1 θ = Real.cos θ := by
  simp [chebyshevCosine_def]

/-- Chebyshev polynomials restrict along `x = cos θ` to the cosine functions. -/
lemma eval_T_real_cos_eq_chebyshevCosine (n : ℕ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) = chebyshevCosine n θ := by
  simp [chebyshevCosine_def, Polynomial.Chebyshev.T_real_cos]

/-- The cosine-side representatives are continuous. -/
lemma continuous_chebyshevCosine (n : ℕ) : Continuous (chebyshevCosine n) := by
  have h : Continuous (fun θ : ℝ => Real.cos ((n : ℝ) * θ)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  exact h.congr fun θ => (chebyshevCosine_def n θ).symm

/-- Transfer a single Chebyshev `T` integral from `measureT` to the angular
cosine-side integral. -/
lemma integral_eval_T_real_measureT_eq_integral_chebyshevCosine (n : ℕ) :
    ∫ x, (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, chebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [chebyshevCosine_def]

/-- Transfer a product of two Chebyshev `T` polynomials from `measureT` to the
angular cosine-side integral. -/
lemma integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul (m n : ℕ) :
    ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [chebyshevCosine_def]

/-- The cosine-side integral of the constant Chebyshev mode. -/
lemma integral_chebyshevCosine_zero :
    ∫ θ in (0)..Real.pi, chebyshevCosine 0 θ = Real.pi := by
  rw [← integral_eval_T_real_measureT_eq_integral_chebyshevCosine]
  exact integral_eval_T_real_measureT_zero

/-- Nonzero cosine modes have zero integral over `[0, π]`. -/
lemma integral_chebyshevCosine_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ θ in (0)..Real.pi, chebyshevCosine n θ = 0 := by
  rw [← integral_eval_T_real_measureT_eq_integral_chebyshevCosine]
  exact integral_eval_T_real_measureT_of_ne_zero (by exact_mod_cast hn)

/-- The diagonal cosine-side `L²` integral, using the same squared-norm
constant as the Chebyshev `T` polynomials. -/
lemma integral_chebyshevCosine_mul_self (n : ℕ) :
    ∫ θ in (0)..Real.pi, chebyshevCosine n θ * chebyshevCosine n θ =
      chebyshevTNormSq n := by
  rw [← integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul]
  exact integral_eval_T_real_mul_self_measureT n

/-- Off-diagonal cosine modes are orthogonal over `[0, π]`. -/
lemma integral_chebyshevCosine_mul_chebyshevCosine_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ = 0 := by
  rw [← integral_eval_T_real_mul_eval_T_real_measureT_eq_integral_chebyshevCosine_mul]
  exact integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn

/-- Cosine-side Chebyshev orthogonality in the Kronecker-delta form expected by
the later Chebyshev Hilbert-basis construction. -/
lemma integral_chebyshevCosine_mul_chebyshevCosine_eq_ite (m n : ℕ) :
    ∫ θ in (0)..Real.pi, chebyshevCosine m θ * chebyshevCosine n θ =
      if m = n then chebyshevTNormSq n else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_chebyshevCosine_mul_self]
  · simp [hmn, integral_chebyshevCosine_mul_chebyshevCosine_of_ne hmn]

/-! ### Normalized cosine modes -/

/-- The normalized angular cosine mode corresponding to the normalized Chebyshev `Tₙ` mode. -/
noncomputable def normalizedChebyshevCosine (n : ℕ) (θ : ℝ) : ℝ :=
  chebyshevCosine n θ / Real.sqrt (chebyshevTNormSq n)

/-- The defining equation for the normalized angular cosine representative. -/
lemma normalizedChebyshevCosine_def (n : ℕ) (θ : ℝ) :
    normalizedChebyshevCosine n θ =
      chebyshevCosine n θ / Real.sqrt (chebyshevTNormSq n) :=
  normalizedChebyshevCosine.eq_1 n θ

@[simp]
lemma normalizedChebyshevCosine_zero (θ : ℝ) :
    normalizedChebyshevCosine 0 θ = 1 / Real.sqrt Real.pi := by
  simp [normalizedChebyshevCosine_def]

@[simp high]
lemma normalizedChebyshevCosine_one (θ : ℝ) :
    normalizedChebyshevCosine 1 θ = Real.cos θ / Real.sqrt (Real.pi / 2) := by
  simp [normalizedChebyshevCosine_def]

@[simp]
lemma normalizedChebyshevCosine_of_ne_zero {n : ℕ} (hn : n ≠ 0) (θ : ℝ) :
    normalizedChebyshevCosine n θ = Real.cos (n * θ) / Real.sqrt (Real.pi / 2) := by
  simp [normalizedChebyshevCosine_def, chebyshevCosine_def, chebyshevTNormSq_of_ne_zero hn]

/-- The normalized angular Chebyshev representatives are continuous. -/
lemma continuous_normalizedChebyshevCosine (n : ℕ) :
    Continuous (normalizedChebyshevCosine n) :=
  (continuous_chebyshevCosine n).div_const _

/-- Pulling back a normalized Chebyshev `T` polynomial along `x = cos θ` gives the normalized
angular cosine mode. -/
lemma normalized_eval_T_real_cos_eq_normalizedChebyshevCosine (n : ℕ) (θ : ℝ) :
    (T ℝ n).eval (Real.cos θ) / Real.sqrt (chebyshevTNormSq n) =
      normalizedChebyshevCosine n θ := by
  rw [eval_T_real_cos_eq_chebyshevCosine]
  simp [normalizedChebyshevCosine_def]

/-- Transfer a product of normalized Chebyshev `T` polynomials from `measureT` to the normalized
angular cosine-side integral. -/
lemma integral_normalized_eval_T_real_mul_measureT_eq_integral_normalizedChebyshevCosine_mul
    (m n : ℕ) :
    ∫ x, ((T ℝ m).eval x / Real.sqrt (chebyshevTNormSq m)) *
        ((T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n)) ∂Polynomial.Chebyshev.measureT =
      ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ *
        normalizedChebyshevCosine n θ := by
  rw [integral_measureT_eq_integral_cos]
  simp [normalizedChebyshevCosine_def, chebyshevCosine_def]

/-- The diagonal normalized angular cosine modes have integral one over `[0, π]`. -/
lemma integral_normalizedChebyshevCosine_mul_self (n : ℕ) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine n θ * normalizedChebyshevCosine n θ = 1 := by
  have hfun : (fun θ : ℝ => normalizedChebyshevCosine n θ * normalizedChebyshevCosine n θ) =
      fun θ : ℝ => (Real.sqrt (chebyshevTNormSq n) * Real.sqrt (chebyshevTNormSq n))⁻¹ *
        (chebyshevCosine n θ * chebyshevCosine n θ) := by
    funext θ
    simp only [normalizedChebyshevCosine_def]
    field_simp [(Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos n)]
  rw [hfun, intervalIntegral.integral_const_mul, integral_chebyshevCosine_mul_self]
  have hsqrt : Real.sqrt (chebyshevTNormSq n) * Real.sqrt (chebyshevTNormSq n) =
      chebyshevTNormSq n := by
    rw [← sq, Real.sq_sqrt (chebyshevTNormSq_pos n).le]
  rw [hsqrt]
  field_simp [chebyshevTNormSq_ne_zero n]

/-- Distinct normalized angular cosine modes are orthogonal over `[0, π]`. -/
lemma integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_of_ne {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ = 0 := by
  have hfun : (fun θ : ℝ => normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ) =
      fun θ : ℝ => (Real.sqrt (chebyshevTNormSq m) * Real.sqrt (chebyshevTNormSq n))⁻¹ *
        (chebyshevCosine m θ * chebyshevCosine n θ) := by
    funext θ
    simp only [normalizedChebyshevCosine_def]
    field_simp [(Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos m),
      (Real.sqrt_ne_zero').mpr (chebyshevTNormSq_pos n)]
  rw [hfun, intervalIntegral.integral_const_mul,
    integral_chebyshevCosine_mul_chebyshevCosine_of_ne hmn, mul_zero]

/-- Normalized angular Chebyshev-cosine orthogonality in Kronecker-delta form. -/
lemma integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_eq_ite (m n : ℕ) :
    ∫ θ in (0)..Real.pi, normalizedChebyshevCosine m θ * normalizedChebyshevCosine n θ =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_normalizedChebyshevCosine_mul_self]
  · simp [hmn, integral_normalizedChebyshevCosine_mul_normalizedChebyshevCosine_of_ne hmn]

end TauCeti
