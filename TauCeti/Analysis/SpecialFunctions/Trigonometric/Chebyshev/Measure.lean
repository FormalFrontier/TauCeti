/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Real
import TauCeti.MeasureTheory.Function.BoundedSupportExponential
import Mathlib.Topology.Algebra.Polynomial

/-!
# Finite measure API for the Chebyshev `T` weight

This file records the finite-measure bookkeeping for Mathlib's Chebyshev
orthogonality measure `Polynomial.Chebyshev.measureT`, together with the
single normalization constant used by the roadmap's Chebyshev Hilbert-basis
target.

The main facts are that `measureT` has total mass `π`, hence is finite and
nonzero, and that the existing Mathlib orthogonality lemmas combine into one
Kronecker-delta statement with squared norms `π` in degree zero and `π / 2` in
positive degree.  The file also records `L²` membership of the normalized `T`
modes and the finite exponential moments used by the later Chebyshev
Hilbert-basis construction.

For finite-coordinate arguments, use `orthonormal_normalizedChebyshevTLp`
together with Mathlib's generic `Orthonormal` coordinate and finite linear
combination API.  This file intentionally keeps the Chebyshev-specific surface
to the normalized modes and their orthonormality.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

open scoped ENNReal

/-- The Chebyshev `T` orthogonality measure has total mass `π`. -/
lemma chebyshevMeasureT_univ :
    Polynomial.Chebyshev.measureT Set.univ = ENNReal.ofReal Real.pi := by
  have h := integral_eval_T_real_measureT_zero
  have hreal : Polynomial.Chebyshev.measureT.real Set.univ = Real.pi := by
    simpa using h
  have hfinite : Polynomial.Chebyshev.measureT Set.univ ≠ ∞ := by
    intro htop
    have hzero : Polynomial.Chebyshev.measureT.real Set.univ = 0 := by
      simp [Measure.real, htop]
    linarith [hreal, Real.pi_pos]
  rw [← MeasureTheory.ofReal_measureReal (μ := Polynomial.Chebyshev.measureT)
    (s := Set.univ) hfinite, hreal]

/-- Mathlib's Chebyshev `T` orthogonality measure is finite. -/
noncomputable instance chebyshevMeasureT.instIsFiniteMeasure :
    IsFiniteMeasure Polynomial.Chebyshev.measureT where
  measure_univ_lt_top := by
    rw [chebyshevMeasureT_univ]
    exact ENNReal.ofReal_lt_top

/-- The Chebyshev `T` orthogonality measure has positive total mass. -/
lemma chebyshevMeasureT_univ_pos : 0 < Polynomial.Chebyshev.measureT Set.univ := by
  rw [chebyshevMeasureT_univ]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

/-- Mathlib's Chebyshev `T` orthogonality measure is nonzero. -/
lemma chebyshevMeasureT_ne_zero : Polynomial.Chebyshev.measureT ≠ 0 :=
  Measure.measure_univ_pos.mp chebyshevMeasureT_univ_pos

/-- The squared `L²(measureT)` norm of the `n`th Chebyshev `T` polynomial. -/
noncomputable def chebyshevTNormSq (n : ℕ) : ℝ :=
  if n = 0 then Real.pi else Real.pi / 2

@[simp]
lemma chebyshevTNormSq_zero : chebyshevTNormSq 0 = Real.pi := by
  simp [chebyshevTNormSq]

@[simp]
lemma chebyshevTNormSq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    chebyshevTNormSq n = Real.pi / 2 := by
  simp [chebyshevTNormSq, hn]

/-- The squared norm constant for Chebyshev `T` polynomials is positive. -/
lemma chebyshevTNormSq_pos (n : ℕ) : 0 < chebyshevTNormSq n := by
  by_cases hn : n = 0
  · simp [hn, Real.pi_pos]
  · rw [chebyshevTNormSq_of_ne_zero hn]
    positivity

/-- The squared norm constant for Chebyshev `T` polynomials is nonzero. -/
lemma chebyshevTNormSq_ne_zero (n : ℕ) : chebyshevTNormSq n ≠ 0 :=
  ne_of_gt (chebyshevTNormSq_pos n)

/-- The diagonal Chebyshev `T` orthogonality integral, with the degree-zero and
positive-degree cases hidden behind one normalization constant. -/
lemma integral_eval_T_real_mul_self_measureT (n : ℕ) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      chebyshevTNormSq n := by
  by_cases hn : n = 0
  · subst hn
    exact integral_eval_T_real_mul_self_measureT_zero
  · rw [chebyshevTNormSq_of_ne_zero hn]
    exact integral_T_real_mul_self_measureT_of_ne_zero hn

/-- Chebyshev `T` orthogonality in the Kronecker-delta form expected by the
general orthogonality-to-Hilbert-basis bridge. -/
lemma integral_eval_T_real_mul_eval_T_real_measureT_eq_ite (m n : ℕ) :
    ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      if m = n then chebyshevTNormSq n else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_eval_T_real_mul_self_measureT]
  · simp [hmn, integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn]

/-! ### Exponential-moment consumer forms -/

/-- The Chebyshev `T` orthogonality measure is supported on `[-1, 1]`. -/
lemma ae_mem_Icc_measureT :
    ∀ᵐ x ∂Polynomial.Chebyshev.measureT, x ∈ Set.Icc (-1 : ℝ) 1 := by
  -- Across the `module` boundary, `measureT`'s restricted-measure definition is not
  -- unfoldable here.  Recover the support fact through the public `integral_measureT`
  -- API instead.
  rw [ae_iff]
  have hreal : Polynomial.Chebyshev.measureT.real (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    calc
      Polynomial.Chebyshev.measureT.real (Set.Icc (-1 : ℝ) 1)ᶜ
          = ∫ x, ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun _ => (1 : ℝ)) x)
              ∂Polynomial.Chebyshev.measureT := by
            rw [(integral_indicator_one (μ := Polynomial.Chebyshev.measureT)
              measurableSet_Icc.compl).symm]
            rfl
      _ = ∫ x in (-1 : ℝ)..1,
            ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun _ => (1 : ℝ)) x) *
              √(1 - x ^ 2)⁻¹ := by
            exact integral_measureT _
      _ = 0 := by
            have hzero : (fun x : ℝ =>
                ((Set.Icc (-1 : ℝ) 1)ᶜ.indicator (fun _ => (1 : ℝ)) x) *
                  √(1 - x ^ 2)⁻¹) =ᵐ[volume.restrict (Set.uIoc (-1 : ℝ) 1)] 0 := by
              refine ae_restrict_of_forall_mem measurableSet_uIoc fun x hx => ?_
              have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
                rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
                exact ⟨le_of_lt hx.1, hx.2⟩
              simp [hxIcc]
            rw [intervalIntegral.integral_congr_ae_restrict hzero]
            simp
  rw [Measure.real] at hreal
  exact ((ENNReal.toReal_eq_zero_iff _).1 hreal).resolve_right (by finiteness)

/-- Multiplication by an exponential absolute moment preserves `L¹(measureT)`.

This is the compact-support consumer form used by the Chebyshev completeness
argument. -/
lemma integrable_exp_mul_abs_smul_measureT {𝕜 β : Type*} [RCLike 𝕜] [NormedAddCommGroup β]
    [NormedSpace 𝕜 β] {g : ℝ → β} (a : ℝ) (hg : Integrable g Polynomial.Chebyshev.measureT) :
    Integrable (fun x : ℝ => (Real.exp (a * |x|) : 𝕜) • g x)
      Polynomial.Chebyshev.measureT := by
  exact Integrable.exp_abs_smul_of_ae_abs_le hg a 1 (by
    filter_upwards [ae_mem_Icc_measureT] with x hx
    exact abs_le.mpr hx)

/-! ### `L²` consumer forms -/

/-- The real normalized Chebyshev `T` mode, with squared norm one in `L²(measureT)`. -/
noncomputable def normalizedChebyshevT (n : ℕ) (x : ℝ) : ℝ :=
  (T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n)

/-- The defining equation for the real normalized Chebyshev `T` mode. -/
@[simp]
lemma normalizedChebyshevT_def (n : ℕ) (x : ℝ) :
    normalizedChebyshevT n x = (T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n) :=
  normalizedChebyshevT.eq_1 n x

/-- The real normalized Chebyshev `T` mode is continuous. -/
lemma continuous_normalizedChebyshevT (n : ℕ) :
    Continuous (normalizedChebyshevT n) :=
  ((T ℝ n).continuous.div_const _).congr fun x => (normalizedChebyshevT_def n x).symm

/-- The real normalized Chebyshev `T` mode lies in `L²(measureT)`. -/
lemma memLp_normalizedChebyshevT_measureT (n : ℕ) :
    MemLp (normalizedChebyshevT n) 2 Polynomial.Chebyshev.measureT := by
  have hcont : Continuous (normalizedChebyshevT n) := continuous_normalizedChebyshevT n
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  exact integrable_measureT (hcont.pow 2).continuousOn

/-- The scalar-cast normalized Chebyshev `T` mode lies in `L²(measureT)`, in
the form consumed by the family-generic orthogonality-to-Hilbert-basis bridge. -/
lemma memLp_algebraMap_normalizedChebyshevT_measureT {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedChebyshevT n x)) 2
      Polynomial.Chebyshev.measureT := by
  simpa only [← RCLike.algebraMap_eq_ofReal] using
    (memLp_normalizedChebyshevT_measureT n).ofReal (K := 𝕜)

/-- The normalized Chebyshev `T` mode as a vector of `L²(measureT)`. -/
noncomputable def normalizedChebyshevTLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Lp 𝕜 2 Polynomial.Chebyshev.measureT :=
  (memLp_algebraMap_normalizedChebyshevT_measureT (𝕜 := 𝕜) n).toLp _

/-- The `Lp` representative of the normalized Chebyshev `T` mode is the expected scalar-cast
function. -/
lemma coeFn_normalizedChebyshevTLp {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    ⇑(normalizedChebyshevTLp 𝕜 n) =ᵐ[Polynomial.Chebyshev.measureT]
      fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) :=
  MemLp.coeFn_toLp _

/-- The real `measureT` integral of two normalized Chebyshev `T` modes is the Kronecker
delta. -/
@[simp]
lemma integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite (m n : ℕ) :
    ∫ x, normalizedChebyshevT m x * normalizedChebyshevT n x
        ∂Polynomial.Chebyshev.measureT = if m = n then 1 else 0 := by
  have hmpos := chebyshevTNormSq_pos m
  have hnpos := chebyshevTNormSq_pos n
  calc
    ∫ x, normalizedChebyshevT m x * normalizedChebyshevT n x
        ∂Polynomial.Chebyshev.measureT
        = (Real.sqrt (chebyshevTNormSq m) * Real.sqrt (chebyshevTNormSq n))⁻¹ *
            ∫ x, (T ℝ m).eval x * (T ℝ n).eval x
              ∂Polynomial.Chebyshev.measureT := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [normalizedChebyshevT_def, normalizedChebyshevT_def]
          field_simp [normalizedChebyshevT_def, Real.sqrt_ne_zero'.mpr hmpos,
            Real.sqrt_ne_zero'.mpr hnpos]
    _ = if m = n then 1 else 0 := by
          rw [integral_eval_T_real_mul_eval_T_real_measureT_eq_ite]
          by_cases hmn : m = n
          · subst hmn
            rw [if_pos rfl, if_pos rfl]
            field_simp [Real.sqrt_ne_zero'.mpr hnpos]
            rw [Real.sq_sqrt hnpos.le]
          · rw [if_neg hmn, if_neg hmn, mul_zero]

/-- The normalized Chebyshev `T` modes have Kronecker-delta inner products in `L²(measureT)`. -/
@[simp]
lemma inner_normalizedChebyshevTLp {𝕜 : Type*} [RCLike 𝕜] (m n : ℕ) :
    inner 𝕜 (normalizedChebyshevTLp 𝕜 m) (normalizedChebyshevTLp 𝕜 n) =
      if m = n then 1 else 0 := by
  have hinner : ∀ a b : ℝ,
      inner 𝕜 ((algebraMap ℝ 𝕜) a) ((algebraMap ℝ 𝕜) b) =
        (algebraMap ℝ 𝕜) (a * b) := by
    intro a b
    simp [RCLike.inner_apply, RCLike.conj_ofReal, map_mul, mul_comm]
  calc
    inner 𝕜 (normalizedChebyshevTLp 𝕜 m) (normalizedChebyshevTLp 𝕜 n)
        = ∫ x, (algebraMap ℝ 𝕜) (normalizedChebyshevT m x * normalizedChebyshevT n x)
            ∂Polynomial.Chebyshev.measureT := by
          rw [MeasureTheory.L2.inner_def]
          refine integral_congr_ae ?_
          filter_upwards [coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) m,
            coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n] with x hxm hxn
          rw [hxm, hxn]
          exact hinner (normalizedChebyshevT m x) (normalizedChebyshevT n x)
    _ = if m = n then 1 else 0 :=
          by
            rw [integral_ofReal,
              integral_normalizedChebyshevT_mul_normalizedChebyshevT_measureT_eq_ite]
            by_cases hmn : m = n <;> simp [hmn]

/-- The normalized Chebyshev `T` modes have Kronecker-delta inner products in real
`L²(measureT)`. -/
lemma inner_normalizedChebyshevTLp_real (m n : ℕ) :
    inner ℝ (normalizedChebyshevTLp ℝ m) (normalizedChebyshevTLp ℝ n) =
      if m = n then 1 else 0 :=
  inner_normalizedChebyshevTLp (𝕜 := ℝ) m n

/-- The normalized Chebyshev `T` modes form an orthonormal family in `L²(measureT)`. -/
lemma orthonormal_normalizedChebyshevTLp {𝕜 : Type*} [RCLike 𝕜] :
    Orthonormal 𝕜 (normalizedChebyshevTLp 𝕜) := by
  rw [orthonormal_iff_ite]
  exact inner_normalizedChebyshevTLp

/-- The normalized Chebyshev `T` modes form an orthonormal family in real `L²(measureT)`. -/
lemma orthonormal_normalizedChebyshevTLp_real :
    Orthonormal ℝ (normalizedChebyshevTLp ℝ) :=
  orthonormal_normalizedChebyshevTLp (𝕜 := ℝ)

end TauCeti
