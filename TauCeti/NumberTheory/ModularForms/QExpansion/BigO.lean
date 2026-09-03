/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# `q`-coefficient vanishing and cusp-function growth

The dictionary between vanishing of the first `N` `q`-coefficients of a periodic function
on `ℍ` and `O(‖q‖^N)` growth of its cusp function at `0`, in both directions, together with
the limit of the function's values along `Im τ → ∞`. The general layer asks only for
analyticity of the cusp function at `0` (with periodicity for the limit); the corollaries
specialize to modular forms. These are the analytic inputs of the norm step of the
general-level valence reduction: growth bounds are multiplicative, so they transport
coefficient vanishing through the norm map to level one.

## Main declarations

* `TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero` and
  `TauCeti.UpperHalfPlane.qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow`: the two
  directions of the dictionary, for any function whose cusp function is analytic at `0`.
* `TauCeti.UpperHalfPlane.tendsto_valueAtInfty`: an `h`-periodic function with cusp
  function analytic at `0` tends to `valueAtInfty` along `atImInfty`.
* The `TauCeti.ModularFormClass` corollaries of all three, for a modular form on a
  subgroup with `h` in its strict period set.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, the file
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/Auxiliary.lean`),
generalized to the function level and reproved through Mathlib's power-series uniqueness
machinery instead of the source's circle-integral bounds.
-/

open UpperHalfPlane Filter

open scoped Topology

namespace TauCeti.UpperHalfPlane

noncomputable section

variable {h : ℝ} {F : Type*} [FunLike F ℍ ℂ] {f : F}

/-- A function on `ℍ` that is `h`-periodic with cusp function analytic at `0` tends to
`valueAtInfty` along `atImInfty`. -/
public lemma tendsto_valueAtInfty (hh : 0 < h) (hper : Function.Periodic (⇑f ∘ ofComplex) h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) := by
  have ht : Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (cuspFunction h f 0)) := by
    refine Filter.Tendsto.congr (fun τ ↦ ?_)
      ((hfanalytic.continuousAt.tendsto).comp (qParam_tendsto_atImInfty hh))
    simpa using eq_cuspFunction τ hh.ne' hper
  simpa [cuspFunction_apply_zero hh hfanalytic hper] using ht

/-- The power series of the cusp function at `0` is the `q`-expansion. -/
private lemma hasFPowerSeriesAt_cuspFunction (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) :
    HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
  simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
    using hfanalytic.hasFPowerSeriesAt

/-- If the first `N` `q`-coefficients vanish, then the cusp function is `O(‖q‖^N)` near
`0`. -/
public lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) (N : ℕ)
    (hcoeff : ∀ n < N, (qExpansion h f).coeff n = 0) :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) := by
  have hps : (qExpansionFormalMultilinearSeries h f).partialSum N = 0 := by
    ext q
    exact Finset.sum_eq_zero fun n hn ↦ by
      simp [hcoeff n (by simpa [Finset.mem_range] using hn)]
  simpa [zero_add, hps] using
    (hasFPowerSeriesAt_cuspFunction hfanalytic).isBigO_sub_partialSum_pow N

/-- If `cuspFunction h f = O(‖q‖^N)` near `0`, then the `n`-th `q`-coefficient vanishes for
`n < N`. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hON : cuspFunction h f =O[𝓝 (0 : ℂ)] fun q : ℂ ↦ ‖q‖ ^ (n + 1) := by
    refine hO.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    simpa [abs_of_nonneg (norm_nonneg q)] using
      pow_le_pow_of_le_one (norm_nonneg q) (mem_ball_zero_iff.mp hq).le hn
  have hps : ∀ y : ℂ,
      (qExpansionFormalMultilinearSeries h f).partialSum (n + 1) y =
        y ^ n • (qExpansion h f).coeff n := by
    intro y
    rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_eq_zero
      (fun m hm ↦ by
        simp [ih m (Finset.mem_range.mp hm) ((Finset.mem_range.mp hm).trans hn)]),
      zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      qExpansionFormalMultilinearSeries_coeff]
  have hhom : (fun y : ℂ ↦ qExpansionFormalMultilinearSeries h f n fun _ ↦ y)
      =O[𝓝 (0 : ℂ)] fun y : ℂ ↦ ‖y‖ ^ (n + 1) := by
    have hsub := (hasFPowerSeriesAt_cuspFunction hfanalytic).isBigO_sub_partialSum_pow (n + 1)
    simp only [zero_add] at hsub
    refine (hON.sub hsub).congr_left fun y ↦ ?_
    rw [hps, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      qExpansionFormalMultilinearSeries_coeff]
    ring
  simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    qExpansionFormalMultilinearSeries_coeff] using
    hhom.continuousMultilinearMap_apply_eq_zero 1

end

end TauCeti.UpperHalfPlane

namespace TauCeti.ModularFormClass

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma tendsto_valueAtInfty [ModularFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto (fun τ : ℍ ↦ f τ) atImInfty (𝓝 (valueAtInfty f)) :=
  TauCeti.UpperHalfPlane.tendsto_valueAtInfty hh
    (SlashInvariantFormClass.periodic_comp_ofComplex (k := k) f hΓ)
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero (F := F) (k := k) (f := f) hh hΓ)

/-- If the first `N` `q`-coefficients of a modular form vanish, then its cusp function is
`O(‖q‖^N)` near `0`. -/
public lemma cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (N : ℕ)
    (hcoeff : ∀ n < N, (qExpansion h f).coeff n = 0) :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) :=
  TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero (F := F) (k := k) (f := f) hh hΓ)
    N hcoeff

/-- If the cusp function of a modular form is `O(‖q‖^N)` near `0`, then its `n`-th
`q`-coefficient vanishes for `n < N`. -/
public lemma qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N n : ℕ} (hn : n < N)
    (hO : cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N)) :
    (qExpansion h f).coeff n = 0 :=
  TauCeti.UpperHalfPlane.qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero (F := F) (k := k) (f := f) hh hΓ)
    hn hO

end TauCeti.ModularFormClass
