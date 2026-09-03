/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Local inverse equations for the Banach algebra logarithm

This file proves that `NormedSpace.logOneAdd` and the exponential are inverse near the origin.
The proof first computes the corresponding formal series compositions over the reals and then
transports their scalar coefficients to an arbitrary real Banach algebra.
-/

public section

open Filter
open scoped Topology

noncomputable section

namespace NormedSpace

private def logCoeffs (n : ℕ) : ℝ := -(-1 : ℝ) ^ n / n

private theorem logOneAddSeries_eq_ofScalars (A : Type*) [NormedRing A]
    [NormedAlgebra ℝ A] :
    logOneAddSeries ℝ A = FormalMultilinearSeries.ofScalars A logCoeffs := by
  ext n v
  rw [logOneAddSeries_apply]
  simp only [FormalMultilinearSeries.ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  congr 1
  simp only [logCoeffs, pow_succ]
  ring

private theorem hasFPowerSeriesAt_real_logOneAdd :
    HasFPowerSeriesAt (fun x : ℝ ↦ Real.log (1 + x))
      (logOneAddSeries ℝ ℝ) 0 := by
  rw [logOneAddSeries_eq_ofScalars]
  have hcoeff : logCoeffs = fun n : ℕ ↦ -(-1 : ℝ) ^ n / n := by
    funext n
    rfl
  rw [hcoeff]
  exact hasFPowerSeriesAt_log_one_add

private def expSubOneSeries (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :
    FormalMultilinearSeries ℝ A A :=
  (expSeries ℝ A).removeZero

private theorem expSubOne_hasFPowerSeriesAt (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] :
    HasFPowerSeriesAt (fun x : A ↦ exp x - 1) (expSubOneSeries A) 0 := by
  have h := (exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := A)).sub
    (hasFPowerSeriesAt_const (𝕜 := ℝ) (E := A) (c := (1 : A)) (e := (0 : A)))
  convert h using 1
  · ext x
    rfl
  · ext n v
    cases n with
    | zero => simp [expSubOneSeries, expSeries_eq_ofScalars,
        FormalMultilinearSeries.ofScalars]
    | succ n => simp [expSubOneSeries, expSeries_eq_ofScalars,
        FormalMultilinearSeries.ofScalars]

private theorem logSeries_comp_expSeries_real :
    (logOneAddSeries ℝ ℝ).comp (expSeries ℝ ℝ) =
      FormalMultilinearSeries.id ℝ ℝ 0 := by
  have hlog' : HasFPowerSeriesAt (fun x : ℝ ↦ Real.log (1 + x))
      (logOneAddSeries ℝ ℝ) ((fun x : ℝ ↦ exp x - 1) 0) := by
    simpa only [exp_zero, sub_self] using hasFPowerSeriesAt_real_logOneAdd
  have hcomp : HasFPowerSeriesAt
      ((fun u : ℝ ↦ Real.log (1 + u)) ∘ (fun x : ℝ ↦ exp x - 1))
      ((logOneAddSeries ℝ ℝ).comp (expSubOneSeries ℝ)) 0 :=
    HasFPowerSeriesAt.comp (g := fun u : ℝ ↦ Real.log (1 + u))
      (f := fun x : ℝ ↦ exp x - 1) hlog' (expSubOne_hasFPowerSeriesAt ℝ)
  have hid := (ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt 0
  have hh := hcomp.eq_formalMultilinearSeries_of_eventually hid (by
    filter_upwards with x
    have harg : 1 + (Real.exp x - 1) = Real.exp x := by ring
    have hidApply : ContinuousLinearMap.id ℝ ℝ x = x :=
      ContinuousLinearMap.id_apply x
    simpa only [Function.comp_apply, ← Real.exp_eq_exp_ℝ, harg, hidApply] using
      Real.log_exp x)
  have hidseries : (ContinuousLinearMap.id ℝ ℝ).fpowerSeries 0 =
      FormalMultilinearSeries.id ℝ ℝ 0 := by
    rfl
  simpa only [expSubOneSeries, FormalMultilinearSeries.comp_removeZero, hidseries] using hh

private def idCoeffs (n : ℕ) : ℝ := if n = 1 then 1 else 0

private theorem id_eq_ofScalars (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :
    FormalMultilinearSeries.id ℝ A 0 =
      FormalMultilinearSeries.ofScalars A idCoeffs := by
  ext n v
  rcases n with _ | _ | n
  · simp [idCoeffs, FormalMultilinearSeries.ofScalars]
  · simp [idCoeffs, FormalMultilinearSeries.ofScalars]
  · simp [idCoeffs, FormalMultilinearSeries.ofScalars,
      FormalMultilinearSeries.id_apply_of_one_lt]

private theorem logSeries_comp_expSeries (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :
    (logOneAddSeries ℝ A).comp (expSeries ℝ A) =
      FormalMultilinearSeries.id ℝ A 0 := by
  rw [logOneAddSeries_eq_ofScalars, expSeries_eq_ofScalars,
    FormalMultilinearSeries.ofScalars_comp_ofScalars]
  rw [id_eq_ofScalars]
  apply congrArg (FormalMultilinearSeries.ofScalars A)
  have h := logSeries_comp_expSeries_real
  rw [logOneAddSeries_eq_ofScalars, expSeries_eq_ofScalars,
    FormalMultilinearSeries.ofScalars_comp_ofScalars, id_eq_ofScalars] at h
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ h

private def oneAddCoeffs (n : ℕ) : ℝ := if n = 0 ∨ n = 1 then 1 else 0

private theorem oneAdd_hasFPowerSeriesAt (A : Type*) [NormedRing A]
    [NormedAlgebra ℝ A] :
    HasFPowerSeriesAt (fun x : A ↦ 1 + x)
      (FormalMultilinearSeries.ofScalars A oneAddCoeffs) 0 := by
  have h := (hasFPowerSeriesAt_const (𝕜 := ℝ) (E := A) (c := (1 : A))
    (e := (0 : A))).add ((ContinuousLinearMap.id ℝ A).hasFPowerSeriesAt 0)
  convert h using 1
  · ext x
    rfl
  · ext n
    match n with
    | 0 => simp [oneAddCoeffs, FormalMultilinearSeries.ofScalars]
    | 1 => simp [oneAddCoeffs, FormalMultilinearSeries.ofScalars]
    | n + 2 => simp [oneAddCoeffs, FormalMultilinearSeries.ofScalars,
        ContinuousLinearMap.fpowerSeries]

private theorem expSeries_comp_logSeries_real :
    (expSeries ℝ ℝ).comp (logOneAddSeries ℝ ℝ) =
      FormalMultilinearSeries.ofScalars ℝ oneAddCoeffs := by
  have hexp := exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := ℝ)
  have hcomp : HasFPowerSeriesAt
      ((exp : ℝ → ℝ) ∘ fun x : ℝ ↦ Real.log (1 + x))
      ((expSeries ℝ ℝ).comp (logOneAddSeries ℝ ℝ)) 0 :=
    HasFPowerSeriesAt.comp (g := exp) (f := fun x : ℝ ↦ Real.log (1 + x))
      (by simpa using hexp) hasFPowerSeriesAt_real_logOneAdd
  apply hcomp.eq_formalMultilinearSeries_of_eventually (oneAdd_hasFPowerSeriesAt ℝ)
  have ht : ContinuousAt (fun x : ℝ ↦ 1 + x) 0 := by fun_prop
  have hpos : (0 : ℝ) < (fun x : ℝ ↦ 1 + x) 0 := by norm_num
  filter_upwards [ht.eventually (lt_mem_nhds hpos)] with x hx
  have hexpLog : Real.exp (Real.log (1 + x)) = 1 + x := Real.exp_log hx
  simpa only [Function.comp_apply, ← Real.exp_eq_exp_ℝ] using hexpLog

private theorem expSeries_comp_logSeries (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] :
    (expSeries ℝ A).comp (logOneAddSeries ℝ A) =
      FormalMultilinearSeries.ofScalars A oneAddCoeffs := by
  rw [expSeries_eq_ofScalars, logOneAddSeries_eq_ofScalars,
    FormalMultilinearSeries.ofScalars_comp_ofScalars]
  apply congrArg (FormalMultilinearSeries.ofScalars A)
  have h := expSeries_comp_logSeries_real
  rw [expSeries_eq_ofScalars, logOneAddSeries_eq_ofScalars,
    FormalMultilinearSeries.ofScalars_comp_ofScalars] at h
  exact FormalMultilinearSeries.ofScalars_series_injective ℝ ℝ h

/-- Near zero, taking `logOneAdd` after subtracting one from the exponential is the identity. -/
theorem eventually_logOneAdd_exp_sub_one (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] :
    ∀ᶠ x in 𝓝 (0 : A), logOneAdd ℝ A (exp x - 1) = x := by
  have hlog := hasFPowerSeriesOnBall_logOneAdd (𝕂 := ℝ) (A := A)
  have hlog' : HasFPowerSeriesAt (logOneAdd ℝ A) (logOneAddSeries ℝ A)
      ((fun x : A ↦ exp x - 1) 0) := by
    simpa only [exp_zero, sub_self] using hlog.hasFPowerSeriesAt
  have hcomp : HasFPowerSeriesAt
      ((logOneAdd ℝ A) ∘ fun x : A ↦ exp x - 1)
      ((logOneAddSeries ℝ A).comp (expSubOneSeries A)) 0 :=
    HasFPowerSeriesAt.comp (g := logOneAdd ℝ A) (f := fun x : A ↦ exp x - 1)
      hlog' (expSubOne_hasFPowerSeriesAt A)
  rw [expSubOneSeries, FormalMultilinearSeries.comp_removeZero,
    logSeries_comp_expSeries] at hcomp
  have hid := (ContinuousLinearMap.id ℝ A).hasFPowerSeriesAt 0
  have hzero := hcomp.sub hid
  have hidseries : (ContinuousLinearMap.id ℝ A).fpowerSeries 0 =
      FormalMultilinearSeries.id ℝ A 0 := by
    rfl
  have hseries : FormalMultilinearSeries.id ℝ A 0 -
      (ContinuousLinearMap.id ℝ A).fpowerSeries 0 = 0 := by
    rw [hidseries, sub_self]
  rw [hseries] at hzero
  filter_upwards [hzero.eventually_eq_zero] with x hx
  have hdiff : logOneAdd ℝ A (exp x - 1) - x = 0 := by
    simpa only [Pi.sub_apply, Function.comp_apply, ContinuousLinearMap.id_apply] using hx
  exact sub_eq_zero.mp hdiff

/-- Near zero, exponentiating `logOneAdd` recovers one plus the argument. -/
theorem eventually_exp_logOneAdd (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] :
    ∀ᶠ x in 𝓝 (0 : A), exp (logOneAdd ℝ A x) = 1 + x := by
  have hlog := (hasFPowerSeriesOnBall_logOneAdd (𝕂 := ℝ) (A := A)).hasFPowerSeriesAt
  have hexp : HasFPowerSeriesAt (exp : A → A) (expSeries ℝ A)
      ((logOneAdd ℝ A) 0) := by
    simpa only [logOneAdd_zero] using exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := A)
  have hcomp : HasFPowerSeriesAt ((exp : A → A) ∘ logOneAdd ℝ A)
      ((expSeries ℝ A).comp (logOneAddSeries ℝ A)) 0 := hexp.comp hlog
  rw [expSeries_comp_logSeries] at hcomp
  have hone := oneAdd_hasFPowerSeriesAt A
  have hzero := hcomp.sub hone
  rw [sub_self] at hzero
  filter_upwards [hzero.eventually_eq_zero] with x hx
  have hdiff : exp (logOneAdd ℝ A x) - (1 + x) = 0 := by
    simpa only [Pi.sub_apply, Function.comp_apply] using hx
  exact sub_eq_zero.mp hdiff

end NormedSpace
