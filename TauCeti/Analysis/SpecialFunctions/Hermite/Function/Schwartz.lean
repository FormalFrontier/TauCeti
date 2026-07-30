/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder

/-!
# Hermite functions in Schwartz space

This file packages the real Hermite functions as Schwartz functions.  The construction first
shows directly that the Gaussian `x ↦ exp (-x² / 2)` is rapidly decreasing, using Mathlib's
formula for all of its derivatives in terms of Hermite polynomials.  Multiplication by the
polynomial factor then uses `SchwartzMap.smulLeftCLM`.

The resulting `hermiteSchwartzMap` has `hermiteFunction` as its underlying function.  The
pointwise position and derivative ladder relations are also recorded as equalities in Schwartz
space, so later constructions can use Mathlib's continuous operators on `𝓢(ℝ, ℝ)`.
-/

public section

namespace TauCeti

open Filter Polynomial Set Topology
open scoped SchwartzMap

private theorem tendsto_pow_mul_eval_mul_gaussian (p : ℝ[X]) (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * p.eval x * Real.exp (-(x ^ 2 / 2)))
      (cocompact ℝ) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [eval_add, mul_add, add_mul, zero_add] using hp.add hq
  | monomial n c =>
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
        (a := (1 / 2 : ℝ)) (by norm_num) (s := (k + n : ℕ))
      convert (by simpa only [mul_zero] using h.const_mul ‖c‖) using 1
      ext x
      simp only [eval_monomial, norm_mul, norm_pow, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.rpow_natCast]
      rw [pow_add]
      ring_nf

private noncomputable def gaussianSchwartzMap : 𝓢(ℝ, ℝ) where
  toFun x := Real.exp (-(x ^ 2 / 2))
  smooth' := Real.contDiff_exp.comp (((contDiff_id.pow 2).div_const 2).neg)
  decay' k n := by
    let p : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)
    let F : ℝ → ℝ := fun x =>
      x ^ k * (-1 : ℝ) ^ n * p.eval x * Real.exp (-(x ^ 2 / 2))
    have hp_eval (x : ℝ) : p.eval x = aeval x (hermite n) := by
      dsimp only [p]
      rw [aeval_def, algebraMap_int_eq, eval_map]
    have hF (x : ℝ) :
        F x = x ^ k * iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x := by
      rw [iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
      rw [← hp_eval]
      dsimp only [F]
      ring
    have hF_cont : Continuous F := by
      dsimp only [F, p]
      fun_prop
    have hF_zero : Tendsto F (cocompact ℝ) (𝓝 0) := by
      have h := tendsto_pow_mul_eval_mul_gaussian (C ((-1 : ℝ) ^ n) * p) k
      convert h using 1
      ext x
      simp only [F, eval_mul, eval_C]
      ring
    have hF_bounded : Bornology.IsBounded (Set.range F) :=
      (hF_zero.isCompact_insert_range_of_cocompact hF_cont).isBounded.subset
        (Set.subset_insert 0 (Set.range F))
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hF_bounded
    refine ⟨C, fun x => ?_⟩
    have hx := hC (F x) ⟨x, rfl⟩
    rw [hF, norm_mul, norm_pow] at hx
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hx

@[simp]
private theorem gaussianSchwartzMap_apply (x : ℝ) :
    gaussianSchwartzMap x = Real.exp (-(x ^ 2 / 2)) :=
  rfl

private theorem hasTemperateGrowth_hermiteFactor (n : ℕ) :
    Function.HasTemperateGrowth
      (fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n) /
        Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)) := by
  let p : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)
  have hp : Function.HasTemperateGrowth (fun x : ℝ => p.eval x) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [show (fun x : ℝ => (p + q).eval x) =
          (fun x : ℝ => p.eval x) + fun x : ℝ => q.eval x by
            funext x
            simp only [Pi.add_apply, eval_add]]
        exact hp.add hq
    | monomial k c =>
        rw [show (fun x : ℝ => (monomial k c).eval x) =
          (fun _ : ℝ => c) * (fun x : ℝ => x) ^ k by
            funext x
            simp only [Pi.mul_apply, Pi.pow_apply, eval_monomial]]
        exact (Function.HasTemperateGrowth.const c).mul
          (Function.HasTemperateGrowth.id'.pow k)
  have hcomp : Function.HasTemperateGrowth (fun x : ℝ => p.eval (x * Real.sqrt 2)) := by
    have haff : Function.HasTemperateGrowth (fun x : ℝ => x * Real.sqrt 2) :=
      Function.HasTemperateGrowth.id'.mul
        (Function.HasTemperateGrowth.const (Real.sqrt 2))
    simpa only [Function.comp_def] using hp.comp haff
  have heval (x : ℝ) :
      p.eval (x * Real.sqrt 2) = aeval (x * Real.sqrt 2) (hermite n) := by
    dsimp only [p]
    rw [aeval_def, algebraMap_int_eq, eval_map]
  have hfun :
      (fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n) /
          Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)) =
        (fun x : ℝ => p.eval (x * Real.sqrt 2)) *
          fun _ : ℝ => (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ := by
    funext x
    simp only [Pi.mul_apply, heval, div_eq_mul_inv]
  rw [hfun]
  exact hcomp.mul (Function.HasTemperateGrowth.const
    (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹)

/-- The `n`th Hermite function, as an element of the real Schwartz space `𝓢(ℝ, ℝ)`. -/
noncomputable def hermiteSchwartzMap (n : ℕ) : 𝓢(ℝ, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ
    (fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n) /
      Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))
    gaussianSchwartzMap

/-- The underlying function of `hermiteSchwartzMap n` is `hermiteFunction n`. -/
@[simp]
theorem hermiteSchwartzMap_apply (n : ℕ) (x : ℝ) :
    hermiteSchwartzMap n x = hermiteFunction n x := by
  rw [hermiteSchwartzMap, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_hermiteFactor n)]
  rw [gaussianSchwartzMap_apply, hermiteFunction_def]
  simp only [smul_eq_mul]
  ring

/-- The coercion of `hermiteSchwartzMap n` is the pointwise Hermite function. -/
@[simp]
theorem coe_hermiteSchwartzMap (n : ℕ) :
    ⇑(hermiteSchwartzMap n) = hermiteFunction n := by
  funext x
  exact hermiteSchwartzMap_apply n x

/-- The position ladder relation, as an equality in Schwartz space. -/
theorem mul_hermiteSchwartzMap (n : ℕ) :
    SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) (hermiteSchwartzMap n) =
      Real.sqrt (((n : ℝ) + 1) / 2) • hermiteSchwartzMap (n + 1) +
        Real.sqrt ((n : ℝ) / 2) • hermiteSchwartzMap (n - 1) := by
  ext x
  simpa only [SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    hermiteSchwartzMap_apply, add_apply, smul_apply, smul_eq_mul] using mul_hermiteFunction n x

/-- The derivative ladder relation, as an equality in Schwartz space. -/
theorem deriv_hermiteSchwartzMap (n : ℕ) :
    SchwartzMap.derivCLM ℝ ℝ (hermiteSchwartzMap n) =
      Real.sqrt ((n : ℝ) / 2) • hermiteSchwartzMap (n - 1) -
        Real.sqrt (((n : ℝ) + 1) / 2) • hermiteSchwartzMap (n + 1) := by
  ext x
  rw [SchwartzMap.derivCLM_apply, coe_hermiteSchwartzMap, deriv_hermiteFunction]
  simp only [sub_apply, smul_apply, hermiteSchwartzMap_apply, smul_eq_mul]

/-- The annihilation relation, as an equality in Schwartz space. -/
theorem mul_add_deriv_hermiteSchwartzMap (n : ℕ) :
    SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) (hermiteSchwartzMap n) +
        SchwartzMap.derivCLM ℝ ℝ (hermiteSchwartzMap n) =
      Real.sqrt (2 * (n : ℝ)) • hermiteSchwartzMap (n - 1) := by
  ext x
  simp only [add_apply, smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    SchwartzMap.derivCLM_apply, coe_hermiteSchwartzMap]
  simp only [hermiteSchwartzMap_apply, smul_eq_mul]
  rw [mul_add_deriv_hermiteFunction]

/-- The creation relation, as an equality in Schwartz space. -/
theorem mul_sub_deriv_hermiteSchwartzMap (n : ℕ) :
    SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x) (hermiteSchwartzMap n) -
        SchwartzMap.derivCLM ℝ ℝ (hermiteSchwartzMap n) =
      Real.sqrt (2 * ((n : ℝ) + 1)) • hermiteSchwartzMap (n + 1) := by
  ext x
  simp only [sub_apply, smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    SchwartzMap.derivCLM_apply, coe_hermiteSchwartzMap]
  simp only [hermiteSchwartzMap_apply, smul_eq_mul]
  rw [mul_sub_deriv_hermiteFunction]

end TauCeti
