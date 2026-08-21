/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Reciprocal building blocks are completely monotone

This file adds a second family of concrete completely monotone functions to the
`OneParameterSemigroups` roadmap, alongside the exponentials `t ↦ e^{-x t}` already in
`TauCeti.Analysis.CompletelyMonotone.Basic`: the **reciprocals of affine functions**
`t ↦ (a + t)⁻¹` with `a > 0`.

These are the resolvent kernels `t ↦ (λ + t)⁻¹` that Part A of the roadmap builds a semigroup
theory around, and they are among the basic Stieltjes (resolvent) kernels appearing in Stieltjes
representations. The acceptance example `t ↦ 1/(1 + t)` named in Part B of the roadmap is the
special case `a = 1`; its representing measure `e^{-x} dx` is the exponential distribution.

## Main declarations

* `TauCeti.isCompletelyMonotone_inv_const_add`: for `a > 0`, the reciprocal `t ↦ (a + t)⁻¹` is
  completely monotone.
* `TauCeti.isCompletelyMonotone_one_div_const_add`: the `t ↦ 1 / (a + t)` phrasing of the same
  resolvent kernel.
* `TauCeti.isCompletelyMonotone_one_div_one_add`: the roadmap acceptance example
  `t ↦ 1 / (1 + t)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff Nat

namespace TauCeti

/-- For `a > 0`, the reciprocal `t ↦ (a + t)⁻¹` is completely monotone. This is the resolvent
kernel `t ↦ (λ + t)⁻¹` of the roadmap's semigroup theory. -/
theorem isCompletelyMonotone_inv_const_add {a : ℝ} (ha : 0 < a) :
    IsCompletelyMonotone (fun t => (a + t)⁻¹) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < a + t := fun t ht => by linarith
  -- The denominator never vanishes on `[0, ∞)`, so the reciprocal is smooth there.
  have hsmooth : ContDiffOn ℝ ∞ (fun t : ℝ => (a + t)⁻¹) (Ici 0) :=
    ContDiffOn.inv (by fun_prop) fun x hx => (hpos x hx).ne'
  refine ⟨hsmooth, fun n t ht => ?_⟩
  have htpos : 0 < a + t := hpos t ht
  -- Reduce the derivative *within* `[0, ∞)` to the ordinary iterated derivative at `t`.
  have haff : ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => a + t) t := by fun_prop
  have hcat : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => (a + t)⁻¹) t :=
    (haff.inv htpos.ne').of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcat (mem_Ici.mpr ht)]
  -- The iterated derivative of `y ↦ y⁻¹` at a positive point, from Mathlib's open-set formula.
  have hform : ∀ s : ℝ, 0 < s → iteratedDeriv n (fun y : ℝ => y⁻¹) s
      = (-1) ^ n * (n ! : ℝ) * s ^ (-1 - n : ℤ) := by
    intro s hs
    have hmem : s ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hs
    have h1 := iteratedDerivWithin_one_div (s := Ioi (0 : ℝ)) n isOpen_Ioi hmem
    have h2 := iteratedDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun y : ℝ => 1 / y) (n := n)
      isOpen_Ioi hmem
    have e1 : iteratedDeriv n (fun y : ℝ => (1 : ℝ) / y) s
        = (-1) ^ n * (n ! : ℝ) * s ^ (-1 - n : ℤ) := by rw [← h2]; exact h1
    simpa [one_div] using e1
  -- Translation invariance: `t ↦ (a + t)⁻¹` is `y ↦ y⁻¹` shifted by `a`.
  have hcomp : iteratedDeriv n (fun t : ℝ => (a + t)⁻¹) t
      = iteratedDeriv n (fun y : ℝ => y⁻¹) (a + t) :=
    congrFun (iteratedDeriv_comp_const_add n (fun y : ℝ => y⁻¹) a) t
  rw [hcomp, hform (a + t) htpos]
  -- The sign: `(-1)ⁿ · (-1)ⁿ = ((-1)ⁿ)² ≥ 0`, and `n! · (a + t)^{-1-n} ≥ 0`.
  have hzpow : 0 ≤ (a + t) ^ (-1 - n : ℤ) := (zpow_pos htpos _).le
  have hrw : (-1 : ℝ) ^ n * ((-1) ^ n * (n ! : ℝ) * (a + t) ^ (-1 - n : ℤ))
      = ((-1 : ℝ) ^ n) ^ 2 * (n ! : ℝ) * (a + t) ^ (-1 - n : ℤ) := by ring
  rw [hrw]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hzpow

/-- For `a > 0`, the reciprocal `t ↦ 1 / (a + t)` is completely monotone. This is the `1 / (a + t)`
phrasing of the resolvent kernel `isCompletelyMonotone_inv_const_add`. -/
theorem isCompletelyMonotone_one_div_const_add {a : ℝ} (ha : 0 < a) :
    IsCompletelyMonotone (fun t => 1 / (a + t)) := by
  simpa only [one_div] using isCompletelyMonotone_inv_const_add ha

/-- The roadmap acceptance example: `t ↦ 1 / (1 + t)` is completely monotone. Its representing
measure under Bernstein's theorem is the exponential distribution `e^{-x} dx`. -/
theorem isCompletelyMonotone_one_div_one_add :
    IsCompletelyMonotone (fun t => 1 / (1 + t)) :=
  isCompletelyMonotone_one_div_const_add one_pos

end TauCeti
