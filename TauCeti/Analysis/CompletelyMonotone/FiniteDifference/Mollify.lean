/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Basic

/-!
# Smoothing a finite-difference completely monotone function

`TauCeti.IsDifferenceCompletelyMonotone.isCompletelyMonotone` upgrades the finite-difference sign
condition to genuine complete monotonicity, but only for a function that is already `C^∞`. This
file supplies the missing smoothing step without imposing any regularity beyond the difference
condition itself.

Averaging `f` against a smooth probability density supported in `(-ε, 0)`,
`g t = ∫ ψ s · f (t - s) ds`,
only ever evaluates `f` on `[t, t + ε]`, so on `[0, ∞)` it never leaves the half-line where the
hypothesis lives. The average is `C^∞` because it is a convolution with a smooth compactly
supported kernel, and every mixed forward difference of `g` is the same average of the
corresponding difference of `f`, so the sign condition passes to `g` verbatim. Since `f` is
nonincreasing, `g` is squeezed between `f (· + ε)` and `f`.

The outcome, `TauCeti.IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_forall_le`, is a
completely monotone `g` with `f (t + ε) ≤ g t ≤ f t` on `[0, ∞)`.

## Main declarations

* `TauCeti.IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_forall_le`: a function that
  is completely monotone in the finite-difference sense is squeezed between the shift
  `f (· + ε)` and `f` by a completely monotone function, for every `ε > 0`.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
-/

public section

open Set MeasureTheory Metric
open scoped ContDiff Convolution

namespace TauCeti

variable {f : ℝ → ℝ}

/-- Mixed forward differences of a locally integrable function remain locally integrable. -/
private theorem locallyIntegrable_fwdDiffList {F : ℝ → ℝ} (hF : LocallyIntegrable F volume)
    (l : List ℝ) : LocallyIntegrable (fwdDiffList l F) volume := by
  induction l with
  | nil => simpa using hF
  | cons h l ih =>
      have hshift : LocallyIntegrable (fun t => fwdDiffList l F (t + h)) volume := by
        have hmap : LocallyIntegrable (fwdDiffList l F)
            (Measure.map (Homeomorph.addRight h) volume) := by
          change LocallyIntegrable (fwdDiffList l F)
            (Measure.map (fun x : ℝ => x + h) volume)
          rw [map_add_right_eq_self]
          exact ih
        have := (locallyIntegrable_map_homeomorph (Homeomorph.addRight h)).mp hmap
        change LocallyIntegrable (fun t => fwdDiffList l F (t + h)) volume at this
        exact this
      change LocallyIntegrable (fun t => fwdDiffList l F (t + h) - fwdDiffList l F t) volume
      exact hshift.sub ih

/-- A mixed forward difference of a kernel average is the kernel average of the mixed forward
difference. -/
private theorem fwdDiffList_integral_kernel {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {F : ℝ → ℝ} (hF : LocallyIntegrable F volume)
    (l : List ℝ) (t : ℝ) :
    fwdDiffList l (fun u => ∫ s, ψ s * F (u - s)) t = ∫ s, ψ s * fwdDiffList l F (t - s) := by
  have hint : ∀ l : List ℝ, ∀ u : ℝ,
      Integrable (fun s => ψ s * fwdDiffList l F (u - s)) volume := by
    intro l u
    exact hψc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hψ
      (locallyIntegrable_fwdDiffList hF l) u
  induction l generalizing t with
  | nil => rfl
  | cons h l ih =>
      simp only [fwdDiffList_cons, fwdDiff]
      rw [ih (t + h), ih t, ← integral_sub (hint l (t + h)) (hint l t)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      have hts : t + h - s = t - s + h := by ring
      simp only [hts]
      ring

/-- Averaging against a nonnegative kernel supported in the negative half-line preserves complete
monotonicity in the finite-difference sense. -/
private theorem isDifferenceCompletelyMonotone_integral_kernel {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ s, 0 ≤ ψ s) (hsupp : ∀ s : ℝ, ψ s ≠ 0 → s < 0)
    {F : ℝ → ℝ} (hF : LocallyIntegrable F volume)
    (hFcm : IsDifferenceCompletelyMonotone F) :
    IsDifferenceCompletelyMonotone (fun u => ∫ s, ψ s * F (u - s)) := by
  intro l hl t ht
  rw [fwdDiffList_integral_kernel hψ hψc hF l t, ← integral_const_mul]
  refine integral_nonneg fun s => ?_
  rcases eq_or_ne (ψ s) 0 with h0 | h0
  · simp [h0]
  · have hsign := hFcm l hl (t - s) (by linarith [hsupp s h0])
    have key : (-1 : ℝ) ^ l.length * (ψ s * fwdDiffList l F (t - s))
        = ψ s * ((-1 : ℝ) ^ l.length * fwdDiffList l F (t - s)) := by ring
    rw [key]
    exact mul_nonneg (hψ0 s) hsign

/-- **Smoothing a finite-difference completely monotone function.** If all mixed forward
differences of `f` with nonnegative steps alternate in sign on `[0, ∞)`, then for every `ε > 0`
there is a genuinely completely monotone `g` with
`f (t + ε) ≤ g t ≤ f t` for `t ≥ 0`.

The function `g` is the average of `f` against a smooth probability density supported in
`(-ε, 0)`; smoothness comes from the convolution, the sign condition is inherited pointwise, and
the two-sided bound is monotonicity of `f`. -/
theorem IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_forall_le
    (hf : IsDifferenceCompletelyMonotone f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, IsCompletelyMonotone g ∧ ∀ t : ℝ, 0 ≤ t → f (t + ε) ≤ g t ∧ g t ≤ f t := by
  -- Extend `f` to the whole line by the constant value `f 0` on the left.
  set F : ℝ → ℝ := fun t => f (max t 0) with hFdef
  have hFeq : ∀ t : ℝ, 0 ≤ t → F t = f t := fun t ht => by simp only [hFdef, max_eq_left ht]
  have hFcm : IsDifferenceCompletelyMonotone F := hf.congr hFeq
  have hFanti : Antitone F := by
    intro a b hab
    exact hf.antitoneOn (mem_Ici.mpr (le_max_right a 0)) (mem_Ici.mpr (le_max_right b 0))
      (max_le_max hab le_rfl)
  have hFloc : LocallyIntegrable F volume := hFanti.locallyIntegrable
  -- A smooth probability density supported in `(-ε, 0)`.
  set φ : ContDiffBump (-(ε / 2) : ℝ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩ with hφdef
  set ψ : ℝ → ℝ := φ.normed volume with hψdef
  have hψcont : Continuous ψ := φ.continuous_normed
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s => φ.nonneg_normed s
  have hψint : ∫ s, ψ s = 1 := φ.integral_normed
  have hψi : Integrable ψ volume := hψcont.integrable_of_hasCompactSupport hψc
  have hsupp : ∀ s : ℝ, ψ s ≠ 0 → -ε < s ∧ s < 0 := by
    intro s hs
    have hmem : s ∈ Function.support ψ := hs
    rw [hψdef, φ.support_normed_eq] at hmem
    simp only [Metric.mem_ball, Real.dist_eq, hφdef, abs_lt] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  refine ⟨fun u => ∫ s, ψ s * F (u - s), ?_, fun t ht => ?_⟩
  · -- Smooth, hence completely monotone by the finite-difference characterization.
    have hconv : (fun u => ∫ s, ψ s * F (u - s))
        = ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] F := rfl
    have hsmooth : ContDiff ℝ ∞ fun u => ∫ s, ψ s * F (u - s) := by
      rw [hconv]
      exact hψc.contDiff_convolution_left _ φ.contDiff_normed hFloc
    exact (isDifferenceCompletelyMonotone_integral_kernel hψcont hψc hψ0
      (fun s hs => (hsupp s hs).2) hFloc hFcm).isCompletelyMonotone hsmooth.contDiffOn
  · -- The two-sided bound, from monotonicity of `F` and the normalization of `ψ`.
    have hintF : Integrable (fun s => ψ s * F (t - s)) volume :=
      hψc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hψcont hFloc t
    have hmass : ∀ c : ℝ, ∫ s, ψ s * c = c := by
      intro c
      rw [integral_mul_const, hψint, one_mul]
    constructor
    · have hle : ∀ s : ℝ, ψ s * F (t + ε) ≤ ψ s * F (t - s) := by
        intro s
        rcases eq_or_ne (ψ s) 0 with h0 | h0
        · simp [h0]
        · obtain ⟨hs1, hs2⟩ := hsupp s h0
          exact mul_le_mul_of_nonneg_left
            (hFcm.antitoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith))
              (by linarith)) (hψ0 s)
      calc f (t + ε) = ∫ s, ψ s * F (t + ε) := by
              rw [hmass, hFeq _ (by linarith)]
        _ ≤ ∫ s, ψ s * F (t - s) := integral_mono (hψi.mul_const _) hintF hle
    · have hle : ∀ s : ℝ, ψ s * F (t - s) ≤ ψ s * F t := by
        intro s
        rcases eq_or_ne (ψ s) 0 with h0 | h0
        · simp [h0]
        · obtain ⟨hs1, hs2⟩ := hsupp s h0
          exact mul_le_mul_of_nonneg_left
            (hFcm.antitoneOn (mem_Ici.mpr ht) (mem_Ici.mpr (by linarith)) (by linarith))
            (hψ0 s)
      calc ∫ s, ψ s * F (t - s) ≤ ∫ s, ψ s * F t := integral_mono hintF (hψi.mul_const _) hle
        _ = f t := by rw [hmass, hFeq t ht]

end TauCeti
