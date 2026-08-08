/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation
public import TauCeti.Analysis.Normed.Module.Ball

/-!
# Ball normalizations for harmonic functions

The PDE roadmap's Lane C uses translations and dilations to reduce local arguments on a ball
`Metric.ball x r` to arguments on the unit ball. The files
`TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry` and
`TauCeti.Analysis.InnerProductSpace.Harmonic.Dilation` prove the underlying invariance of
harmonicity under translations and nonzero dilations. This file packages the corresponding
consumer forms for metric balls, using the generic set normalizations from
`TauCeti.Analysis.Normed.Module.Ball`.

The main statement is `harmonicOnNhd_comp_const_add_smul_ball_iff`: for `0 < r`, the
normalized function `y ↦ f (x + r • y)` is harmonic near the unit ball if and only if `f` is
harmonic near `Metric.ball x r`.

## Main declarations

* `TauCeti.harmonicOnNhd_comp_add_right_ball_zero_iff`: translation-normalized harmonicity
  on a ball.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_ball_radius_iff`: ball-level affine normalization
  by `y ↦ x + c • y` for nonzero scale `c`.
* `TauCeti.harmonicOnNhd_comp_const_add_smul_ball_iff`: the unit-ball specialization.
-/

public section

namespace TauCeti

open InnerProductSpace

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Harmonicity on a neighbourhood of `Metric.ball x (‖c‖ * r)` is equivalent to harmonicity
of `y ↦ f (x + c • y)` on a neighbourhood of `Metric.ball 0 r`, for nonzero scale `c`. -/
theorem harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x : E) {c : ℝ} (hc : c ≠ 0)
    (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + c • y)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x (‖c‖ * r)) := by
  rw [← preimage_smul_vadd_ball_norm x hc r]
  simpa only [vadd_eq_add, add_comm] using
    harmonicOnNhd_comp_const_add_smul_iff x hc (f := f) (s := Metric.ball x (‖c‖ * r))

/-- Translation-normalized harmonicity on a ball. The function `y ↦ f (y + x)` is harmonic
near the radius-`r` ball centered at `0` exactly when `f` is harmonic near the corresponding
ball centered at `x`. -/
theorem harmonicOnNhd_comp_add_right_ball_zero_iff (x : E) (r : ℝ) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (y + x)) (Metric.ball 0 r) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  simpa [one_smul, add_comm] using
    harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x := x) (c := 1) one_ne_zero r (f := f)

/-- Harmonicity on a neighbourhood of `Metric.ball x r` is equivalent to harmonicity of the
normalized function `y ↦ f (x + r • y)` on a neighbourhood of the unit ball. -/
theorem harmonicOnNhd_comp_const_add_smul_ball_iff (x : E) {r : ℝ} (hr : 0 < r) {f : E → F} :
    HarmonicOnNhd (fun y ↦ f (x + r • y)) (Metric.ball 0 1) ↔
      HarmonicOnNhd f (Metric.ball x r) := by
  simpa [Real.norm_of_nonneg hr.le] using
    harmonicOnNhd_comp_const_add_smul_ball_radius_iff (x := x) hr.ne' 1 (f := f)

end TauCeti
