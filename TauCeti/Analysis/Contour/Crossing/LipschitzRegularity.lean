/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The `C^{1,1}` crossing-regularity hypothesis

This file defines `HasLipschitzDerivOnEachSideAt`, the one-sided-Lipschitz-derivative regularity
condition a crossing needs for the real winding integrand to stay bounded there
(`Winding.LipschitzBoundedIntegrand`), and its introduction/elimination API. The predicate itself
is integrand-independent -- purely a statement about `derivWithin γ` on each side of `t` -- so it
is kept separate from the integrand-specific boundedness result it feeds.

## Main results

* `Contour.HasLipschitzDerivOnEachSideAt` -- `derivWithin γ` is Lipschitz on a one-sided closed
  window ending or starting at `t`, on each side (a `KR`/`εR`-window to the right, a `KL`/`εL`-
  window to the left) -- the two sides need not agree, so `t` may coincide with a breakpoint of
  the immersion.
* `Contour.hasLipschitzDerivOnEachSideAt_iff` -- its characteristic elimination/introduction iff.
* `Contour.hasLipschitzDerivOnEachSideAt_of_lipschitzOnWith` -- introduces it from one-sided
  `C^{1,1}` data on arbitrary pieces.
* `Contour.hasLipschitzDerivOnEachSideAt_of_contDiffOn` -- introduces it from `C²` data.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

open scoped NNReal

/-- **The `C^{1,1}` crossing-regularity hypothesis**: `derivWithin γ` is Lipschitz on a one-sided
closed window ending or starting at `t`, on each side (a `KR`/`εR`-window to the right, a
`KL`/`εL`-window to the left) — the two sides need not agree, so `t` may coincide with a
breakpoint of the immersion. Packages the hypotheses of `Winding.LipschitzBoundedIntegrand`'s
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner`. An opaque
`def`, not an `abbrev`: consumers destructure it via `hasLipschitzDerivOnEachSideAt_iff`
below rather than unfolding it directly. -/
def HasLipschitzDerivOnEachSideAt (γ : ℝ → ℂ) (t : ℝ) : Prop :=
  ∃ εR > 0, ∃ KR : ℝ≥0,
    DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
      (Icc t (t + εR)) ∧
    ∃ εL > 0, ∃ KL : ℝ≥0,
    DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
      (Icc (t - εL) t)

/-- **The characteristic iff for `HasLipschitzDerivOnEachSideAt`.** Equates the opaque `def` above
with its displayed one-sided witness proposition, exposing the `εR`/`KR`-window to the right and
the `εL`/`KL`-window to the left as a plain nested existential -- the introduction/elimination
interface a caller (e.g. via `choose!`) uses to name the witnesses, or to build the predicate from
them directly, rather than unfolding the `def`. -/
@[simp] theorem hasLipschitzDerivOnEachSideAt_iff {γ : ℝ → ℂ} {t : ℝ} :
    HasLipschitzDerivOnEachSideAt γ t ↔
    ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t) :=
  Iff.rfl

/-- **Introducing `HasLipschitzDerivOnEachSideAt` from one-sided `C^{1,1}` data on arbitrary
pieces.** If `γ` is differentiable with Lipschitz `derivWithin` on `[c, t]` and on `[t, d]`, `t`
itself has a Lipschitz derivative on each side -- the defining `εR`/`εL`-windows are just these
same pieces, `εR := d - t` and `εL := t - c`. A caller whose one-sided pieces are wider than it
ultimately needs can restrict along `DifferentiableOn.mono`/`LipschitzOnWith.mono` first, since
both hypotheses are monotone in the underlying set. -/
theorem hasLipschitzDerivOnEachSideAt_of_lipschitzOnWith {γ : ℝ → ℂ} {c t d : ℝ} {KR KL : ℝ≥0}
    (hct : c < t) (htd : t < d) (hdiffR : DifferentiableOn ℝ γ (Icc t d))
    (hlipR : LipschitzOnWith KR (derivWithin γ (Icc t d)) (Icc t d))
    (hdiffL : DifferentiableOn ℝ γ (Icc c t))
    (hlipL : LipschitzOnWith KL (derivWithin γ (Icc c t)) (Icc c t)) :
    HasLipschitzDerivOnEachSideAt γ t := by
  refine ⟨d - t, by linarith, KR, ?_, ?_, t - c, by linarith, KL, ?_, ?_⟩ <;>
    simpa only [add_sub_cancel, sub_sub_cancel]

/-- **Introducing `HasLipschitzDerivOnEachSideAt` from `C²` data.** A `γ` twice differentiable on
a two-sided neighborhood `[t - ε, t + ε]` of `t` has, on each half, a `C¹` (hence locally
Lipschitz, and Lipschitz on the compact half itself) `derivWithin` -- the natural route to
`HasLipschitzDerivOnEachSideAt` for a curve with an honest second derivative at a crossing, as
opposed to the merely `C^{1,1}` corner case this predicate was built to also cover. -/
theorem hasLipschitzDerivOnEachSideAt_of_contDiffOn {γ : ℝ → ℂ} {t ε : ℝ} (hε : 0 < ε)
    (hγ : ContDiffOn ℝ 2 γ (Icc (t - ε) (t + ε))) : HasLipschitzDerivOnEachSideAt γ t := by
  have hγR : ContDiffOn ℝ 2 γ (Icc t (t + ε)) := hγ.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hγL : ContDiffOn ℝ 2 γ (Icc (t - ε) t) := hγ.mono (Icc_subset_Icc le_rfl (by linarith))
  have huR : UniqueDiffOn ℝ (Icc t (t + ε)) := uniqueDiffOn_Icc (by linarith)
  have huL : UniqueDiffOn ℝ (Icc (t - ε) t) := uniqueDiffOn_Icc (by linarith)
  obtain ⟨KR, hKR⟩ := ContDiffOn.exists_lipschitzOnWith
    (ContDiffOn.derivWithin hγR huR (m := 1) (by norm_num)) one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  obtain ⟨KL, hKL⟩ := ContDiffOn.exists_lipschitzOnWith
    (ContDiffOn.derivWithin hγL huL (m := 1) (by norm_num)) one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  exact hasLipschitzDerivOnEachSideAt_of_lipschitzOnWith (by linarith) (by linarith)
    (ContDiffOn.differentiableOn hγR (by norm_num)) hKR
    (ContDiffOn.differentiableOn hγL (by norm_num)) hKL

end TauCeti.Contour

end
