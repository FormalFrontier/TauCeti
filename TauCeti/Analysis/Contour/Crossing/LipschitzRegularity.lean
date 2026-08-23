/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The `C^{1,1}` crossing-regularity hypothesis

This file defines `HasLipschitzDerivOnEachSideAt`, the one-sided-Lipschitz-derivative regularity
condition a crossing needs for the real winding integrand to stay bounded there
(`Winding.RealIntegral.OnCurve`), and its introduction/elimination API. The predicate itself
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
* `Contour.hasLipschitzDerivOnEachSideAt_of_contDiffOn` -- introduces it from one-sided `C²` data.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.3 and its proof's one-sided treatment of a corner
  crossing, p. 9.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The `C^{1,1}` crossing-regularity hypothesis**: `derivWithin γ` is Lipschitz on a one-sided
closed window ending or starting at `t`, on each side (a `KR`/`εR`-window to the right, a
`KL`/`εL`-window to the left) — the two sides need not agree, so `t` may coincide with a
breakpoint of the immersion. Packages the hypotheses of `Winding.LipschitzBoundedIntegrand`'s
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner` other than
differentiability and each side's non-vanishing velocity, which a caller who already
has a piecewise-`C¹` immersion in hand gets for free from
`IsPwC1ImmersionOn.exists_lipschitzOnWith_derivWithin_shrink_right`/`_left` (differentiability)
and `IsPwC1ImmersionOn.derivWithin_ne_zero_right`/`_left` (non-vanishing velocity), so should not
need to separately supply either. An opaque `def`, not an `abbrev`: consumers destructure it via
`hasLipschitzDerivOnEachSideAt_iff` below rather than unfolding it directly. -/
def HasLipschitzDerivOnEachSideAt (γ : ℝ → E) (t : ℝ) : Prop :=
  ∃ εR > 0, ∃ KR : ℝ≥0, LipschitzOnWith KR (derivWithin γ (Icc t (t + εR))) (Icc t (t + εR)) ∧
    ∃ εL > 0, ∃ KL : ℝ≥0,
    LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t)) (Icc (t - εL) t)

/-- **The characteristic iff for `HasLipschitzDerivOnEachSideAt`.** Equates the opaque `def` above
with its displayed one-sided witness proposition, exposing the `εR`/`KR`-window to the right and
the `εL`/`KL`-window to the left as a plain nested existential -- the introduction/elimination
interface a caller (e.g. via `choose!`) uses to name the witnesses, or to build the predicate from
them directly, rather than unfolding the `def`. -/
theorem hasLipschitzDerivOnEachSideAt_iff {γ : ℝ → E} {t : ℝ} :
    HasLipschitzDerivOnEachSideAt γ t ↔
    ∃ εR > 0, ∃ KR : ℝ≥0, LipschitzOnWith KR (derivWithin γ (Icc t (t + εR))) (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t)) (Icc (t - εL) t) :=
  Iff.rfl

/-- **Introducing `HasLipschitzDerivOnEachSideAt` from one-sided `C^{1,1}` data on arbitrary
pieces.** If `derivWithin γ` is Lipschitz on `[c, t]` and on `[t, d]`, `t` itself has a Lipschitz
derivative on each side -- the defining `εR`/`εL`-windows are just these same pieces, `εR := d - t`
and `εL := t - c`. A caller whose one-sided pieces are wider than it ultimately needs must
transfer `derivWithin` to the narrower piece first (e.g. via
`IsPwC1ImmersionOn.exists_lipschitzOnWith_derivWithin_shrink_right`/`_left`):
`LipschitzOnWith.mono`
alone does not suffice, since `derivWithin` itself depends on the underlying set. -/
theorem hasLipschitzDerivOnEachSideAt_of_lipschitzOnWith {γ : ℝ → E} {c t d : ℝ} {KR KL : ℝ≥0}
    (hct : c < t) (htd : t < d)
    (hlipR : LipschitzOnWith KR (derivWithin γ (Icc t d)) (Icc t d))
    (hlipL : LipschitzOnWith KL (derivWithin γ (Icc c t)) (Icc c t)) :
    HasLipschitzDerivOnEachSideAt γ t := by
  refine ⟨d - t, by linarith, KR, ?_, t - c, by linarith, KL, ?_⟩ <;>
    simpa only [add_sub_cancel, sub_sub_cancel]

/-- **Introducing `HasLipschitzDerivOnEachSideAt` from one-sided `C²` data.** A `γ` twice
differentiable on `[c, t]` and on `[t, d]` -- independently, so `t` may be a corner where the two
sides disagree -- has, on each half, a `C¹` (hence locally Lipschitz, and Lipschitz on the
compact half itself) `derivWithin`: the natural route to `HasLipschitzDerivOnEachSideAt` for a
curve with an honest second derivative on each side of a crossing, as opposed to the merely
`C^{1,1}` case this predicate was built to also cover. The two-sided `C²` case is `hγ.mono` on
each half at the call site. -/
theorem hasLipschitzDerivOnEachSideAt_of_contDiffOn {γ : ℝ → E} {c t d : ℝ} (hct : c < t)
    (htd : t < d) (hγL : ContDiffOn ℝ 2 γ (Icc c t)) (hγR : ContDiffOn ℝ 2 γ (Icc t d)) :
    HasLipschitzDerivOnEachSideAt γ t := by
  have huR : UniqueDiffOn ℝ (Icc t d) := uniqueDiffOn_Icc htd
  have huL : UniqueDiffOn ℝ (Icc c t) := uniqueDiffOn_Icc hct
  obtain ⟨KR, hKR⟩ := ContDiffOn.exists_lipschitzOnWith
    (ContDiffOn.derivWithin hγR huR (m := 1) (by norm_num)) one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  obtain ⟨KL, hKL⟩ := ContDiffOn.exists_lipschitzOnWith
    (ContDiffOn.derivWithin hγL huL (m := 1) (by norm_num)) one_ne_zero (convex_Icc _ _)
    isCompact_Icc
  exact hasLipschitzDerivOnEachSideAt_of_lipschitzOnWith hct htd hKR hKL

end TauCeti.Contour

end
