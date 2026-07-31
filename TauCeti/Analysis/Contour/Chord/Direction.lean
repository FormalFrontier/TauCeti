/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.AffineSpace.Slope

/-!
# The direction of a chord at a point the curve passes through

Let `γ t₀ = z₀`, so the chord `γ t - z₀` vanishes at `t₀`. If the one-sided slope
`(γ t - γ t₀) / (t - t₀)` converges to a non-zero `L`, then although the chord shrinks to zero
its *direction* still converges: to the normalisation of `L` from the right, and to its negative
from the left.

The sign is the substance. Approaching from the left `t - t₀ < 0`, so the chord is a *negative*
multiple of the slope and points opposite to it. This is why the interior angle swept at a
crossing is measured from the outgoing tangent to the reversed incoming one, as
`TauCeti.Contour.crossingAngle` does, and hence why a smooth crossing has angle `π` and
contributes `½` rather than `0`.

Both statements are exact rather than asymptotic: away from `t₀` the chord *is* a real multiple
of the slope (Mathlib's `sub_smul_slope`), so `NormedSpace.normalize_smul_of_pos` and
`normalize_smul_of_neg` give the identity pointwise, and the limits are the slope limits
transported.

Nothing here mentions curves, crossings or immersions, nor anything specific to `ℂ`: the
hypotheses are a point equality and a one-sided slope limit, so the results hold for any
`γ : ℝ → V` into a real normed space.

## Main results

* `TauCeti.Contour.tendsto_normalize_sub_nhdsGT` — the outgoing direction limit.
* `TauCeti.Contour.tendsto_normalize_sub_nhdsLT` — the incoming direction limit, reversed.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, Proposition 2.2.
-/

public section

namespace TauCeti.Contour

open Filter Set Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {γ : ℝ → V} {z₀ L : V} {t₀ : ℝ}

/-- Normalising a slope with a non-zero limit converges to the normalised limit. -/
private theorem tendsto_normalize_slope {l : Filter ℝ} (hL : L ≠ 0)
    (hslope : Tendsto (slope γ t₀) l (𝓝 L)) :
    Tendsto (fun t => NormedSpace.normalize (slope γ t₀ t)) l
      (𝓝 (NormedSpace.normalize L)) := by
  simp only [NormedSpace.normalize]
  exact (hslope.norm.inv₀ (norm_ne_zero_iff.mpr hL)).smul hslope

/-- **The outgoing chord direction.** As `t → t₀⁺` the direction of `γ t - z₀` tends to that
of the one-sided slope limit. -/
theorem tendsto_normalize_sub_nhdsGT (hcross : γ t₀ = z₀) (hL : L ≠ 0)
    (hslope : Tendsto (slope γ t₀) (𝓝[>] t₀) (𝓝 L)) :
    Tendsto (fun t => NormedSpace.normalize (γ t - z₀)) (𝓝[>] t₀)
      (𝓝 (NormedSpace.normalize L)) := by
  refine (tendsto_normalize_slope hL hslope).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← hcross, ← vsub_eq_sub (γ t) (γ t₀), ← sub_smul_slope γ t₀ t,
    NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht)]

/-- **The incoming chord direction, reversed.** As `t → t₀⁻` the direction of `γ t - z₀` tends
to the *negative* of that of the one-sided slope limit, since `t - t₀` is negative there. -/
theorem tendsto_normalize_sub_nhdsLT (hcross : γ t₀ = z₀) (hL : L ≠ 0)
    (hslope : Tendsto (slope γ t₀) (𝓝[<] t₀) (𝓝 L)) :
    Tendsto (fun t => NormedSpace.normalize (γ t - z₀)) (𝓝[<] t₀)
      (𝓝 (-NormedSpace.normalize L)) := by
  refine ((tendsto_normalize_slope hL hslope).neg).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← hcross, ← vsub_eq_sub (γ t) (γ t₀), ← sub_smul_slope γ t₀ t,
    NormedSpace.normalize_smul_of_neg (sub_neg.mpr ht)]

end TauCeti.Contour
