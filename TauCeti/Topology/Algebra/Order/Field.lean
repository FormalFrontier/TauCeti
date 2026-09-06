/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Ratios whose denominator diverges

Mathlib's `Mathlib/Topology/Algebra/Order/Field.lean` proves
`tendsto_bdd_div_atTop_nhds_zero`: a numerator confined to a fixed interval, divided by a
denominator that diverges to `atTop`, tends to `0`. This file records the companion statement
for a numerator that is *not* bounded but instead tracks the denominator: if `f` agrees with `g`
up to a two-sided additive bounded error and `g` diverges, then `f / g` tends to `1`.

## Main results

* `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` — if `g` tends to `atTop`
  along `l` and,
  eventually along `l`, `g - C₂ ≤ f ≤ g + C₁` for constants `C₁` and `C₂`, then `f / g` tends
  to `1`. No property of the denominator beyond divergence is used: the additive error washes
  out because `g` blows up.

## Implementation notes

The two error bounds are taken as separate `∃ C, ∀ᶠ …` hypotheses rather than as a single
bound on `|f - g|`, because a caller that derives the two inequalities from different estimates
arrives holding them in that shape and would otherwise have to recombine them.

## References

Adapted from `tendsto_ratio_one_of_div_atTop_pm_bounded` in
`CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states it
over `ℝ`; the statement here is over an arbitrary linearly ordered topological field.
-/

public section

namespace TauCeti

open Filter Topology

/-- A ratio whose denominator diverges and whose numerator tracks it up to a two-sided additive
bounded error tends to `1`. Contrast `tendsto_bdd_div_atTop_nhds_zero`, whose numerator is confined
to a fixed interval and whose ratio tends to `0`. -/
theorem tendsto_div_nhds_one_of_le_add_const_of_sub_const_le {𝕜 α : Type*} [Field 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    {l : Filter α} {g f : α → 𝕜}
    (hg : Tendsto g l atTop) (h_le : ∃ C : 𝕜, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : 𝕜, ∀ᶠ s in l, g s - C ≤ f s) : Tendsto (fun s ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  -- the additive error washes out under division because the denominator blows up
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  exact (add_zero (1 : 𝕜) ▸ h0.const_add 1).congr' <|
    (hg.eventually_gt_atTop 0).mono fun s h ↦ by grind

end TauCeti
