/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Extension by zero between restricted `Lᵖ` spaces

An `Lᵖ` function on a measurable set `s` extends by zero to any larger set `t ⊇ s`, and the
extension has the *same* `Lᵖ` norm, because the added region contributes nothing.  This file
bundles that extension as a linear isometry

`TauCeti.extendByZeroLpₗᵢ μ hs hst : Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t)`,

together with the almost-everywhere description of its values, `TauCeti.coeFn_extendByZeroLpₗᵢ`.

The one point that needs care is that `Lᵖ` elements are equivalence classes: `s.indicator ⇑f`
depends on the chosen representative `⇑f`, which is only pinned down `μ.restrict s`-almost
everywhere, whereas the answer must be pinned down `μ.restrict t`-almost everywhere.  The two are
reconciled by `TauCeti.indicator_ae_eq_indicator_of_restrict`: an identity holding
`μ.restrict s`-almost everywhere survives multiplication by the indicator of `s` and passes to any
restriction of `μ`, because the set where it can fail meets `s` in a `μ`-null set.

## Main declarations

* `TauCeti.indicator_ae_eq_indicator_of_restrict`: transporting an almost-everywhere identity on
  `s` to the indicators, against any restriction of `μ`.
* `TauCeti.eLpNorm_indicator_restrict` and `TauCeti.memLp_indicator_restrict`: extension by zero
  preserves the `Lᵖ` seminorm and hence `Lᵖ` membership.
* `TauCeti.extendByZeroLpₗᵢ`: extension by zero as a linear isometry.
* `TauCeti.coeFn_extendByZeroLpₗᵢ` and `TauCeti.extendByZeroLpₗᵢ_ae_eq_of_restrict`: the values of
  the extension, on `t` and back on `s`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set

open scoped ENNReal

variable {α F 𝕜 : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {p : ℝ≥0∞} {μ : Measure α}
  {s t : Set α}

/-- **Almost-everywhere identities on `s` survive extension by zero.**  If `g` and `h` agree
`μ.restrict s`-almost everywhere then their zero-extensions agree almost everywhere for *any*
restriction of `μ`: outside `s` both vanish, and inside `s` they can differ only on a `μ`-null
set. -/
theorem indicator_ae_eq_indicator_of_restrict (hs : MeasurableSet s) {g h : α → F}
    (hgh : g =ᵐ[μ.restrict s] h) (t : Set α) :
    s.indicator g =ᵐ[μ.restrict t] s.indicator h := by
  have hmu : μ ({x | ¬ g x = h x} ∩ s) = 0 := by
    rw [← Measure.restrict_apply' hs]
    exact ae_iff.mp hgh
  have hnu : μ.restrict t ({x | ¬ g x = h x} ∩ s) = 0 :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self hmu
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnu
  by_cases hxs : x ∈ s
  · exact ⟨fun hgx => hx (by rw [indicator_of_mem hxs, indicator_of_mem hxs, hgx]), hxs⟩
  · exact absurd (by rw [indicator_of_notMem hxs, indicator_of_notMem hxs]) hx

/-- **Extension by zero preserves the `Lᵖ` seminorm.**  Enlarging the domain from `s` to `t ⊇ s`
adds only a region on which the extended function vanishes. -/
theorem eLpNorm_indicator_restrict (hs : MeasurableSet s) (hst : s ⊆ t) (g : α → F) :
    eLpNorm (s.indicator g) p (μ.restrict t) = eLpNorm g p (μ.restrict s) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, Measure.restrict_restrict_of_subset hst]

/-- **Extension by zero preserves `Lᵖ` membership.** -/
theorem memLp_indicator_restrict (hs : MeasurableSet s) (hst : s ⊆ t) {g : α → F}
    (hg : MemLp g p (μ.restrict s)) : MemLp (s.indicator g) p (μ.restrict t) := by
  rw [memLp_indicator_iff_restrict hs, Measure.restrict_restrict_of_subset hst]
  exact hg

variable (μ) in
/-- Extension by zero as a linear map; `TauCeti.extendByZeroLpₗᵢ` upgrades it to an isometry. -/
private def extendByZeroLpₗ [NormedField 𝕜] [NormedSpace 𝕜 F]
    (hs : MeasurableSet s) (hst : s ⊆ t) :
    Lp F p (μ.restrict s) →ₗ[𝕜] Lp F p (μ.restrict t) where
  toFun f := (memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _)
        ((memLp_indicator_restrict hs hst (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp g)),
      indicator_ae_eq_indicator_of_restrict hs (Lp.coeFn_add f g) t] with x h1 h2 h3 h4 h5
    rw [h1, h5, h2]
    simp only [Pi.add_apply, h3, h4]
    by_cases hxs : x ∈ s <;> simp [hxs]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp f)),
      indicator_ae_eq_indicator_of_restrict hs (Lp.coeFn_smul c f) t] with x h1 h2 h3 h4
    rw [h1, h4, RingHom.id_apply, h2]
    simp only [Pi.smul_apply, h3]
    by_cases hxs : x ∈ s <;> simp [hxs]

variable (μ) in
/-- **Extension by zero as a linear isometry** `Lᵖ(s) → Lᵖ(t)` for a measurable `s ⊆ t`: a
function on `s` is regarded as a function on the larger set `t` by declaring it zero on `t \ s`.

It is an isometry, not merely a bounded map, because the enlarged region contributes nothing to
the `Lᵖ` norm; in particular the extension is injective, so `Lᵖ(s)` really does sit inside
`Lᵖ(t)`. -/
def extendByZeroLpₗᵢ [NormedField 𝕜] [NormedSpace 𝕜 F] [Fact (1 ≤ p)] (hs : MeasurableSet s)
    (hst : s ⊆ t) : Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t) where
  toLinearMap := extendByZeroLpₗ μ hs hst
  norm_map' f := by
    change ‖(memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_restrict hs hst, ← Lp.norm_def]

/-- **The extension by zero is the indicator of the original representative.** -/
theorem coeFn_extendByZeroLpₗᵢ [NormedField 𝕜] [NormedSpace 𝕜 F] [Fact (1 ≤ p)]
    (hs : MeasurableSet s) (hst : s ⊆ t) (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ (𝕜 := 𝕜) μ hs hst f : α → F) =ᵐ[μ.restrict t] s.indicator (f : α → F) :=
  MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp f))

/-- **The extension by zero restricts back to the original function.** -/
theorem extendByZeroLpₗᵢ_ae_eq_of_restrict [NormedField 𝕜] [NormedSpace 𝕜 F] [Fact (1 ≤ p)]
    (hs : MeasurableSet s) (hst : s ⊆ t) (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ (𝕜 := 𝕜) μ hs hst f : α → F) =ᵐ[μ.restrict s] (f : α → F) := by
  have hle : μ.restrict s ≤ μ.restrict t := Measure.restrict_mono hst le_rfl
  exact ((coeFn_extendByZeroLpₗᵢ (𝕜 := 𝕜) hs hst f).filter_mono
    (ae_mono hle)).trans (indicator_ae_eq_restrict hs)

end TauCeti
