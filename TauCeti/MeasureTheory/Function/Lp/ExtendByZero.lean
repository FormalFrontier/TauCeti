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

`TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs hst : Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t)`,

together with the almost-everywhere description of its values, `TauCeti.coeFn_extendByZeroLpₗᵢ`.

The one point that needs care is that `Lᵖ` elements are equivalence classes: `s.indicator ⇑f`
depends on the chosen representative `⇑f`, which is only pinned down `μ.restrict s`-almost
everywhere, whereas the answer must be pinned down `μ.restrict t`-almost everywhere.  Mathlib's
`MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq` reconciles the two: an identity holding
`μ.restrict s`-almost everywhere survives multiplication by the indicator of `s` as an identity
against `μ`, hence against every restriction of `μ`.

## Main declarations

* `TauCeti.extendByZeroLpₗᵢ`: extension by zero as a linear isometry.
* `TauCeti.coeFn_extendByZeroLpₗᵢ` and `TauCeti.coeFn_extendByZeroLpₗᵢ_restrict`: the values of
  the extension, on `t` and back on `s`.
* `TauCeti.extendByZeroLpₗᵢ_self` and `TauCeti.extendByZeroLpₗᵢ_extendByZeroLpₗᵢ`: extending
  along `s ⊆ s` is the identity, and extending twice is extending once.
* `TauCeti.extendByZeroLpₗᵢ_eq_of_ae_eq` and `TauCeti.coeFn_extendByZeroLpₗᵢ_comp`: the two ways
  an extension is recognised in practice — from a representative that already vanishes off `s`,
  and through pointwise postcomposition by a map fixing `0`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {F : Type*} [NormedAddCommGroup F] (𝕜 : Type*)
  [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {p : ℝ≥0∞} {μ : Measure α} {s t : Set α}

/-- Extending by zero from `s` to `t` preserves `Lᵖ` membership when `s ⊆ t`. -/
private theorem memLp_indicator_restrict (hs : MeasurableSet s) (hst : s ⊆ t)
    {g : α → F} (hg : MemLp g p (μ.restrict s)) : MemLp (s.indicator g) p (μ.restrict t) := by
  rw [memLp_indicator_iff_restrict hs, Measure.restrict_restrict_of_subset hst]
  exact hg

/-- An almost-everywhere identity on `s` remains true after taking indicators, against
`μ.restrict t`. -/
private theorem indicator_ae_eq (hs : MeasurableSet s) {g h : α → F}
    (hgh : g =ᵐ[μ.restrict s] h) : s.indicator g =ᵐ[μ.restrict t] s.indicator h :=
  ((ae_eq_restrict_iff_indicator_ae_eq hs).mp hgh).filter_mono (ae_mono Measure.restrict_le_self)

variable (μ) in
/-- Extension by zero as a linear map; `TauCeti.extendByZeroLpₗᵢ` upgrades it to an isometry. -/
private def extendByZeroLpₗ (hs : MeasurableSet s) (hst : s ⊆ t) :
    Lp F p (μ.restrict s) →ₗ[𝕜] Lp F p (μ.restrict t) where
  toFun f := (memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      ((indicator_ae_eq hs (Lp.coeFn_add f g)).trans (.of_eq (indicator_add' s _ _)))
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _
      ((indicator_ae_eq hs (Lp.coeFn_smul c f)).trans (.of_eq (indicator_const_smul s c _)))

variable (μ) in
/-- **Extension by zero as a linear isometry** `Lᵖ(s) → Lᵖ(t)` for a measurable `s ⊆ t`: a
function on `s` is regarded as a function on the larger set `t` by declaring it zero on `t \ s`.

It is an isometry, not merely a bounded map, because the enlarged region contributes nothing to
the `Lᵖ` norm; in particular the extension is injective, so `Lᵖ(s)` really does sit inside
`Lᵖ(t)`. -/
def extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t) :
    Lp F p (μ.restrict s) →ₗᵢ[𝕜] Lp F p (μ.restrict t) where
  toLinearMap := extendByZeroLpₗ 𝕜 μ hs hst
  norm_map' f := by
    -- `Lp.norm_toLp` is stated for the unbundled `MemLp.toLp`; expose that implementation of
    -- `extendByZeroLpₗ`, which the bundled `toLinearMap` field hides.
    change ‖(memLp_indicator_restrict hs hst (Lp.memLp f)).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs,
      Measure.restrict_restrict_of_subset hst, ← Lp.norm_def]

/-- **The extension by zero is the indicator of the original representative.** -/
theorem coeFn_extendByZeroLpₗᵢ [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict t] s.indicator (f : α → F) :=
  MemLp.coeFn_toLp (memLp_indicator_restrict hs hst (Lp.memLp f))

/-- **The extension by zero restricts back to the original function.** -/
theorem coeFn_extendByZeroLpₗᵢ_restrict [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    (f : Lp F p (μ.restrict s)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst f : α → F) =ᵐ[μ.restrict s] (f : α → F) :=
  ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).filter_mono
    (ae_mono (Measure.restrict_mono hst le_rfl))).trans (indicator_ae_eq_restrict hs)

/-- **Extending by zero along `s ⊆ s` does nothing.** -/
@[simp]
theorem extendByZeroLpₗᵢ_self [Fact (1 ≤ p)] (hs : MeasurableSet s)
    (f : Lp F p (μ.restrict s)) : extendByZeroLpₗᵢ 𝕜 μ hs Subset.rfl f = f :=
  Lp.ext (coeFn_extendByZeroLpₗᵢ_restrict 𝕜 hs Subset.rfl f)

/-- **Extending by zero twice is extending by zero once.**  Zero-extending from `s` to `t` and
then from `t` to `u` is the zero-extension from `s` to `u`. -/
@[simp]
theorem extendByZeroLpₗᵢ_extendByZeroLpₗᵢ [Fact (1 ≤ p)] {u : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) (htu : t ⊆ u) (f : Lp F p (μ.restrict s)) :
    extendByZeroLpₗᵢ 𝕜 μ ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f) =
      extendByZeroLpₗᵢ 𝕜 μ hs (hst.trans htu) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 ht htu (extendByZeroLpₗᵢ 𝕜 μ hs hst f),
    indicator_ae_eq (t := u) ht (coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f),
    coeFn_extendByZeroLpₗᵢ 𝕜 hs (hst.trans htu) f] with x h1 h2 h3
  rw [h1, h2, h3, indicator_indicator, inter_eq_self_of_subset_right hst]

/-- **Recognising an extension by zero from a common representative.**  A function `h` supported
in `s` that represents `f` on `s` and `g` on `t` exhibits `g` as the zero-extension of `f`; this
is how a function already known to vanish off `s` is transported from `Lᵖ(s)` to `Lᵖ(t)`. -/
theorem extendByZeroLpₗᵢ_eq_of_ae_eq [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t)
    {h : α → F} (hsupp : Function.support h ⊆ s) {f : Lp F p (μ.restrict s)}
    {g : Lp F p (μ.restrict t)} (hf : ∀ᵐ x ∂μ.restrict s, f x = h x)
    (hg : ∀ᵐ x ∂μ.restrict t, g x = h x) : extendByZeroLpₗᵢ 𝕜 μ hs hst f = g :=
  Lp.ext <| ((coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f).trans
    ((indicator_ae_eq hs hf).trans (.of_eq (indicator_eq_self.2 hsupp)))).trans
    (Filter.EventuallyEq.symm hg)

/-- **Extension by zero commutes with pointwise postcomposition by a map fixing `0`.**  If `g'` is
the pointwise image of `f` under `L`, then the extension of `g'` is the pointwise image under `L`
of the extension of `f`: off `s` both sides are `L 0 = 0`. -/
theorem coeFn_extendByZeroLpₗᵢ_comp {G : Type*} [NormedAddCommGroup G] [Module 𝕜 G]
    [IsBoundedSMul 𝕜 G] [Fact (1 ≤ p)] (hs : MeasurableSet s) (hst : s ⊆ t) (L : F → G)
    (hL : L 0 = 0) {f : Lp F p (μ.restrict s)} {g' : Lp G p (μ.restrict s)}
    (hg' : ∀ᵐ x ∂μ.restrict s, g' x = L (f x)) :
    (extendByZeroLpₗᵢ 𝕜 μ hs hst g' : α → G) =ᵐ[μ.restrict t]
      fun x => L (extendByZeroLpₗᵢ 𝕜 μ hs hst f x) := by
  filter_upwards [coeFn_extendByZeroLpₗᵢ 𝕜 hs hst g', coeFn_extendByZeroLpₗᵢ 𝕜 hs hst f,
    indicator_ae_eq (t := t) hs hg'] with x h1 h2 h3
  rw [h1, h3, h2]
  by_cases hx : x ∈ s <;> simp [hx, hL]

end TauCeti
