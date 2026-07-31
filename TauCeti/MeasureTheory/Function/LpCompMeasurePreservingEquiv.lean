/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cadence
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `L^p` isometric equivalences from an almost-everywhere inverse pair

Mathlib turns a measure-preserving map `f : α → β` into a linear isometry
`MeasureTheory.Lp.compMeasurePreservingₗᵢ : Lp E p μb →ₗᵢ[𝕜] Lp E p μ`, but stops there: there is
no constructor producing a `LinearIsometryEquiv`. Transporting structure between `L²` spaces —
a Hilbert basis, an orthonormal family, a spectral decomposition — needs the equivalence, since
`HilbertBasis.mapₗᵢ` and its relatives consume `≃ₗᵢ` rather than `→ₗᵢ`.

A change of variables rarely supplies a `MeasurableEquiv`. The maps that arise in practice are
inverse to each other only *almost everywhere*: `Real.cos` and `Real.arccos` are mutually inverse
on `[-1, 1]` and on `(0, π]`, not on all of `ℝ`. This file therefore takes the weakest hypothesis
that still yields an equivalence — a pair of measure-preserving maps that compose to the identity
almost everywhere in each direction — and builds the isometric equivalence from it.

## Main declarations

* `MeasureTheory.Lp.compMeasurePreservingₗᵢ_apply` is the application lemma for Mathlib's
  linear isometry. Mathlib's `@[simps!]` generates only `compMeasurePreservingₗᵢ_apply_coe`,
  which unfolds one level too far to rewrite with.
* `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` upgrades that linear isometry to a
  `LinearIsometryEquiv` given an almost-everywhere inverse partner.
* `MeasureTheory.Lp.coeFn_compMeasurePreservingₗᵢEquiv` identifies the equivalence with
  precomposition by `f`.
-/

public section

open scoped ENNReal

namespace MeasureTheory
namespace Lp

/-- The application lemma for `MeasureTheory.Lp.compMeasurePreservingₗᵢ`.

Mathlib marks that definition `@[simps!]`, which generates `compMeasurePreservingₗᵢ_apply_coe`
— an equation about the underlying `AEEqFun`, one unfolding past the point where a rewrite is
usable. This states the map itself. -/
@[simp]
theorem compMeasurePreservingₗᵢ_apply {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E] {f : α → β}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (x : Lp E p μb) :
    compMeasurePreservingₗᵢ 𝕜 f hf x = compMeasurePreserving f hf x :=
  rfl

/-- If `f` and `g` are measure-preserving and `f ∘ g` is the identity almost everywhere, then
precomposing by `g` undoes precomposing by `f`. -/
theorem compMeasurePreserving_comp_of_ae_id {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (x : Lp E p μb) :
    compMeasurePreserving g hg (compMeasurePreserving f hf x) = x := by
  refine Lp.ext ?_
  rw [← compMeasurePreserving_comp_apply (E := E) (p := p) x hf hg]
  filter_upwards [coeFn_compMeasurePreserving (E := E) (p := p) x (hf.comp hg), hfg]
    with b hb hid
  rw [hb]
  simpa using congrArg (fun a => (x : β → E) a) hid

/-- **The `L^p` isometric equivalence induced by an almost-everywhere inverse pair of
measure-preserving maps.**

`f` and `g` are each measure-preserving and compose to the identity almost everywhere in both
directions; precomposition by `f` is then an isometric isomorphism `Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ`,
with inverse precomposition by `g`.

The almost-everywhere hypotheses are what make this usable for a change of variables: `Real.cos`
and `Real.arccos` satisfy them without forming a `MeasurableEquiv`. -/
@[expose]
noncomputable def compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (hgf : g ∘ f =ᵐ[μ] id) :
    Lp E p μb ≃ₗᵢ[𝕜] Lp E p μ :=
  LinearIsometryEquiv.ofLinearIsometry (compMeasurePreservingₗᵢ 𝕜 f hf)
    (compMeasurePreservingₗ 𝕜 g hg)
    (LinearMap.ext fun x => compMeasurePreserving_comp_of_ae_id (E := E) (p := p) hg hf hgf x)
    (LinearMap.ext fun x => compMeasurePreserving_comp_of_ae_id (E := E) (p := p) hf hg hfg x)

@[simp]
theorem compMeasurePreservingₗᵢEquiv_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (hgf : g ∘ f =ᵐ[μ] id) (x : Lp E p μb) :
    compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg hgf x = compMeasurePreserving f hf x :=
  rfl

@[simp]
theorem compMeasurePreservingₗᵢEquiv_symm_apply {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (hgf : g ∘ f =ᵐ[μ] id) (x : Lp E p μ) :
    (compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg hgf).symm x = compMeasurePreserving g hg x :=
  rfl

/-- The equivalence is almost everywhere precomposition by `f`. -/
theorem coeFn_compMeasurePreservingₗᵢEquiv {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {μb : Measure β} {p : ℝ≥0∞} [NormedAddCommGroup E]
    {f : α → β} {g : β → α}
    (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [Fact (1 ≤ p)]
    (hf : MeasurePreserving f μ μb) (hg : MeasurePreserving g μb μ)
    (hfg : f ∘ g =ᵐ[μb] id) (hgf : g ∘ f =ᵐ[μ] id) (x : Lp E p μb) :
    ⇑(compMeasurePreservingₗᵢEquiv 𝕜 hf hg hfg hgf x) =ᵐ[μ] ⇑x ∘ f := by
  simpa using coeFn_compMeasurePreserving (E := E) (p := p) x hf

end Lp
end MeasureTheory
