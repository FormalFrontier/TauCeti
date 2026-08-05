/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- Both imports are public: `TestFunction` supplies `𝓓(Ω, ℝ)`, `Opens`, `lineDeriv` and
-- `LocallyIntegrableOn`, and the Bochner integral supplies the `∫ … ∂μ` appearing in every
-- statement below.
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- The next two imports are private: integration by parts is used only to prove that a classical
-- derivative is a weak one, and the fundamental lemma of the calculus of variations only to prove
-- uniqueness, so downstream importers pay for neither.
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weak derivatives on an open set

Lane A of the PDE roadmap builds the Sobolev spaces `W^{k,p}(Ω)` of a domain out of *weak*
derivatives, rather than out of Mathlib's whole-space Bessel-potential scale. This file supplies
the underlying differentiation notion: for an open set `Ω` in a real normed space `E`, a measure
`μ` on `E`, functions `u, u' : E → F` and a direction `v : E`,

`TauCeti.HasWeakLineDerivOn μ Ω u u' v`

says that `∫ (∂_v φ) • u = - ∫ φ • u'` for every test function `φ ∈ 𝓓(Ω, ℝ)`, i.e. that `u'`
represents the distributional derivative `∂_v u` on `Ω`. The bundled test-function type
`TestFunction` of `Mathlib/Analysis/Distribution/TestFunction.lean` is the class of admissible
`φ`, so the definition is exactly the distributional one; `TauCeti.hasWeakLineDerivOn_iff`
restates it in terms of unbundled smooth compactly supported functions when that is more
convenient.

Assembling the directions gives `TauCeti.HasWeakFDerivOn μ Ω u U` for a candidate weak derivative
`U : E → E →L[ℝ] F`, the object whose `Lᵖ` integrability cuts out `W^{1,p}(Ω)`.

Two facts make the notion usable, and both are proved here.

* **Uniqueness.** Two weak derivatives that are locally integrable on `Ω` agree almost everywhere
  on `Ω` (`TauCeti.HasWeakLineDerivOn.ae_eq` and `TauCeti.HasWeakFDerivOn.ae_eq`). This is the
  fundamental lemma of the calculus of variations, consumed from Mathlib in the form
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. Local integrability is a genuine
  hypothesis and is carried separately, exactly as the roadmap asks: without it the identity
  defining a weak derivative is a statement about junk-valued integrals.
* **Consistency.** A classical derivative is a weak derivative
  (`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`, `TauCeti.hasWeakFDerivOn_of_differentiableOn`),
  by integration by parts. Together with uniqueness this pins the notion down: on a `C¹`
  function the weak derivative is the classical one almost everywhere.

Nothing here assumes that `Ω` is bounded or that its boundary is regular: the weak derivative is a
purely interior notion, and boundary hypotheses enter only with traces and extensions.

## Main declarations

* `TauCeti.HasWeakLineDerivOn`: `u'` is a weak derivative of `u` in the direction `v` on `Ω`.
* `TauCeti.HasWeakFDerivOn`: `U` is a weak (Fréchet) derivative of `u` on `Ω`.
* `TauCeti.hasWeakLineDerivOn_iff`: the unbundled restatement of the defining identity.
* `TauCeti.integrable_smul_of_locallyIntegrableOn` and
  `TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn`: the two integrability facts that
  make the defining integrals honest.
* `TauCeti.HasWeakLineDerivOn.mono` and `TauCeti.HasWeakFDerivOn.mono`: a weak derivative on `Ω`
  is one on every smaller open set.
* `TauCeti.HasWeakLineDerivOn.congr_ae` and `TauCeti.HasWeakLineDerivOn.congr_ae'`: the notion
  only sees `u` and `u'` up to almost-everywhere equality on `Ω`.
* `TauCeti.HasWeakLineDerivOn.add`, `.neg`, `.sub`, `.const_smul`: linearity in the function.
* `TauCeti.HasWeakLineDerivOn.add_direction` and `.smul_direction`: linearity in the direction,
  which is what makes the `TauCeti.HasWeakFDerivOn` packaging the right one.
* `TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt` and
  `TauCeti.hasWeakFDerivOn_of_differentiableOn`: classical derivatives are weak derivatives.
* `TauCeti.hasWeakLineDerivOn_const`: a constant has weak derivative `0`.
* `TauCeti.HasWeakLineDerivOn.ae_eq` and `TauCeti.HasWeakFDerivOn.ae_eq`: uniqueness almost
  everywhere on `Ω`.
* `TauCeti.HasWeakLineDerivOn.ae_eq_lineDeriv` and `TauCeti.HasWeakFDerivOn.ae_eq_fderiv`: where
  the classical derivative exists, the weak one agrees with it almost everywhere.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E}

/-! ### Derivatives of test functions -/

/-- Outside its support, the directional derivative of a test function vanishes. -/
theorem lineDeriv_eq_zero_of_notMem_tsupport (φ : 𝓓(Ω, ℝ)) {x : E}
    (hx : x ∉ tsupport (φ : E → ℝ)) (v : E) : lineDeriv ℝ (φ : E → ℝ) x v = 0 := by
  have hd : DifferentiableAt ℝ (φ : E → ℝ) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt
  rw [hd.lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hx]
  simp

/-! ### The definitions -/

section Defs

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- `HasWeakLineDerivOn μ Ω u u' v` says that `u'` is a **weak derivative** of `u` in the
direction `v` on the open set `Ω`: the integration-by-parts identity

`∫ (∂_v φ) • u ∂μ = - ∫ φ • u' ∂μ`

holds for every test function `φ : 𝓓(Ω, ℝ)`, that is, for every smooth `φ : E → ℝ` whose support
is compact and contained in `Ω`. Equivalently, `u'` represents the distributional derivative
`∂_v u` on `Ω`.

This carries no integrability hypothesis: `LocallyIntegrableOn u Ω μ` and
`LocallyIntegrableOn u' Ω μ` are the separate hypotheses under which the identity determines `u'`
almost everywhere (`TauCeti.HasWeakLineDerivOn.ae_eq`). -/
def HasWeakLineDerivOn (μ : Measure E) (Ω : Opens E) (u u' : E → F) (v : E) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ = -∫ x, (φ : E → ℝ) x • u' x ∂μ

/-- `HasWeakFDerivOn μ Ω u U` says that `U : E → E →L[ℝ] F` is a **weak (Fréchet) derivative** of
`u` on the open set `Ω`: for every direction `v`, the function `x ↦ U x v` is a weak derivative of
`u` in the direction `v`.

Requiring `u` and `U` to be `Lᵖ` on `Ω` is what cuts out the first-order Sobolev space
`W^{1,p}(Ω)`. -/
def HasWeakFDerivOn (μ : Measure E) (Ω : Opens E) (u : E → F) (U : E → E →L[ℝ] F) : Prop :=
  ∀ v : E, HasWeakLineDerivOn μ Ω u (fun x => U x v) v

/-- The defining identity of a weak derivative, stated for unbundled test functions. -/
theorem hasWeakLineDerivOn_iff :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, lineDeriv ℝ φ x v • u x ∂μ = -∫ x, φ x • u' x ∂μ :=
  ⟨fun h φ hφ hφc hφs => h ⟨φ, hφ, hφc, hφs⟩,
    fun h φ => h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset⟩

/-- A weak derivative on `Ω` is a weak derivative on every smaller open set: weak
differentiability is a local notion. -/
theorem HasWeakLineDerivOn.mono {Ω' : Opens E} (h : HasWeakLineDerivOn μ Ω u u' v) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDerivOn μ Ω' u u' v := fun φ =>
  h ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩

/-- A weak Fréchet derivative on `Ω` is one on every smaller open set. -/
theorem HasWeakFDerivOn.mono {U : E → E →L[ℝ] F} {Ω' : Opens E} (h : HasWeakFDerivOn μ Ω u U)
    (hΩ : Ω' ≤ Ω) : HasWeakFDerivOn μ Ω' u U := fun v => (h v).mono hΩ

/-- Every direction of a weak Fréchet derivative is a weak directional derivative. -/
theorem HasWeakFDerivOn.hasWeakLineDerivOn {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (v : E) : HasWeakLineDerivOn μ Ω u (fun x => U x v) v := h v

/-- Weak differentiation commutes with negation. -/
theorem HasWeakLineDerivOn.neg (h : HasWeakLineDerivOn μ Ω u u' v) :
    HasWeakLineDerivOn μ Ω (-u) (-u') v := by
  intro φ
  simp only [Pi.neg_apply, smul_neg, integral_neg, h φ, neg_neg]

/-- Weak differentiation commutes with multiplication by a real scalar. -/
theorem HasWeakLineDerivOn.const_smul (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω (c • u) (c • u') v := by
  intro φ
  simp only [Pi.smul_apply, smul_comm _ c, integral_smul, h φ, smul_neg]

end Defs

/-! ### Integrability of the defining integrands -/

section Integrability

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- A test function on `Ω` scales a function locally integrable on `Ω` to a globally integrable
one: this is `TestFunction.integrable_bilin` for scalar multiplication. -/
theorem integrable_smul_of_locallyIntegrableOn {w : E → F} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => (φ : E → ℝ) x • w x) μ := by
  simpa using TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hw φ

/-- The direction-`v` derivative of a test function on `Ω` is again a test function on `Ω`, so it
too scales a function locally integrable on `Ω` to a globally integrable one. -/
theorem integrable_lineDeriv_smul_of_locallyIntegrableOn {w : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x => lineDeriv ℝ (φ : E → ℝ) x v • w x) μ := by
  have hcoe : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  simpa [hcoe] using
    integrable_smul_of_locallyIntegrableOn hw (TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ))

/-- Replacing `u` by a function agreeing with it almost everywhere on `Ω` preserves the weak
derivative: only the restriction of `u` to `Ω` is seen. -/
theorem HasWeakLineDerivOn.congr_ae {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω w u' v := by
  intro φ
  rw [← h φ]
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [lineDeriv_eq_zero_of_notMem_tsupport φ (fun h' => hxΩ (φ.tsupport_subset h')) v]
    simp

/-- Replacing `u'` by a function agreeing with it almost everywhere on `Ω` preserves the weak
derivative. -/
theorem HasWeakLineDerivOn.congr_ae' {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u' =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω u w v := by
  intro φ
  rw [h φ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => hxΩ (φ.tsupport_subset h'))]
    simp

end Integrability

/-! ### Linearity -/

section Linearity

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- Weak differentiation is additive, once all four functions involved are locally integrable
on `Ω`. -/
theorem HasWeakLineDerivOn.add {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) (hu₁ : LocallyIntegrableOn u₁ Ω μ)
    (hu₁' : LocallyIntegrableOn u₁' Ω μ) (hu₂ : LocallyIntegrableOn u₂ Ω μ)
    (hu₂' : LocallyIntegrableOn u₂' Ω μ) :
    HasWeakLineDerivOn μ Ω (u₁ + u₂) (u₁' + u₂') v := by
  intro φ
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • (u₁ + u₂) x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₁ x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₂ x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn hu₁ φ v)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hu₂ φ v)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn hu₁' φ)
      (integrable_smul_of_locallyIntegrableOn hu₂' φ)
  rw [hleft, hright, h₁ φ, h₂ φ, neg_add]

/-- Weak differentiation is compatible with subtraction, once all four functions involved are
locally integrable on `Ω`. -/
theorem HasWeakLineDerivOn.sub {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) (hu₁ : LocallyIntegrableOn u₁ Ω μ)
    (hu₁' : LocallyIntegrableOn u₁' Ω μ) (hu₂ : LocallyIntegrableOn u₂ Ω μ)
    (hu₂' : LocallyIntegrableOn u₂' Ω μ) :
    HasWeakLineDerivOn μ Ω (u₁ - u₂) (u₁' - u₂') v := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg hu₁ hu₁' hu₂.neg hu₂'.neg

/-- The weak derivative is additive in the direction of differentiation. Together with
`TauCeti.HasWeakLineDerivOn.smul_direction` this is what makes packaging the directional weak
derivatives into a single continuous linear map, as `TauCeti.HasWeakFDerivOn` does, the right
move. -/
theorem HasWeakLineDerivOn.add_direction {u u₁' u₂' : E → F} {v₁ v₂ : E}
    (h₁ : HasWeakLineDerivOn μ Ω u u₁' v₁) (h₂ : HasWeakLineDerivOn μ Ω u u₂' v₂)
    (hu : LocallyIntegrableOn u Ω μ) (hu₁' : LocallyIntegrableOn u₁' Ω μ)
    (hu₂' : LocallyIntegrableOn u₂' Ω μ) :
    HasWeakLineDerivOn μ Ω u (u₁' + u₂') (v₁ + v₂) := by
  intro φ
  have hφd : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  have hsplit : ∀ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) =
      lineDeriv ℝ (φ : E → ℝ) x v₁ + lineDeriv ℝ (φ : E → ℝ) x v₂ := by
    intro x
    simp only [(hφd x).lineDeriv_eq_fderiv, map_add]
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) • u x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v₁ • u x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v₂ • u x ∂μ := by
    simp only [hsplit, add_smul]
    exact integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v₁)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v₂)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn hu₁' φ)
      (integrable_smul_of_locallyIntegrableOn hu₂' φ)
  rw [hleft, hright, h₁ φ, h₂ φ, neg_add]

end Linearity

/-! ### Scaling the direction -/

section SmulDirection

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

/-- The weak derivative is homogeneous in the direction of differentiation. -/
theorem HasWeakLineDerivOn.smul_direction (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω u (c • u') (c • v) := by
  intro φ
  have hφd : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  have hsmul : ∀ x, lineDeriv ℝ (φ : E → ℝ) x (c • v) = c * lineDeriv ℝ (φ : E → ℝ) x v := by
    intro x
    simp only [(hφd x).lineDeriv_eq_fderiv, map_smul, smul_eq_mul]
  simp only [hsmul, mul_smul, integral_smul, h φ, Pi.smul_apply, smul_comm _ c, smul_neg]

end SmulDirection

/-! ### Classical derivatives are weak derivatives -/

section Classical

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {u u' : E → F}

/-- **A classical derivative is a weak derivative.** If `u` has line derivative `u' x` in the
direction `v` at every point of the open set `Ω`, and both `u` and `u'` are locally integrable
on `Ω`, then `u'` is a weak derivative of `u` in the direction `v` on `Ω`.

The proof is Mathlib's integration by parts applied to `u` against a test function; the boundary
term is absent because the test function has compact support inside `Ω`. -/
theorem hasWeakLineDerivOn_of_hasLineDerivAt (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) (h : ∀ x ∈ (Ω : Set E), HasLineDerivAt ℝ u (u' x) x v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  intro φ
  have hφd : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (f := u) (f' := u') (g := (φ : E → ℝ))
    (g' := fun x => lineDeriv ℝ (φ : E → ℝ) x v) (v := v)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu' φ)
    (by simpa using integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu φ)
    (fun x hx => h x (φ.tsupport_subset hx))
    (fun x _ => ((hφd x).hasFDerivAt.hasLineDerivAt v).lineDeriv ▸
      (hφd x).hasFDerivAt.hasLineDerivAt v)
  simpa using key

/-- A constant function has weak derivative `0` in every direction: the first sanity check that
`TauCeti.HasWeakLineDerivOn` is not vacuous. -/
theorem hasWeakLineDerivOn_const (c : F) :
    HasWeakLineDerivOn μ Ω (fun _ => c) (fun _ => 0) v :=
  hasWeakLineDerivOn_of_hasLineDerivAt (locallyIntegrableOn_const c) locallyIntegrableOn_zero
    fun x _ => (hasFDerivAt_const c x).hasLineDerivAt v

/-- **A classical Fréchet derivative is a weak one.** If `u` is differentiable at every point of
the open set `Ω`, and both `u` and `fderiv ℝ u` are locally integrable on `Ω`, then `fderiv ℝ u`
is a weak derivative of `u` on `Ω`. -/
theorem hasWeakFDerivOn_of_differentiableOn (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (h : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    HasWeakFDerivOn μ Ω u (fderiv ℝ u) := fun v =>
  hasWeakLineDerivOn_of_hasLineDerivAt hu
    (by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hu')
    fun x hx => (h x hx).hasFDerivAt.hasLineDerivAt v

end Classical

/-! ### Uniqueness -/

section Uniqueness

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  {μ : Measure E} {u : E → F}

/-- **A weak derivative is unique almost everywhere.** Two locally integrable weak derivatives of
`u` in the same direction on `Ω` agree almost everywhere on `Ω`.

This is the fundamental lemma of the calculus of variations: their difference integrates to zero
against every test function supported in `Ω`. -/
theorem HasWeakLineDerivOn.ae_eq {u₁' u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u u₂' v) (hu₁ : LocallyIntegrableOn u₁' Ω μ)
    (hu₂ : LocallyIntegrableOn u₂' Ω μ) : u₁' =ᵐ[μ.restrict Ω] u₂' := by
  have key : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ (Ω : Set E) →
      ∫ x, φ x • (u₁' - u₂') x ∂μ = 0 := by
    intro φ hφ hφc hφs
    have hi₁ : Integrable (fun x => φ x • u₁' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₁ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hi₂ : Integrable (fun x => φ x • u₂' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₂ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hsame : ∫ x, φ x • u₁' x ∂μ = ∫ x, φ x • u₂' x ∂μ := by
      have hneg := (h₁ ⟨φ, hφ, hφc, hφs⟩).symm.trans (h₂ ⟨φ, hφ, hφc, hφs⟩)
      simpa using neg_injective hneg
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi₁ hi₂, hsame, sub_self]
  have hzero := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hu₁.sub hu₂) key
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hzero] with x hx hxΩ
  simpa [sub_eq_zero] using hx hxΩ

/-- **A weak Fréchet derivative is unique almost everywhere.** Two locally integrable weak
derivatives of `u` on `Ω` agree almost everywhere on `Ω`.

The directional statement `TauCeti.HasWeakLineDerivOn.ae_eq` is applied along the finitely many
vectors of a basis of `E`, and the resulting almost-everywhere statements are intersected. -/
theorem HasWeakFDerivOn.ae_eq {U₁ U₂ : E → E →L[ℝ] F} (h₁ : HasWeakFDerivOn μ Ω u U₁)
    (h₂ : HasWeakFDerivOn μ Ω u U₂) (hU₁ : LocallyIntegrableOn U₁ Ω μ)
    (hU₂ : LocallyIntegrableOn U₂ Ω μ) : U₁ =ᵐ[μ.restrict Ω] U₂ := by
  set b := Module.finBasis ℝ E with hb
  have hcoord : ∀ i, (fun x => U₁ x (b i)) =ᵐ[μ.restrict Ω] fun x => U₂ x (b i) := by
    intro i
    refine (h₁ (b i)).ae_eq (h₂ (b i)) ?_ ?_
    · simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℝ F (b i)).locallyIntegrableOn_comp hU₁
    · simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℝ F (b i)).locallyIntegrableOn_comp hU₂
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  exact ContinuousLinearMap.coe_injective (b.ext fun i => hx i)

end Uniqueness

/-! ### The weak derivative of a classically differentiable function -/

section Comparison

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u u' : E → F}

/-- **The weak derivative of a classically differentiable function is the classical one.** If `u`
has a line derivative in the direction `v` at every point of `Ω`, then any locally integrable weak
derivative of `u` in that direction agrees with it almost everywhere on `Ω`.

Combined with `TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`, this says that the weak derivative
extends the classical one without changing it where the classical one exists. -/
theorem HasWeakLineDerivOn.ae_eq_lineDeriv (h : HasWeakLineDerivOn μ Ω u u' v)
    (hu : LocallyIntegrableOn u Ω μ) (hu' : LocallyIntegrableOn u' Ω μ)
    (hd : LocallyIntegrableOn (fun x => lineDeriv ℝ u x v) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), LineDifferentiableAt ℝ u x v) :
    u' =ᵐ[μ.restrict Ω] fun x => lineDeriv ℝ u x v :=
  h.ae_eq (hasWeakLineDerivOn_of_hasLineDerivAt hu hd fun x hx => (hdiff x hx).hasLineDerivAt)
    hu' hd

/-- **The weak Fréchet derivative of a differentiable function is `fderiv`.** If `u` is
differentiable at every point of `Ω`, then any locally integrable weak Fréchet derivative of `u`
agrees with `fderiv ℝ u` almost everywhere on `Ω`. -/
theorem HasWeakFDerivOn.ae_eq_fderiv {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hu : LocallyIntegrableOn u Ω μ) (hU : LocallyIntegrableOn U Ω μ)
    (hd : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    U =ᵐ[μ.restrict Ω] fderiv ℝ u :=
  h.ae_eq (hasWeakFDerivOn_of_differentiableOn hu hd hdiff) hU hd

end Comparison

end TauCeti
