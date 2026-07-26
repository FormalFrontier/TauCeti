module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product-measure helpers: a.e. transfer along the projections, and a Dynkin step for integrals

Two small pieces of product-measure theory with no `L²` or inner-product content.

* `TauCeti.ae_of_ae_fst` / `TauCeti.ae_of_ae_snd` transfer an a.e. statement about one factor to the
  product measure, along `Measure.quasiMeasurePreserving_fst` / `_snd`.
* `TauCeti.setIntegral_eq_zero_of_forall_prod` is the Dynkin (π-λ) step for Bochner integrals: a
  function whose integral vanishes on every measurable rectangle has vanishing integral on every
  measurable set. Rectangles are a π-system generating the product σ-algebra
  (`MeasureTheory.isPiSystem_prod`, `MeasureTheory.generateFrom_prod`), so
  `MeasurableSpace.induction_on_inter` applies. This is the Bochner counterpart of Mathlib's
  `ℝ≥0∞`-valued `MeasureTheory.lintegral_eq_lintegral_of_isPiSystem`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An a.e. statement on the first factor transfers to the product measure. -/
theorem ae_of_ae_fst {p : α → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.1 :=
  Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hp

/-- An a.e. statement on the second factor transfers to the product measure. -/
theorem ae_of_ae_snd {p : β → Prop} (hp : ∀ᵐ y ∂ν, p y) :
    ∀ᵐ q : α × β ∂(μ.prod ν), p q.2 :=
  Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hp

/-- **The Dynkin (π-λ) step for Bochner integrals on a product space.** A function whose integral
vanishes on every measurable rectangle has vanishing integral on every measurable set. -/
theorem setIntegral_eq_zero_of_forall_prod {ρ : Measure (α × β)} {f : α × β → E}
    (hf : Integrable f ρ)
    (hrect : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t → ∫ p in s ×ˢ t, f p ∂ρ = 0) :
    ∀ u, MeasurableSet u → ∫ p in u, f p ∂ρ = 0 := by
  have huniv : ∫ p, f p ∂ρ = 0 := by
    have h := hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
    rwa [Set.univ_prod_univ, setIntegral_univ] at h
  refine MeasurableSpace.induction_on_inter (C := fun u _ => ∫ p in u, f p ∂ρ = 0)
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  · simp
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact hrect s hs t ht
  · intro u hu ih
    rw [setIntegral_compl hu hf, huniv, ih, sub_zero]
  · intro u hd hm ih
    rw [integral_iUnion hm hd hf.integrableOn]
    simp [ih]

end TauCeti
