/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Codex
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Sard's lemma in equal dimensions

This file proves the equal-dimensional case of Sard's theorem for maps between two possibly
different finite-dimensional real normed spaces.  A differentiable map sends any set on which its
derivative is nowhere surjective to a set of additive Haar measure zero.  In particular, the
critical values of a differentiable map between spaces of equal dimension have measure zero, and
the regular values are dense.

Mathlib proves the corresponding result for an endomorphism of one normed space in
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.  We transport the codomain across a continuous
linear equivalence and use uniqueness of additive Haar measure to return to the original codomain.
This is the first, equal-dimensional slice of finite-dimensional Sard required by Lane F0 of the
analytic Heegaard Floer roadmap.  The general Morse--Sard theorem additionally needs the
higher-regularity argument when the dimensions differ.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin`: a map between equal-dimensional
  spaces sends a set of nonsurjective derivative points to a null set.
* `TauCeti.Differentiable.addHaar_image_criticalPoints_eq_zero`: the critical values of a globally
  differentiable map between equal-dimensional spaces form a null set.
* `TauCeti.Differentiable.dense_compl_image_criticalPoints`: the regular values of such a map are
  dense.

The measure-theoretic input follows Sébastien Gouëzel's Mathlib formalization of the change of
variables theorem, itself based on Fremlin, *Measure Theory*, volume 2.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}
  (ν : Measure F) [IsAddHaarMeasure ν]

/-- **Sard's lemma in equal dimensions.** Let `E` and `F` be finite-dimensional real normed
spaces of equal dimension. If `f` is differentiable along `s` with derivative `f'`, and `f'` is
nowhere surjective on `s`, then `f '' s` has additive Haar measure zero in `F`.

Unlike the endomorphism version in Mathlib, the domain and codomain need not be the same normed
space and may carry unrelated norms and Haar measure normalizations. -/
theorem addHaar_image_eq_zero_of_not_surjective_fderivWithin
    (hdim : finrank ℝ E = finrank ℝ F)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, ¬ Surjective (f' x)) : ν (f '' s) = 0 := by
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim.symm
  let g : E → E := fun x ↦ e (f x)
  let g' : E → E →L[ℝ] E := fun x ↦ (e : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x := by
    intro x hx
    exact e.hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hdet : ∀ x ∈ s, (g' x).det = 0 := by
    intro x hx
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    apply hcrit x hx
    intro y
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hinj (e y)
    refine ⟨z, e.injective ?_⟩
    simpa only [g', ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hz
  have hnull : (addHaar : Measure E) (g '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero addHaar hg' hdet
  have hpreimage : ν (e ⁻¹' (g '' s)) = 0 :=
    (ContinuousLinearEquiv.quasiMeasurePreserving_addHaar ν addHaar e).preimage_null hnull
  have himage : g '' s = e '' (f '' s) := by
    rw [image_image]
  rw [himage, Set.preimage_image_eq _ e.injective] at hpreimage
  exact hpreimage

/-- The critical values of a differentiable map between equal-dimensional finite-dimensional real
normed spaces have additive Haar measure zero. A point is critical here exactly when the Fréchet
derivative is not surjective. -/
theorem Differentiable.addHaar_image_criticalPoints_eq_zero
    (hf : Differentiable ℝ f) (hdim : finrank ℝ E = finrank ℝ F) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  apply addHaar_image_eq_zero_of_not_surjective_fderivWithin ν hdim
  · intro x _
    exact (hf x).hasFDerivAt.hasFDerivWithinAt
  · exact fun x hx ↦ hx

/-- The regular values of a differentiable map between equal-dimensional finite-dimensional real
normed spaces are dense. Here the regular values are expressed as the complement of the image of
the points where the Fréchet derivative is not surjective. -/
theorem Differentiable.dense_compl_image_criticalPoints
    (hf : Differentiable ℝ f) (hdim : finrank ℝ E = finrank ℝ F) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ := by
  let t : Set F := f '' {x | ¬ Surjective (fderiv ℝ f x)}
  have ht : (addHaar : Measure F) t = 0 :=
    Differentiable.addHaar_image_criticalPoints_eq_zero (ν := addHaar) hf hdim
  have htc : ∀ᵐ x ∂(addHaar : Measure F), x ∈ tᶜ := ae_iff.mpr (by simpa using ht)
  simpa only [ofPred_mem_eq, t] using Measure.dense_of_ae htc

end TauCeti
