/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The Morse index

This file defines the Hessian quadratic form of a real-valued function on a real normed space and,
in finite dimensions, its **Morse index**: the negative index of inertia of the Hessian.  Thus the
index is the maximal dimension of a subspace on which the Hessian is negative-definite.

The Hessian quadratic form used here is

`v ↦ fderiv ℝ (fderiv ℝ f) x v v`.

Some statements of the Morse lemma put a factor `2⁻¹` in front of this form.  That positive factor
does not change its negative index, by
`TauCeti.QuadraticForm.sigNeg_smul_of_pos`.  In particular the convention agrees with the normal
form in `TauCeti.Analysis.Calculus.Morse.NormalForm`.

The definition is made at every point, not only at a critical point, since the index of the
Hessian is meaningful there and this keeps regularity and criticality hypotheses on the results
that use them.  It follows Mathlib's total `sigNeg`, whose value is defined to be zero outside
finite dimensions; all results interpreting the value as a Morse-theoretic index assume finite
dimension.  At a nondegenerate critical point the Hessian quadratic form is nondegenerate, so its
positive and negative indices add to the dimension.  Consequently index zero is equivalent to a
positive-definite Hessian and full index is equivalent to a negative-definite Hessian.

The index depends only on the germ of the function and is invariant under a twice continuously
differentiable change of coordinates with invertible derivative.  Finally, Sylvester's law of
inertia puts the Hessian into a diagonal normal form with weights `±1`; the number of negative
weights is exactly the Morse index.  This supplies the integer grading of critical points needed
by the Morse complex in Lane M of the analytic Heegaard Floer roadmap.

## Main declarations

* `TauCeti.hessianQuadraticForm`: the quadratic form defined by the Hessian at a point.
* `TauCeti.morseIndex`: the negative index of inertia of the Hessian quadratic form.
* `TauCeti.morseIndex_comp`: invariance under a change of coordinates.
* `TauCeti.IsNondegenerateCriticalPoint.hessianQuadraticForm_nondegenerate`: the Hessian
  quadratic form at a nondegenerate critical point is nondegenerate.
* `TauCeti.IsNondegenerateCriticalPoint.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero`:
  index zero characterizes a positive-definite Hessian at a nondegenerate critical point.
* `TauCeti.IsNondegenerateCriticalPoint.exists_hessianQuadraticForm_equivalent_weightedSumSquares`:
  the Hessian has a diagonal `±1` normal form whose negative weights count the index.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function Module Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : E → ℝ} {x : E}

/-- The **Hessian quadratic form** of `f` at `x`, sending `v` to the second derivative of `f` at
`x` evaluated twice on `v`.  The definition uses Mathlib's totalized Fréchet derivative, so no
regularity hypothesis is needed to form it. -/
noncomputable def hessianQuadraticForm (f : E → ℝ) (x : E) : QuadraticForm ℝ E :=
  (fderiv ℝ (fderiv ℝ f) x).toBilinForm.toQuadraticMap

/-- The Hessian quadratic form evaluates the second derivative twice on the same vector. -/
@[simp]
theorem hessianQuadraticForm_apply (f : E → ℝ) (x v : E) :
    hessianQuadraticForm f x v = fderiv ℝ (fderiv ℝ f) x v v := by
  simp only [hessianQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
    ContinuousLinearMap.toBilinForm_apply]

/-- The Hessian quadratic form depends only on the germ of the function at the point. -/
theorem hessianQuadraticForm_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    hessianQuadraticForm f x = hessianQuadraticForm g x := by
  rw [hessianQuadraticForm, hessianQuadraticForm, hfg.fderiv.fderiv_eq]

/-- At a critical point the Hessian quadratic form pulls back along the derivative of a `C²`
change of variables. -/
theorem hessianQuadraticForm_comp {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b) (hcrit : fderiv ℝ f (φ b) = 0) :
    hessianQuadraticForm (f ∘ φ) b =
      (hessianQuadraticForm f (φ b)).comp (fderiv ℝ φ b).toLinearMap := by
  ext v
  simp only [hessianQuadraticForm_apply, QuadraticMap.comp_apply]
  rw [fderiv_fderiv_comp_apply_of_fderiv_eq_zero hf hφ hcrit]
  simp only [ContinuousLinearMap.coe_coe]

/-- The **Morse index** of `f` at `x` is the negative index of inertia of its Hessian quadratic
form.  In finite dimensions it is equivalently the maximal dimension of a subspace on which the
Hessian is negative-definite.  Following Mathlib's `sigNeg`, its value is defined to be zero in
infinite dimensions; the Morse-theoretic results below assume finite dimension. -/
noncomputable def morseIndex (f : E → ℝ) (x : E) : ℕ :=
  sigNeg (hessianQuadraticForm f x)

/-- The Morse index is the negative index of inertia of the Hessian quadratic form. -/
theorem morseIndex_def : morseIndex f x = sigNeg (hessianQuadraticForm f x) := by
  simp [morseIndex]

/-- The Morse index depends only on the germ of the function at the point. -/
theorem morseIndex_congr_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    morseIndex f x = morseIndex g x := by
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_congr_of_eventuallyEq hfg]

/-- The Morse index is invariant under a `C²` change of coordinates with invertible derivative.
Criticality is needed because it removes the first-order term from the second-order chain rule. -/
theorem morseIndex_comp {φ : F → E} {b : F} (hf : ContDiffAt ℝ 2 f (φ b))
    (hφ : ContDiffAt ℝ 2 φ b)
    (hcrit : fderiv ℝ f (φ b) = 0) (hinv : (fderiv ℝ φ b).IsInvertible) :
    morseIndex (f ∘ φ) b = morseIndex f (φ b) := by
  obtain ⟨e, he⟩ := hinv
  rw [morseIndex_def, morseIndex_def, hessianQuadraticForm_comp hf hφ hcrit, ← he]
  exact (QuadraticMap.Equivalent.sigNeg_eq
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv
      (hessianQuadraticForm f (φ b)) e.toLinearEquiv⟩).symm

/-- At a nondegenerate critical point, the Hessian quadratic form is nondegenerate. -/
theorem IsNondegenerateCriticalPoint.hessianQuadraticForm_nondegenerate
    (h : IsNondegenerateCriticalPoint f x) : (hessianQuadraticForm f x).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  let B := (fderiv ℝ (fderiv ℝ f) x).toBilinForm
  have hsymm : B.IsSymm := by
    refine ⟨?_⟩
    exact h.contDiffAt.isSymmSndFDerivAt (by norm_num)
  rw [hessianQuadraticForm, LinearMap.BilinForm.radical_toQuadraticMap B hsymm]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp h.separatingLeft

/-- The Morse index is at most the dimension of the ambient space. -/
theorem morseIndex_le_finrank [FiniteDimensional ℝ E] :
    morseIndex f x ≤ Module.finrank ℝ E := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := hessianQuadraticForm f x)
  rw [morseIndex_def]
  omega

/-- At a nondegenerate critical point, the positive index of the Hessian and the Morse index add
to the dimension of the ambient space. -/
theorem IsNondegenerateCriticalPoint.sigPos_hessianQuadraticForm_add_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    sigPos (hessianQuadraticForm f x) + morseIndex f x = Module.finrank ℝ E := by
  have hsig := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := hessianQuadraticForm f x)
  rw [h.hessianQuadraticForm_nondegenerate.radical_eq_bot, finrank_bot, add_zero] at hsig
  simpa only [morseIndex_def] using hsig

/-- At a nondegenerate critical point, the Hessian is positive-definite exactly when the Morse
index is zero. -/
theorem IsNondegenerateCriticalPoint.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    (hessianQuadraticForm f x).PosDef ↔ morseIndex f x = 0 := by
  rw [TauCeti.QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    h.hessianQuadraticForm_nondegenerate.radical_eq_bot, morseIndex_def]
  simp only [eq_self, and_true]

/-- At a nondegenerate critical point, the Hessian is negative-definite exactly when the Morse
index is the dimension of the ambient space. -/
theorem IsNondegenerateCriticalPoint.neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    (-hessianQuadraticForm f x).PosDef ↔ morseIndex f x = Module.finrank ℝ E := by
  rw [TauCeti.QuadraticForm.posDef_iff_sigNeg_eq_zero_and_radical_eq_bot,
    QuadraticMap.radical_neg, h.hessianQuadraticForm_nondegenerate.radical_eq_bot, sigNeg_neg]
  simp only [eq_self, and_true]
  have hsum := h.sigPos_hessianQuadraticForm_add_morseIndex_eq_finrank
  omega

/-- At a nondegenerate critical point, the Hessian quadratic form has a diagonal normal form with
every weight equal to `-1` or `1`, and the negative weights are counted by the Morse index.  This
is Sylvester's law of inertia applied to the Hessian. -/
theorem IsNondegenerateCriticalPoint.exists_hessianQuadraticForm_equivalent_weightedSumSquares
    [FiniteDimensional ℝ E] (h : IsNondegenerateCriticalPoint f x) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (hessianQuadraticForm f x)
          (QuadraticMap.weightedSumSquares ℝ w) ∧
        morseIndex f x = {i | w i < 0}.ncard := by
  let B := (fderiv ℝ (fderiv ℝ f) x).toBilinForm
  have hsymm : B.IsSymm := by
    refine ⟨?_⟩
    exact h.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hassoc : (QuadraticMap.associated (R := ℝ) (hessianQuadraticForm f x)).SeparatingLeft := by
    rw [hessianQuadraticForm, QuadraticMap.associated_left_inverse (S := ℝ) hsymm.eq]
    exact h.separatingLeft
  obtain ⟨w, hw, hequiv⟩ :=
    QuadraticForm.equivalent_one_neg_one_weighted_sum_squared
      (hessianQuadraticForm f x) hassoc
  refine ⟨w, hw, hequiv, ?_⟩
  simpa only [morseIndex_def] using QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv

end TauCeti
