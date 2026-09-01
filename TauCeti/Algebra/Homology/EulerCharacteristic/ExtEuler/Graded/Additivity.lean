/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Additivity of the graded Ext-Euler characteristic

The graded Ext-Euler characteristic is additive on short exact sequences in either variable.
The proof reads each Laurent coefficient as an ordinary Ext-Euler characteristic: the coefficient
of `q^j` is the Euler characteristic against the target shifted by `-j`.  Ordinary Ext-Euler
additivity then applies, after mapping a short exact sequence through the grading shift when the
sequence occurs in the second variable.  The admissibility of the middle term is supplied by the
extension-closure results of `TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic`.

## Main results

* `TauCeti.coeff_gradedExtEuler_eq_extEuler`: a Laurent coefficient is an ordinary Ext-Euler
  characteristic against one shifted target.
* `TauCeti.gradedExtEuler_shortExact₂` and `TauCeti.gradedExtEuler_shortExact₁`: additivity on
  short exact sequences in either variable.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.4--2.7, for the long
  exact Ext sequences underlying ordinary Euler additivity.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2, for the
  Laurent-polynomial-valued Ext-Euler form.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 6, "q-Euler form".
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C} {S : ShortComplex C}

/-! ### Coefficients and additivity -/

/-- The coefficient of `q^j` in the graded Ext-Euler characteristic is the ordinary Ext-Euler
characteristic against the target shifted by `-j`. -/
@[simp]
theorem coeff_gradedExtEuler_eq_extEuler {X Y : C}
    (h : IsGradedEulerAdmissible.{w} k e X Y) (j : ℤ) :
    (gradedExtEuler k e h).coeff j = extEuler.{w} k (h.isEulerAdmissible (-j)) := by
  obtain ⟨N, hN⟩ := h.bounded.exists_bound
  rw [coeff_gradedExtEuler k e h hN j,
    extEuler_eq k (h.isEulerAdmissible (-j)) (hN.isExtBoundedBy (-j))]
  clear hN
  induction N with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, truncatedExtEuler_succ, ih]

/-- The graded Ext-Euler characteristic is additive on a short exact sequence in its second
variable. -/
theorem gradedExtEuler_shortExact₂ (hS : S.ShortExact) (X : C)
    (h₁ : IsGradedEulerAdmissible.{w} k e X S.X₁)
    (h₃ : IsGradedEulerAdmissible.{w} k e X S.X₃) :
    gradedExtEuler k e (h₁.of_shortExact₂ hS h₃) =
      gradedExtEuler k e h₁ + gradedExtEuler k e h₃ := by
  ext j
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_gradedExtEuler_eq_extEuler h₁,
    coeff_gradedExtEuler_eq_extEuler (h₁.of_shortExact₂ hS h₃),
    coeff_gradedExtEuler_eq_extEuler h₃]
  exact extEuler_shortExact₂ (hS.map_of_exact (e ^ (-j)).functor) X
    (h₁.isEulerAdmissible (-j)) ((h₁.of_shortExact₂ hS h₃).isEulerAdmissible (-j))
    (h₃.isEulerAdmissible (-j))

/-- The graded Ext-Euler characteristic is additive on a short exact sequence in its first
variable. -/
theorem gradedExtEuler_shortExact₁ (hS : S.ShortExact) (Y : C)
    (h₁ : IsGradedEulerAdmissible.{w} k e S.X₁ Y)
    (h₃ : IsGradedEulerAdmissible.{w} k e S.X₃ Y) :
    gradedExtEuler k e (h₁.of_shortExact₂' hS h₃) =
      gradedExtEuler k e h₁ + gradedExtEuler k e h₃ := by
  ext j
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_gradedExtEuler_eq_extEuler h₁,
    coeff_gradedExtEuler_eq_extEuler (h₁.of_shortExact₂' hS h₃),
    coeff_gradedExtEuler_eq_extEuler h₃]
  exact extEuler_shortExact₁ hS ((e ^ (-j)).functor.obj Y)
    (h₁.isEulerAdmissible (-j)) ((h₁.of_shortExact₂' hS h₃).isEulerAdmissible (-j))
    (h₃.isEulerAdmissible (-j))

end TauCeti
