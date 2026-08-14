/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFun.PosDef
public import TauCeti.Analysis.PositiveDefinite.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Characteristic functions as positive-definite functions

This file connects the quadratic-form positivity calculation for characteristic functions to
Tau Ceti's generic positive-definite-function predicate. If the involution on an additive group is
negation, then Mathlib's characteristic function `MeasureTheory.charFun μ` of a finite measure is
`TauCeti.IsPositiveDefinite`.

Together with Mathlib's continuity theorem for characteristic functions, this gives the "finite
measure's Fourier transform is continuous positive-definite" bridge lemma requested in Part C of
the `OneParameterSemigroups` roadmap, before the harder converse direction of Bochner's theorem.

## Main declarations

* `TauCeti.charFun_isPositiveDefinite_of_star_eq_neg`: `charFun μ` is positive definite for any
  explicit `star = -` involution.
* `TauCeti.continuous_charFun_and_isPositiveDefinite_of_star_eq_neg`: the paired continuity and
  positive-definiteness package.
-/

public section

open MeasureTheory

namespace TauCeti

open scoped ComplexOrder

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic function of a finite measure is positive definite for any additive-group
involution that is explicitly negation. This is the generic-predicate form of
`charFun_fintype_sum_mul_conj_nonneg`, using
`F (vᵢ + star vⱼ) = charFun μ (vᵢ - vⱼ)`. -/
theorem charFun_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E] (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite (MeasureTheory.charFun μ) := by
  intro n c v
  have h := charFun_fintype_sum_mul_conj_nonneg (μ := μ) c v
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [hstar, sub_eq_add_neg]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic function of a finite measure on a second-countable real inner product space
is continuous and positive definite, provided the chosen involution is negation. This is the
forward bridge toward Bochner's theorem in the language of `TauCeti.IsPositiveDefinite`. -/
theorem continuous_charFun_and_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous (MeasureTheory.charFun μ) ∧ IsPositiveDefinite (MeasureTheory.charFun μ) :=
  ⟨MeasureTheory.continuous_charFun, charFun_isPositiveDefinite_of_star_eq_neg hstar⟩

end Normed

end TauCeti
