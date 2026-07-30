/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Birkhoff averages of the `Lᵖ` composition operator

The Birkhoff sums and averages of the composition (Koopman) operator of a measure-preserving map
`T` on `Lᵖ` are elements of `Lᵖ`, while the ergodic theorems a probabilist states are about the
pointwise Birkhoff averages `birkhoffAverage ℝ T f n` of an observable. This file records that the
two agree: an `Lᵖ` Birkhoff average of `g` is represented by the pointwise Birkhoff average of the
coercion `⇑g`. For another representative `f =ᵐ[μ] ⇑g`, compose with Mathlib's
`Measure.QuasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq`.

## Main results

* `coeFn_iterate_compMeasurePreserving` — iterating the composition operator composes with the
  iterated transformation;
* `coeFn_birkhoffSum_compMeasurePreserving` and `coeFn_birkhoffAverage_compMeasurePreserving` —
  the Birkhoff sums and averages of the composition operator are represented by the pointwise
  Birkhoff sums and averages of the coercion of the argument.
-/

public section

noncomputable section

open Function MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω} {p : ℝ≥0∞}

/-- Iterating the `Lᵖ` composition operator composes with the iterated transformation. -/
theorem coeFn_iterate_compMeasurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) (n : ℕ) :
    ⇑((Lp.compMeasurePreserving (E := E) (p := p) T hT)^[n] g) =ᵐ[μ] ⇑g ∘ T^[n] := by
  rw [Lp.compMeasurePreserving_iterate hT n]
  exact Lp.coeFn_compMeasurePreserving g (hT.iterate n)

/-- The Birkhoff sums of the `Lᵖ` composition operator are represented by the pointwise Birkhoff
sums of the coercion of `g`. -/
theorem coeFn_birkhoffSum_compMeasurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (g : Lp E p μ) (n : ℕ) :
    ⇑(birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g) =ᵐ[μ]
      birkhoffSum T (⇑g) n := by
  induction n with
  | zero =>
      simp only [birkhoffSum_zero', Pi.zero_apply]
      exact Lp.coeFn_zero E p μ
  | succ n ih =>
      rw [birkhoffSum_succ]
      filter_upwards [ih, coeFn_iterate_compMeasurePreserving hT g n,
        Lp.coeFn_add (birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g)
          (id ((Lp.compMeasurePreserving (E := E) (p := p) T hT)^[n] g))] with ω hsum hiter hadd
      rw [hadd, birkhoffSum_succ]
      exact congrArg₂ _ hsum hiter

/-- The Birkhoff averages of the `Lᵖ` composition operator are represented by the pointwise
Birkhoff averages of the coercion of `g`. -/
theorem coeFn_birkhoffAverage_compMeasurePreserving [NormedSpace ℝ E] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) (g : Lp E p μ) (n : ℕ) :
    ⇑(birkhoffAverage ℝ (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g) =ᵐ[μ]
      birkhoffAverage ℝ T (⇑g) n := by
  filter_upwards [coeFn_birkhoffSum_compMeasurePreserving hT g n,
    Lp.coeFn_smul ((n : ℝ)⁻¹)
      (birkhoffSum (Lp.compMeasurePreserving (E := E) (p := p) T hT) id n g)] with ω hsum hsmul
  rw [birkhoffAverage, hsmul, Pi.smul_apply, hsum, birkhoffAverage]

end Probability

end TauCeti
