/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.DeFinetti.BlockFactorization
public import TauCeti.Probability.DeFinetti.ConditionalCommonEnding

/-!
# Work in progress: the directing-measure joint-rectangle factorization
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The event that the directing measure lands in `S` is a tail event: this is what lets the
conditional factorization be integrated against it. -/
private theorem measurableSet_tailProcess_directingProbabilityMeasure_preimage
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    MeasurableSet[tailProcess X] (directingProbabilityMeasure μ X ⁻¹' S) :=
  measurable_tailProcess_directingProbabilityMeasure hS

/-- **Joint-rectangle factorization, prefix case.** The joint law of the directing measure with a
length-`r` prefix block agrees with the disintegration on rectangles `S ×ˢ ∏ i, B i`. -/
private theorem jointRectangle_prefix
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    (μ.map fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X i ω))
        (S ×ˢ Set.univ.pi B)
      = (μ.bind fun ω =>
          (Measure.dirac (directingProbabilityMeasure μ X ω)).prod
            (ProbabilityMeasure.pi fun _ : Fin r =>
              directingProbabilityMeasure μ X ω).toMeasure)
        (S ×ˢ Set.univ.pi B) := by
  sorry

end Probability

end TauCeti
