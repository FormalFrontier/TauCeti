/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Probability.DeFinetti.CondExpConvergence
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
public import TauCeti.Probability.Exchangeability.Basic

/-!
# The directing measure is the conditional law of every coordinate

`directingMeasure_ae_eq_condExp` (in `DirectingMeasure.lean`) identifies the directing measure with
the conditional law of the initial coordinate `X 0` given the tail σ-algebra. For a **contractable**
process the same holds for every coordinate. `Contractable.directingMeasure_ae_eq_condExp_coord`
promotes that identity from `X 0` to every `X m`, using the "extreme members agree on the tail"
collapse `Contractable.condExp_indicator_tailProcess_eq`.

This is the per-coordinate input to the de Finetti block-product factorisation: it is what lets the
single directing measure serve as the common conditional law of all coordinates.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/CondExpConvergence.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The directing measure is the conditional law of every coordinate.** For a contractable process
and any `m`, the real evaluation `ω ↦ (directingMeasure μ X ω).real B` is a version of the
conditional expectation of `𝟙_B ∘ X m` given the tail σ-algebra `tailProcess X`. -/
theorem Contractable.directingMeasure_ae_eq_condExp_coord [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) (m : ℕ)
    {B : Set α} (hB : MeasurableSet B) :
    (fun ω => (directingMeasure μ X ω).real B)
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X m | tailProcess X] :=
  (directingMeasure_ae_eq_condExp (tailProcess_le_ambient 0 fun k _ => hX_meas k)
      (hX_meas 0) hB).trans
    (hX.condExp_indicator_tailProcess_eq (j := 0) (k := m) hX_meas hB)

end Probability

end TauCeti
