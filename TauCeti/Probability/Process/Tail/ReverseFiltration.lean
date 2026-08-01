/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Process.Tail.Basic
public import TauCeti.Probability.Martingale.Reverse

/-!
# Process tails as infima of reverse filtrations

This file records the Exchangeability roadmap Layer 2 adapter specializing finite-horizon reverse
filtrations to the process-tail family `tailFamily X`, and identifying the process tail σ-algebra
as the infimum of their time-zero levels.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} {β : ℕ → Type*} [MeasurableSpace Ω] [∀ k, MeasurableSpace (β k)]

/-- Reverse filtration of the process-tail family on the finite horizon `N`. -/
def tailReverseFiltration (X : (k : ℕ) → Ω → β k) (hX : ∀ k, Measurable (X k))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
  MeasureTheory.revFiltration (tailFamily X) (tailFamily_antitone X)
    (fun n => tailFamily_le_ambient n fun k _ => hX k) N

/-- Level equation for the finite-horizon reverse filtration of a process tail. -/
@[simp]
theorem tailReverseFiltration_apply (X : (k : ℕ) → Ω → β k) (hX : ∀ k, Measurable (X k)) (N n : ℕ) :
    (tailReverseFiltration X hX N) n = tailFamily X (N - n) := by
  simp only [tailReverseFiltration, MeasureTheory.revFiltration_apply]

/-- The process tail is the infimum of the time-zero levels of the finite-horizon reverse
filtrations attached to `tailFamily X`. -/
theorem tailProcess_eq_iInf_revFiltration (X : (k : ℕ) → Ω → β k) (hX : ∀ k, Measurable (X k)) :
    tailProcess X = ⨅ N : ℕ, (tailReverseFiltration X hX N) 0 := by
  rw [tailProcess_eq_iInf_tailFamily]
  simp only [tailReverseFiltration_apply, tsub_zero]

end Probability

end TauCeti
