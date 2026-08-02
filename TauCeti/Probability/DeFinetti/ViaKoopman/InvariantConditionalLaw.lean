/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Kernel.ProbabilityMeasure
public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# The invariant conditional law

On path space, the conditional law of the initial coordinate given the **shift-invariant**
σ-algebra `MeasurableSpace.invariants (shift α)`, bundled as a random probability measure.

It is named a *conditional law*, not a directing measure: this file does not prove that it directs
the process, and Tau Ceti reserves "directing measure" for a witness of `ConditionallyIIDWith`.
That name belongs with the theorem, not here. It is deliberately a separate object from
`directingProbabilityMeasure`, which conditions on the process tail: the two σ-algebras are not
interchangeable — `invariants_shift_le_pathTail` is one-sided, and `invariants_shift_lt_pathTail`
shows the inclusion is strict over `Bool` — so sharing the underlying construction asserts nothing
about the witnesses being equal. Whether they agree a.e. is a separate question, not settled here.

## Main results

* `invariantConditionalProbabilityMeasure` — the witness;
* `invariantConditionalProbabilityMeasure_toMeasure` — its underlying measure, the abstraction
  boundary that lets measure-level operations cross without unfolding the definition;
* `measurable_invariants_invariantConditionalProbabilityMeasure` — measurability relative to the
  invariant σ-algebra;
* `measurable_invariantConditionalProbabilityMeasure` — the ambient corollary;
* `invariantConditionalProbabilityMeasure_ae_eq_condExp` — the characteristic property: evaluated on
  a measurable set, it is a version of the conditional expectation of that set's indicator at
  coordinate `0`, given the invariant σ-algebra.

Nothing here proves that this witness directs the process; that is the Koopman block
factorization, which is not part of this file.

Adapted from `DeFinetti/DirectingMeasure/Basic.lean`, which carries the attribution to
`cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/DirectingMeasure.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). The specialization here is the conditioning
σ-algebra: that file conditions on `tailProcess X`, this one on
`MeasurableSpace.invariants (shift α)`, with the shared bundling factored through
`Kernel.probabilityMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- The **invariant directing measure**: the conditional law of the initial coordinate `x 0` given
the shift-invariant σ-algebra, bundled as a `ProbabilityMeasure`.

The invariant σ-algebra is a *non-ambient* `MeasurableSpace` on `ℕ → α`, so it must be pinned at
every layer — both on the bundling wrapper and on the `condDistrib` whose fibres it bundles. -/
def invariantConditionalProbabilityMeasure (ρ : Measure (ℕ → α)) [IsFiniteMeasure ρ] :
    (ℕ → α) → ProbabilityMeasure α :=
  Kernel.probabilityMeasure (mβ := MeasurableSpace.invariants (shift α))
    (@condDistrib (ℕ → α) (ℕ → α) α _ _ _ _ (MeasurableSpace.invariants (shift α))
      (fun x => x 0) id ρ _)

/-- The underlying measure is the invariant-indexed `condDistrib` fibre.

This is the abstraction boundary: downstream measure-level reasoning goes through this lemma rather
than unfolding the definition. -/
@[simp]
theorem invariantConditionalProbabilityMeasure_toMeasure {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (x : ℕ → α) :
    (invariantConditionalProbabilityMeasure ρ x : Measure α)
      = (@condDistrib (ℕ → α) (ℕ → α) α _ _ _ _ (MeasurableSpace.invariants (shift α))
          (fun x => x 0) id ρ _) x := by
  simp only [invariantConditionalProbabilityMeasure, Kernel.probabilityMeasure_toMeasure]

/-- The invariant conditional law is measurable with respect to the **invariant** σ-algebra. -/
theorem measurable_invariants_invariantConditionalProbabilityMeasure {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] :
    Measurable[MeasurableSpace.invariants (shift α)] (invariantConditionalProbabilityMeasure ρ) :=
  Kernel.measurable_probabilityMeasure (mβ := MeasurableSpace.invariants (shift α))
    (@condDistrib (ℕ → α) (ℕ → α) α _ _ _ _ (MeasurableSpace.invariants (shift α))
      (fun x => x 0) id ρ _)

/-- The ambient corollary, by monotonicity along `MeasurableSpace.invariants_le`. -/
@[fun_prop]
theorem measurable_invariantConditionalProbabilityMeasure {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] :
    Measurable (invariantConditionalProbabilityMeasure ρ) :=
  measurable_invariants_invariantConditionalProbabilityMeasure.mono
    (MeasurableSpace.invariants_le _) le_rfl

/-- **Characteristic property.** Evaluated on a measurable set `B`, the invariant directing measure
is a version of the conditional expectation of `𝟙_B ∘ (· 0)` given the shift-invariant σ-algebra.

This is what identifies the witness: everything the Koopman route needs to know about it is that
its evaluations are these conditional expectations. -/
theorem invariantConditionalProbabilityMeasure_ae_eq_condExp {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] {B : Set α} (hB : MeasurableSet B) :
    (fun x => ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real B)
      =ᵐ[ρ] ρ[Set.indicator B (fun _ => (1 : ℝ)) ∘ (fun x : ℕ → α => x 0) |
        MeasurableSpace.invariants (shift α)] := by
  have hid : @Measurable (ℕ → α) (ℕ → α) _ (MeasurableSpace.invariants (shift α)) id :=
    measurable_id'' (MeasurableSpace.invariants_le (shift α))
  have hcoord : Measurable fun x : ℕ → α => x 0 := measurable_pi_apply 0
  have h := condDistrib_ae_eq_condExp (μ := ρ) (Y := fun x : ℕ → α => x 0)
    (X := (id : (ℕ → α) → (ℕ → α))) hid hcoord hB
  rw [MeasurableSpace.comap_id] at h
  have hpre : ((fun x : ℕ → α => x 0) ⁻¹' B).indicator (fun _ => (1 : ℝ))
      = Set.indicator B (fun _ => (1 : ℝ)) ∘ (fun x : ℕ → α => x 0) := by
    funext y
    exact Set.indicator_comp_right (g := fun _ => (1 : ℝ)) (fun x : ℕ → α => x 0)
  rw [hpre] at h
  refine h.symm.trans ?_ |>.symm
  filter_upwards with x
  simp only [invariantConditionalProbabilityMeasure, Kernel.probabilityMeasure_toMeasure, id_eq]

end Probability

end TauCeti
