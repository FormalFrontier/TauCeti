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
# The invariant directing measure

On path space, the conditional law of the initial coordinate given the **shift-invariant**
σ-algebra `MeasurableSpace.invariants (shift α)`, bundled as a random probability measure.

This is the witness the Koopman route names. It is deliberately a separate object from
`directingProbabilityMeasure`, which conditions on the process tail: the two σ-algebras are not
interchangeable — `invariants_shift_le_pathTail` is one-sided, and `invariants_shift_lt_pathTail`
shows the inclusion is strict over `Bool` — so sharing the underlying construction asserts nothing
about the witnesses being equal. Whether they agree a.e. is a separate question, not settled here.

## Main results

* `invariantDirectingProbabilityMeasure` — the witness;
* `measurable_invariants_invariantDirectingProbabilityMeasure` — measurability relative to the
  invariant σ-algebra;
* `measurable_invariantDirectingProbabilityMeasure` — the ambient corollary;
* `invariantDirectingProbabilityMeasure_ae_eq_condExp` — the characteristic property: evaluated on
  a measurable set, it is a version of the conditional expectation of that set's indicator at
  coordinate `0`, given the invariant σ-algebra.

Nothing here proves that this witness directs the process; that is the Koopman block
factorization, which is not part of this file.
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
def invariantDirectingProbabilityMeasure (ρ : Measure (ℕ → α)) [IsFiniteMeasure ρ] :
    (ℕ → α) → ProbabilityMeasure α :=
  Kernel.probabilityMeasure (mβ := MeasurableSpace.invariants (shift α))
    (@condDistrib (ℕ → α) (ℕ → α) α _ _ _ _ (MeasurableSpace.invariants (shift α))
      (fun x => x 0) id ρ _)

/-- The invariant directing measure is measurable with respect to the **invariant** σ-algebra. -/
theorem measurable_invariants_invariantDirectingProbabilityMeasure {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] :
    Measurable[MeasurableSpace.invariants (shift α)] (invariantDirectingProbabilityMeasure ρ) :=
  Kernel.measurable_probabilityMeasure (mβ := MeasurableSpace.invariants (shift α))
    (@condDistrib (ℕ → α) (ℕ → α) α _ _ _ _ (MeasurableSpace.invariants (shift α))
      (fun x => x 0) id ρ _)

/-- The ambient corollary, by monotonicity along `MeasurableSpace.invariants_le`. -/
@[fun_prop]
theorem measurable_invariantDirectingProbabilityMeasure {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] :
    Measurable (invariantDirectingProbabilityMeasure ρ) :=
  measurable_invariants_invariantDirectingProbabilityMeasure.mono
    (MeasurableSpace.invariants_le _) le_rfl

/-- **Characteristic property.** Evaluated on a measurable set `B`, the invariant directing measure
is a version of the conditional expectation of `𝟙_B ∘ (· 0)` given the shift-invariant σ-algebra.

This is what identifies the witness: everything the Koopman route needs to know about it is that
its evaluations are these conditional expectations. -/
theorem invariantDirectingProbabilityMeasure_ae_eq_condExp {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] {B : Set α} (hB : MeasurableSet B) :
    (fun x => ((invariantDirectingProbabilityMeasure ρ x : Measure α)).real B)
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
    by_cases hy : (y 0 : α) ∈ B <;> simp [Set.mem_preimage, hy]
  rw [hpre] at h
  refine h.symm.trans ?_ |>.symm
  filter_upwards with x
  simp only [invariantDirectingProbabilityMeasure, Kernel.probabilityMeasure_toMeasure, id_eq]

end Probability

end TauCeti
