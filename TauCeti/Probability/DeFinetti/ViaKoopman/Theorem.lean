/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.CylinderMass
public import TauCeti.Probability.DeFinetti.ConditionalCommonEnding
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge

/-!
# de Finetti via Koopman operators and the shift-invariant σ-algebra

The summit of the Koopman route.

On path space the witness is `invariantConditionalProbabilityMeasure`, the conditional law of the
first coordinate given `MeasurableSpace.invariants (shift α)`. The block-cylinder mass computed in
`CylinderMass.lean` is exactly the hypothesis
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral` consumes, so the path-space
statement follows at once; `ConditionallyIIDWith.of_pathLaw` carries it to an arbitrary space.

## Main results

* `ContractableLaw.conditionallyIIDWith_invariantConditionalProbabilityMeasure` — the path-space
  form, with its
  witness;
* `conditionallyIID_of_contractable_viaKoopman` — a contractable process is conditionally i.i.d.;
* `deFinetti_viaKoopman` — an exchangeable process is conditionally i.i.d.

## How this route differs from `L²`

The two routes are independent at the import level and stay that way: nothing here reaches
`DeFinetti/ViaL2`. The mathematical difference is in what the block comparison rests on. The `L²`
route compares two selections *distributionally*, as an a.e. identity of conditional expectations
given the tail. This route uses actual invariance of the test event under the shift, and
`invariants_shift_lt_pathTail` shows those σ-algebras genuinely differ — strictly, already over
`Bool`. They are deliberately not unified into one σ-algebra-parametric theorem.

Both routes are finite-measure statements: these wrappers and `deFinetti_viaL2` alike ask only for
`[IsFiniteMeasure μ]`. Nothing in the Koopman chain needs more: the mean ergodic input and the
witness are both finite-measure statements.

## Source

No material is adapted from `cameronfreer/exchangeability`. Its Koopman development concludes the
mixture identity; the results here package Tau Ceti's joint-law disintegration, and are assembled
from this repository's own block transport, decoupling and factorization.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 5** (Koopman operators and
  invariant σ-algebras), whose milestone is `deFinetti_viaKoopman`.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The path-space form.** A contractable path law is conditionally i.i.d. with the conditional
law of the first coordinate given the shift-invariant σ-algebra as its witness. -/
theorem ContractableLaw.conditionallyIIDWith_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ) :
    ConditionallyIIDWith ρ (fun j (x : ℕ → α) => x j)
      (invariantConditionalProbabilityMeasure ρ) := by
  refine conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral
    (fun n => (measurable_pi_apply n).aemeasurable)
    ((measurable_invariants_invariantConditionalProbabilityMeasure).mono
      (MeasurableSpace.invariants_le (shift α)) le_rfl) ?_
  intro r k hk S hS B hB
  exact hρ.measure_inter_blockCylinder_eq_setLIntegral_of_measurableSet_invariants hk
    (measurable_invariants_invariantConditionalProbabilityMeasure hS) hB

/-- **A contractable process is conditionally i.i.d.**, via the Koopman route. -/
theorem conditionallyIID_of_contractable_viaKoopman [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ConditionallyIID μ X := by
  have hXae : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  -- Supplied for instance resolution below, not referenced by name.
  have : IsFiniteMeasure (pathLaw μ X) := by
    rw [pathLaw_def]
    exact Measure.isFiniteMeasure_map μ _
  exact ConditionallyIID.of_directing (ConditionallyIIDWith.of_pathLaw hX_meas
    ((hX.contractableLaw_pathLaw hXae).conditionallyIIDWith_invariantConditionalProbabilityMeasure))

/-- **de Finetti's theorem via Koopman operators.** An exchangeable process on a nonempty standard
Borel state space is conditionally i.i.d. -/
theorem deFinetti_viaKoopman [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) (hX : Exchangeable μ X) :
    ConditionallyIID μ X :=
  conditionallyIID_of_contractable_viaKoopman
    (hX.contractable fun n => (hX_meas n).aemeasurable) hX_meas

end Probability

end TauCeti

end
