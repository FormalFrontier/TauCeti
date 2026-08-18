/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the barycenter is a `Measure.bind` against the measurable countable-power kernel, and
-- its values are exchangeable path laws.
public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.Exchangeability.PathSpace.Law.Basic
-- Public: `ExchangeableLaw.existsUnique_mixingLaw` is the path-law form of `deFinetti_mixture`.
public import TauCeti.Probability.DeFinetti.Representation
-- Non-public: used only inside proofs — the canonical conditionally i.i.d. construction that
-- realizes a barycenter as a path law, and the process/path-law bridge.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge

/-!
# The de Finetti barycenter of a mixing law

De Finetti's representation is a map in one direction and a theorem in the other. This file builds
the map. For a measure `π` on `ProbabilityMeasure α` — a *mixing law* — the **de Finetti
barycenter**

```text
deFinettiBarycenter π = ∫ P^{⊗ℕ} dπ(P)
```

is the `Measure.bind` of `π` against the countable-power kernel `P ↦ P^{⊗ℕ}`, equivalently the
barycenter (`Measure.join`) of the pushforward of `π` along `P ↦ P^{⊗ℕ}`; that second reading is
the one that makes the representation an *ergodic decomposition*, since every `P^{⊗ℕ}` is an
extreme exchangeable law (`infinitePi_mem_extremePoints_exchangeable`). The definition accepts an
arbitrary measure `π`; when `π` is a probability measure the barycenter is the law on `ℕ → α` of a
sequence drawn i.i.d. from a `π`-random probability measure.

The map is affine in the mixing law — `deFinettiBarycenter_add` and Mathlib's `Measure.bind_smul`
— sends probability measures to exchangeable probability measures, and, by de Finetti's theorem,
hits every exchangeable probability law exactly once
(`ExchangeableLaw.existsUnique_mixingLaw`). The packaging of that bijection as an equivalence, and
its restriction to point masses, is in `TauCeti.Probability.DeFinetti.Correspondence`.

This is the object the Layer 8 bullet of `TauCetiRoadmap/Exchangeability/README.md` — "package
`p ↦ p^{⊗ℕ}` and the de Finetti barycenter as an affine correspondence between mixing laws and
exchangeable path laws" — asks for. The expression `π.bind (P ↦ P^{⊗ℕ})` already occurs unnamed
throughout the de Finetti development (`deFinetti_mixture`, `mixedIID_mixingLaw_unique`,
`Measure.ext_of_bind_infinitePi_eq`); naming it is what lets the correspondence be stated.

## Main results

* `deFinettiBarycenter` — the mixture of countable powers along a mixing law.
* `deFinettiBarycenter_dirac` — a point mass mixes to a single i.i.d. law.
* `deFinettiBarycenter_zero`, `deFinettiBarycenter_add`, `deFinettiBarycenter_smul` — affinity in
  the mixing law.
* `exchangeableLaw_deFinettiBarycenter` — every barycenter of a mixing probability law is an
  exchangeable path law.
* `ExchangeableLaw.existsUnique_mixingLaw` — conversely, an exchangeable probability law on
  `ℕ → α` is the barycenter of exactly one mixing law, for `α` standard Borel.

## References

* Olav Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Theorem 1.1.

No material is adapted from `cameronfreer/exchangeability`, which carries the mixture
representation only as an unnamed `bind` expression and does not package the correspondence.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The **de Finetti barycenter** of a mixing law `π` on `ProbabilityMeasure α`: the measure
`∫ P^{⊗ℕ} dπ(P)` on `ℕ → α` mixing the countable powers against `π`. For `π` a probability
measure this is the law of a sequence drawn i.i.d. from a `π`-random probability measure. -/
def deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) : Measure (ℕ → α) :=
  π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)

/-- The barycenter unfolded as a `Measure.bind` against the countable-power kernel. This is the
form in which the surrounding development states the mixture representation, so it is the bridge
to `deFinetti_mixture`, `mixedIID_mixingLaw_unique` and `Measure.ext_of_bind_infinitePi_eq`. -/
theorem deFinettiBarycenter_def (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter π = π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  (rfl)

/-- The barycenter as the `Measure.join` of the pushforward of the mixing measure along
`P ↦ P^{⊗ℕ}`: the mixture representation read as a barycenter of measures on `ℕ → α` rather than
of measures on `α`. For `π` a probability measure this pushforward is the law of `P^{⊗ℕ}` under a
`π`-random `P`. -/
theorem deFinettiBarycenter_eq_join_map (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter π =
      (π.map fun P : ProbabilityMeasure α =>
        Measure.infinitePi fun _ : ℕ => (P : Measure α)).join :=
  (rfl)

/-- Evaluation of a barycenter on a measurable set: the `π`-average of the countable-power
masses. -/
theorem deFinettiBarycenter_apply (π : Measure (ProbabilityMeasure α)) {s : Set (ℕ → α)}
    (hs : MeasurableSet s) :
    deFinettiBarycenter π s =
      ∫⁻ P, (Measure.infinitePi fun _ : ℕ => (P : Measure α)) s ∂π :=
  Measure.bind_apply hs TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable

/-- A point mass mixing law has the corresponding i.i.d. law as its barycenter. -/
@[simp]
theorem deFinettiBarycenter_dirac (P : ProbabilityMeasure α) :
    deFinettiBarycenter (Measure.dirac P) = Measure.infinitePi fun _ : ℕ => (P : Measure α) :=
  Measure.dirac_bind TauCeti.MeasureTheory.measurable_infinitePi_const P

/-- The barycenter of a probability mixing law is a probability measure: every countable power of
a probability measure is one, so the mixture keeps the total mass of `π`. -/
instance isProbabilityMeasure_deFinettiBarycenter (π : Measure (ProbabilityMeasure α))
    [IsProbabilityMeasure π] : IsProbabilityMeasure (deFinettiBarycenter π) :=
  isProbabilityMeasure_bind TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable
    (.of_forall fun _ => inferInstance)

/-- **The zero mixing law has the zero barycenter.** -/
@[simp]
theorem deFinettiBarycenter_zero : deFinettiBarycenter (0 : Measure (ProbabilityMeasure α)) = 0 :=
  Measure.bind_zero_left _

/-- **The barycenter is additive in the mixing law.** -/
@[simp]
theorem deFinettiBarycenter_add (π₁ π₂ : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter (π₁ + π₂) = deFinettiBarycenter π₁ + deFinettiBarycenter π₂ := by
  simp only [deFinettiBarycenter_def]
  rw [← Measure.sum_cond π₁ π₂,
    Measure.bind_sum _ _ TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable,
    Measure.sum_bool]
  rfl

/-- **The barycenter is homogeneous in the mixing law.** -/
@[simp]
theorem deFinettiBarycenter_smul (c : ℝ≥0∞) (π : Measure (ProbabilityMeasure α)) :
    deFinettiBarycenter (c • π) = c • deFinettiBarycenter π :=
  Measure.bind_smul c π _

/-- **A barycenter is an exchangeable path law.** Drawing `P` from `π` and then an i.i.d.
`P`-sequence produces a law invariant under every permutation of the time coordinate.

The witness is the canonical conditionally i.i.d. construction `iidMixtureLaw π id`, whose
coordinate process is exchangeable and whose path law is this barycenter. -/
theorem exchangeableLaw_deFinettiBarycenter {π : Measure (ProbabilityMeasure α)}
    [IsProbabilityMeasure π] : ExchangeableLaw (deFinettiBarycenter π) := by
  have := isProbabilityMeasure_iidMixtureLaw (π := π) (P := id) measurable_id
  have hX := exchangeable_iidMixtureLaw (π := π) (P := id) measurable_id
  have hcoord : ∀ n, AEMeasurable
      (fun ω : ProbabilityMeasure α × (ℕ → α) => ω.2 n) (iidMixtureLaw π id) :=
    fun n => ((measurable_pi_apply n).comp measurable_snd).aemeasurable
  have hlaw := (exchangeable_iff_exchangeableLaw_pathLaw
    (X := fun n (ω : ProbabilityMeasure α × (ℕ → α)) => ω.2 n) hcoord).mp hX
  rw [pathLaw_iidMixtureLaw (π := π) (P := id) measurable_id] at hlaw
  simpa [deFinettiBarycenter_def] using hlaw

/-- **The mixing law of an exchangeable path law.** Over a standard Borel state space, an
exchangeable probability measure on `ℕ → α` is the de Finetti barycenter of exactly one mixing
law.

This is the path-law form of `deFinetti_mixture`, obtained by taking the coordinate process of
`ρ` itself: existence is de Finetti's theorem and uniqueness is injectivity of the mixture. Like
`deFinetti_mixture`, it needs no nonemptiness hypothesis on the state space. -/
theorem ExchangeableLaw.existsUnique_mixingLaw [StandardBorelSpace α] {ρ : Measure (ℕ → α)}
    [IsProbabilityMeasure ρ] (hρ : ExchangeableLaw ρ) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure α), ρ = deFinettiBarycenter π := by
  have hcoord : ∀ n, Measurable fun x : ℕ → α => x n := fun n => measurable_pi_apply n
  have hpath : pathLaw ρ (fun n (x : ℕ → α) => x n) = ρ := by simp [pathLaw_def]
  have hexch : Exchangeable ρ (fun n (x : ℕ → α) => x n) :=
    (exchangeable_iff_exchangeableLaw_pathLaw fun n => (hcoord n).aemeasurable).2
      (by simpa [pathLaw_def] using hρ)
  simpa [hpath, deFinettiBarycenter_def] using
    deFinetti_mixture hexch fun n => (hcoord n).aemeasurable

end Probability

end TauCeti
