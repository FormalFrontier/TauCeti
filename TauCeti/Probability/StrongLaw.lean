/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.StrongLaw
-- Public: the statement is about `Measure.infinitePi`; the proof uses `iIndepFun_infinitePi`.
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The strong law of large numbers on a countable product space

Mathlib's `ProbabilityTheory.strong_law_ae` takes a sequence of pairwise independent, identically
distributed, integrable random variables on an abstract probability space. The canonical carrier of
such a sequence is the countable power `Measure.infinitePi fun _ : ℕ => Q` with its coordinate maps,
and this file specializes the strong law to it.

## Main results

* `TauCeti.Probability.strong_law_ae_infinitePi` — for `f` measurable and integrable against `Q`,
  the averages `n⁻¹ • ∑_{i < n} f (xᵢ)` converge `Q^{⊗ℕ}`-almost everywhere to `∫ f dQ`.

## Implementation

Independence of the coordinates is Mathlib's `ProbabilityTheory.iIndepFun_infinitePi` for the
identity variables. Nothing is reproved about product measures.

The strong law itself is then Mathlib's, applied to `x ↦ f (x i)`: the three hypotheses come from
that independence and from `measurePreserving_eval_infinitePi`, which makes the coordinates
identically distributed, transports integrability, and identifies the limit `𝔼[f ∘ eval 0]` with
`∫ f dQ`.

`f` is assumed measurable, not merely almost-everywhere strongly measurable as `Integrable f Q`
gives: it has to be composed with the coordinate maps, so that independence and identical
distribution of the coordinates transfer to the summands.

This is general probability theory with no exchangeability in its statements. It is used by the
conditional strong law for conditionally i.i.d. processes in
`TauCeti.Probability.Exchangeability.ConditionallyIID.StrongLaw`, where the conditional statement is
reduced fibrewise to this one over the mixing law; see
`TauCetiRoadmap/Exchangeability/README.md`, Layer 6 (the empirical-measure form of the
directing-measure theorem).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **The strong law of large numbers on the canonical i.i.d. model.** For an `f` that is measurable
and integrable against `Q`, the averages of `f` along the coordinates of `Q^{⊗ℕ}` converge almost
everywhere to `∫ f dQ`.

This is Mathlib's `ProbabilityTheory.strong_law_ae` for the coordinate process of a countable
power; it is the form in which a statement about *some* i.i.d. sequence becomes a statement about
the product measure itself, and so can be integrated over a mixing law. -/
theorem strong_law_ae_infinitePi (Q : Measure α) [IsProbabilityMeasure Q] {f : α → E}
    (hf : Measurable f) (hint : Integrable f Q) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => Q),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ y, f y ∂Q)) := by
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => Q with hP
  -- Every coordinate is measure preserving onto `Q`; integrability, identical distribution and the
  -- value of the limit all come from that one fact.
  have heval : ∀ i : ℕ, MeasurePreserving (fun x : ℕ → α => x i) P Q := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i
  have hint' : ∀ i : ℕ, Integrable (fun x : ℕ → α => f (x i)) P := fun i =>
    ((heval i).integrable_comp hint.1).2 hint
  have hident : ∀ i : ℕ,
      IdentDistrib (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x 0)) P P := fun i =>
    IdentDistrib.comp ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [(heval i).map_eq, (heval 0).map_eq]⟩ hf
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x j)) P :=
    fun _ _ hij =>
      ((iIndepFun_infinitePi (P := fun _ : ℕ => Q) (X := fun _ x => x)
        fun _ => measurable_id).comp (fun _ => f) fun _ => hf).indepFun hij
  have hlimit : ∫ x, f (x 0) ∂P = ∫ y, f y ∂Q := by
    rw [← (heval 0).map_eq, integral_map (measurable_pi_apply 0).aemeasurable
      (by rw [(heval 0).map_eq]; exact hint.1)]
  simpa only [hlimit] using
    strong_law_ae (fun i (x : ℕ → α) => f (x i)) (hint' 0) hindep hident

end Probability

end TauCeti
