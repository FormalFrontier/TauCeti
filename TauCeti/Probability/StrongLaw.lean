/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.StrongLaw
-- Public: the statements are about `Measure.infinitePi` and independence of its coordinates.
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The strong law of large numbers on a countable product space

Mathlib's `ProbabilityTheory.strong_law_ae` takes a sequence of pairwise independent, identically
distributed, integrable random variables on an abstract probability space. The canonical carrier of
such a sequence is the countable power `Measure.infinitePi fun _ : ℕ => Q` with its coordinate maps,
and this file specializes the strong law to it.

## Main results

* `TauCeti.Probability.iIndepFun_eval_infinitePi` — the coordinates of an infinite product measure
  are independent;
* `TauCeti.Probability.strong_law_ae_infinitePi` — for `f` integrable against `Q`, the averages
  `n⁻¹ • ∑_{i < n} f (xᵢ)` converge `Q^{⊗ℕ}`-almost everywhere to `∫ f dQ`.

## Implementation

Independence of the coordinates is read off Mathlib's characterization
`iIndepFun_iff_map_fun_eq_infinitePi_map`: the joint law of the coordinate family is the identity
pushforward of the product measure, and its marginals are the factors by
`Measure.infinitePi_map_eval`. Nothing is reproved about product measures.

The strong law itself is then Mathlib's, applied to `x ↦ f (x i)`: the three hypotheses come from
that independence, from `Measure.infinitePi_map_eval` again (which makes the coordinates
identically distributed and transports integrability), and from `integral_map` (which identifies
the limit `𝔼[f ∘ eval 0]` with `∫ f dQ`).

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

/-- **The coordinates of an infinite product measure are independent.** -/
theorem iIndepFun_eval_infinitePi {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (Q : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (Q i)] :
    iIndepFun (fun (i : ι) (x : ∀ j, β j) => x i) (Measure.infinitePi Q) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun i => measurable_pi_apply i]
  simp_rw [Measure.infinitePi_map_eval]
  exact Measure.map_id

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- **The strong law of large numbers on the canonical i.i.d. model.** For an integrable `f`, the
averages of `f` along the coordinates of `Q^{⊗ℕ}` converge almost everywhere to `∫ f dQ`.

This is Mathlib's `ProbabilityTheory.strong_law_ae` for the coordinate process of a countable
power; it is the form in which a statement about *some* i.i.d. sequence becomes a statement about
the product measure itself, and so can be integrated over a mixing law. -/
theorem strong_law_ae_infinitePi (Q : Measure α) [IsProbabilityMeasure Q] {f : α → E}
    (hf : Measurable f) (hint : Integrable f Q) :
    ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => Q),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (x i)) atTop
        (𝓝 (∫ y, f y ∂Q)) := by
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ : ℕ => Q with hP
  have hcoord : ∀ i : ℕ, Measurable fun x : ℕ → α => x i := fun i => measurable_pi_apply i
  have hmap : ∀ i : ℕ, P.map (fun x : ℕ → α => x i) = Q := fun i =>
    Measure.infinitePi_map_eval (fun _ : ℕ => Q) i
  -- Composing with `f` keeps the coordinates integrable and identically distributed.
  have hmapf : ∀ i : ℕ, P.map (fun x : ℕ → α => f (x i)) = Q.map f := fun i => by
    rw [show (fun x : ℕ → α => f (x i)) = f ∘ fun x : ℕ → α => x i from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (by rw [hmap i]; exact hint.1.aemeasurable)
        (hcoord i).aemeasurable, hmap i]
  have hint' : ∀ i : ℕ, Integrable (fun x : ℕ → α => f (x i)) P := fun i =>
    ((measurePreserving_eval_infinitePi (fun _ : ℕ => Q) i).integrable_comp hint.1).2 hint
  have hident : ∀ i : ℕ,
      IdentDistrib (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x 0)) P P := fun i =>
    ⟨(hint' i).1.aemeasurable, (hint' 0).1.aemeasurable, by rw [hmapf i, hmapf 0]⟩
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun x : ℕ → α => f (x i)) (fun x : ℕ → α => f (x j)) P :=
    fun _ _ hij =>
      ((iIndepFun_eval_infinitePi fun _ : ℕ => Q).comp (fun _ => f) fun _ => hf).indepFun hij
  have hlimit : ∫ x, f (x 0) ∂P = ∫ y, f y ∂Q := by
    rw [← hmap 0, integral_map (hcoord 0).aemeasurable (by rw [hmap 0]; exact hint.1)]
  simpa only [hlimit] using
    strong_law_ae (fun i (x : ℕ → α) => f (x i)) (hint' 0) hindep hident

end Probability

end TauCeti
