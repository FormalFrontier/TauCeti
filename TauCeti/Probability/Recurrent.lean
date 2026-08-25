/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import TauCeti.Probability.Exchangeability.PathSpace.Shift
-- Non-public: Poincaré recurrence for a conservative map is used only inside proofs.
import Mathlib.Dynamics.Ergodic.Conservative

/-!
# Recurrent processes

A process `X : ℕ → Ω → α` is **recurrent** when, almost surely, every state it ever visits it
visits infinitely often:

```text
∀ᵐ ω ∂μ, ∀ k, ∃ᶠ n in atTop, X n ω = X k ω
```

The main theorem is that recurrence is automatic for a stationary process on a countable state
space (`recurrent_of_measurePreserving_shift`): it is Poincaré recurrence for the one-sided
shift, applied to the countably many coordinate events `{x | x 0 = a}` at once. The
exchangeability-specific corollaries of that theorem live in
`TauCeti.Probability.Exchangeability.Recurrence.Basic`.

## Main results

* `TauCeti.Probability.recurrent_def` — the defining equation of `Recurrent`, which is not
  `@[expose]`, so this is the unfolding interface downstream.
* `TauCeti.Probability.recurrent_iff_ae_forall_state` — the state-indexed reading of recurrence.
* `TauCeti.Probability.recurrent_of_measurePreserving_shift` — a process with a shift-invariant
  path law on a countable state space is recurrent.
* `TauCeti.Probability.recurrent_pathLaw_iff` — the process-level and path-law readings agree.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

Mathlib's `MeasureTheory.Conservative` is recurrence of a map — the Poincaré recurrence theorem
— and is consumed here rather than reproved; recurrence of a process in the above sense is not in
Mathlib. No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable
rather than Markov exchangeable sequences.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

section Defs

variable {Ω α : Type*} [MeasurableSpace Ω]

/-- A process is **recurrent** when, almost surely, every state it visits it visits infinitely
often. This is Diaconis and Freedman's standing hypothesis on a Markov exchangeable process.

The body is not exposed; `recurrent_def` is the unfolding interface. -/
def Recurrent (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ᶠ n in atTop, X n ω = X k ω

variable {μ : Measure Ω} {X Y : ℕ → Ω → α}

/-- **The defining equation of recurrence.** `Recurrent` is not `@[expose]`, so this is how
downstream modules unfold it. -/
theorem recurrent_def :
    Recurrent μ X ↔ ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ᶠ n in atTop, X n ω = X k ω :=
  Iff.rfl

/-- **The state-indexed reading of recurrence.** Almost surely, every state the process attains
it attains infinitely often. -/
theorem recurrent_iff_ae_forall_state :
    Recurrent μ X ↔
      ∀ᵐ ω ∂μ, ∀ a : α, (∃ k, X k ω = a) → ∃ᶠ n in atTop, X n ω = a := by
  constructor
  · intro h
    filter_upwards [h] with ω hω a ha
    obtain ⟨k, hk⟩ := ha
    exact hk ▸ hω k
  · intro h
    filter_upwards [h] with ω hω k
    exact hω (X k ω) ⟨k, rfl⟩

/-- The set of times at which a recurrent process revisits any given one of its states is
infinite. -/
theorem Recurrent.ae_infinite_setOf_eq (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, {n | X n ω = X k ω}.Infinite := by
  filter_upwards [h] with ω hω k
  exact Nat.frequently_atTop_iff_infinite.mp (hω k)

/-- Every state of a recurrent process recurs after every time. -/
theorem Recurrent.ae_exists_ge (h : Recurrent μ X) :
    ∀ᵐ ω ∂μ, ∀ k N : ℕ, ∃ n, N ≤ n ∧ X n ω = X k ω := by
  filter_upwards [h] with ω hω k N
  obtain ⟨n, hn, hxn⟩ := (frequently_atTop.mp (hω k)) N
  exact ⟨n, hn, hxn⟩

/-- Recurrence only depends on the process up to almost-everywhere equality of its
coordinates. -/
theorem Recurrent.congr (h : Recurrent μ X) (hXY : ∀ n, X n =ᵐ[μ] Y n) : Recurrent μ Y := by
  have hall : ∀ᵐ ω ∂μ, ∀ n, X n ω = Y n ω := ae_all_iff.2 hXY
  filter_upwards [h, hall] with ω hω heq k
  refine (hω k).mono fun n hn => ?_
  rw [← heq n, ← heq k]
  exact hn

/-- Recurrence is inherited by every coordinatewise pushforward: a repeated state stays
repeated. -/
theorem Recurrent.map_values {β : Type*} (h : Recurrent μ X) (f : α → β) :
    Recurrent μ fun n ω => f (X n ω) := by
  filter_upwards [h] with ω hω k
  exact (hω k).mono fun n hn => by rw [hn]

end Defs

section Stationary

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Poincaré recurrence on path space.** A shift-invariant law on the paths of a countable
state space gives full mass to the paths that revisit each of their states infinitely often.

The one-sided shift is measure preserving, hence conservative, so almost every path whose orbit
meets the coordinate event `{x | x 0 = a}` meets it infinitely often; countability of the state
space lets a single null set serve all `a` at once. -/
theorem ae_forall_frequently_apply_eq_of_measurePreserving_shift
    [Countable α] [MeasurableSingletonClass α] {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (h : MeasurePreserving (shift α) ρ ρ) :
    ∀ᵐ x ∂ρ, ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k := by
  have hcons : Conservative (shift α) ρ := h.conservative
  have key : ∀ a : α, ∀ᵐ x ∂ρ, ∀ k : ℕ, x k = a → ∃ᶠ n in atTop, x n = a := by
    intro a
    have hpre : {x : ℕ → α | x 0 = a} = (fun x : ℕ → α => x 0) ⁻¹' {a} := by
      ext x
      simp
    have hs : MeasurableSet {x : ℕ → α | x 0 = a} :=
      hpre ▸ (measurable_pi_apply 0) (measurableSet_singleton a)
    filter_upwards [hcons.ae_forall_image_mem_imp_frequently_image_mem hs.nullMeasurableSet]
      with x hx k hk
    -- The orbit of `x` meets `{y | y 0 = a}` at time `n` exactly when `x n = a`.
    have hmem : ∀ n : ℕ, (shift α)^[n] x ∈ {y : ℕ → α | y 0 = a} ↔ x n = a := fun n => by
      simp only [Set.mem_ofPred_eq, shift_iterate_apply, zero_add]
    exact (hx k ((hmem k).2 hk)).mono fun n hn => (hmem n).1 hn
  filter_upwards [ae_all_iff.2 key] with x hx k
  exact hx (x k) k rfl

/-- **A stationary process on a countable state space is recurrent.** -/
theorem recurrent_of_measurePreserving_shift [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X)) :
    Recurrent μ X := by
  have hfin : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  have hmap : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ hX
  have hpath := ae_forall_frequently_apply_eq_of_measurePreserving_shift h
  rw [pathLaw_def] at hpath
  exact ae_of_ae_map hmap hpath

end Stationary

section PathLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The recurrent paths form a measurable set: they are cut out by countably many coordinate
coincidences, each measurable by Mathlib's `measurableSet_eq_fun`. -/
theorem measurableSet_setOf_forall_frequently_apply_eq [MeasurableEq α] :
    MeasurableSet {x : ℕ → α | ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k} := by
  have hcover : {x : ℕ → α | ∀ k : ℕ, ∃ᶠ n in atTop, x n = x k} =
      ⋂ k : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ _ : N ≤ n, {x : ℕ → α | x n = x k} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, frequently_atTop, exists_prop]
  rw [hcover]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      measurableSet_eq_fun (measurable_pi_apply n) (measurable_pi_apply k)

/-- **The process-level and path-law formulations of recurrence agree.** -/
theorem recurrent_pathLaw_iff [MeasurableEq α] {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    Recurrent (pathLaw μ X) (fun n (x : ℕ → α) => x n) ↔ Recurrent μ X := by
  have hmap : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ hX
  rw [recurrent_def, recurrent_def, pathLaw_def,
    ae_map_iff hmap measurableSet_setOf_forall_frequently_apply_eq]

end PathLaw

end Probability

end TauCeti

end

end
