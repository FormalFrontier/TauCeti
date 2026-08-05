/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import TauCeti.Probability.Exchangeability.PathSpace.InvariantTail
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Transporting an integral through a reindexing, over an invariant event

For a contractable path law, a reindexing that is *both* strictly increasing and eventually a
translation acts trivially on integrals taken over a shift-invariant event. Two independent facts
combine to give this, and keeping them apart is the point:

* a strictly increasing reindexing preserves a contractable path law
  (`ContractableLaw.measurePreserving_reindex`) — this needs monotonicity;
* an eventually-translating reindexing fixes every shift-invariant event
  (`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`) — this needs no
  monotonicity, only exact shift invariance.

⚠ This is specific to *invariant* events. A tail event need not satisfy `shift ⁻¹' A = A`, and
`invariants_shift_lt_pathTail` shows the inclusion is strict, so the tail-conditioned analogue
needs a different argument and is not obtained by weakening the hypothesis here.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **An eventually-translating strict reindexing acts trivially over an invariant event.** For a
contractable path law `ρ`, a set `A` measurable in `MeasurableSpace.invariants (shift α)`, and a
strictly increasing `φ` with `φ n = n + C` for all `n ≥ m`, reading a measurable path functional `f`
through `φ` does not change its set-integral over `A`. -/
theorem ContractableLaw.setLIntegral_comp_reindex_eq_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {φ : ℕ → ℕ} {m C : ℕ}
    (hφ_mono : StrictMono φ) (hφ_add : ∀ n, m ≤ n → φ n = n + C)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {f : (ℕ → α) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in A, f (fun k => x (φ k)) ∂ρ = ∫⁻ x in A, f x ∂ρ := by
  have hmp : MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ :=
    hρ.measurePreserving_reindex hφ_mono
  have hpre : (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A = A :=
    preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add hA hφ_add
  have hAmeas : MeasurableSet A := (MeasurableSpace.measurableSet_invariants.1 hA).1
  calc ∫⁻ x in A, f (fun k => x (φ k)) ∂ρ
      = ∫⁻ x in (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A, f (fun k => x (φ k)) ∂ρ := by
        rw [hpre]
    _ = ∫⁻ x in A, f x ∂ρ := by
        rw [← hmp.setLIntegral_comp_preimage hAmeas hf]

end Probability

end TauCeti

end

end
