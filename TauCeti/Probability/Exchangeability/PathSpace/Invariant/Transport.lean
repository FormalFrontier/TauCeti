/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import TauCeti.Probability.Exchangeability.PathSpace.Shift.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

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

## Main results

* `preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add` — the invariant-measurable
  form of reindexing stability;
* `setLIntegral_comp_reindex_eq_of_measurableSet_invariants` — the transport itself, stated for a
  measure-preserving reindexing;
* `ContractableLaw.setLIntegral_comp_reindex_eq_of_measurableSet_invariants` — its contractable
  instance.

## Source

Both statements are Tau Ceti-native. The genuinely external inputs are
`ContractableLaw.measurePreserving_reindex` and
`preimage_reindex_eq_of_preimage_shift_eq_of_eventually_add`, together with Mathlib's
`MeasurePreserving.setLIntegral_comp_preimage`. Nothing here mentions a block, a selection or a
Koopman operator; the Koopman-facing consumer credits the strategy it serves, in
`DeFinetti/ViaKoopman/Invariant/BlockTransport.lean`.

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

/-- **Invariant events are fixed by an eventually-translating reindexing**, in the
`MeasurableSpace.invariants`-measurable form.

Deliberately **not** `@[simp]`: `m` and `C` occur only in the hypothesis `hφ`, never in the
left-hand side, so `simp` cannot infer them and the rule would never fire. -/
theorem preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add {m C : ℕ} {φ : ℕ → ℕ}
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    (hφ : ∀ n, m ≤ n → φ n = n + C) :
    (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A = A :=
  preimage_reindex_eq_of_preimage_shift_eq_of_eventually_add
    (MeasurableSpace.measurableSet_invariants.1 hA).2 hφ

/-- **An eventually-translating measure-preserving reindexing acts trivially over an invariant
event.** If reading a path through `φ` preserves `ρ`, and `φ n = n + C` for all `n ≥ m`, then the
set-integral of a measurable path functional over a shift-invariant `A` is unchanged.

Only measure preservation by *this* reindexing is used; contractability and strict monotonicity are
one way to obtain it, not requirements. In particular a merely shift-invariant law with
`φ = (· + C)` qualifies. -/
theorem setLIntegral_comp_reindex_eq_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} {φ : ℕ → ℕ} {m C : ℕ}
    (hmp : MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ)
    (hφ_add : ∀ n, m ≤ n → φ n = n + C)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {f : (ℕ → α) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in A, f (fun k => x (φ k)) ∂ρ = ∫⁻ x in A, f x ∂ρ := by
  have hpre : (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A = A :=
    preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add hA hφ_add
  have hAmeas : MeasurableSet A := (MeasurableSpace.measurableSet_invariants.1 hA).1
  calc ∫⁻ x in A, f (fun k => x (φ k)) ∂ρ
      = ∫⁻ x in (fun x : ℕ → α => fun k => x (φ k)) ⁻¹' A, f (fun k => x (φ k)) ∂ρ := by
        rw [hpre]
    _ = ∫⁻ x in A, f x ∂ρ := by
        rw [← hmp.setLIntegral_comp_preimage hAmeas hf]

/-- **The contractable instance.** A strictly increasing reindexing preserves a contractable path
law, which is the hypothesis the general statement wants. -/
theorem ContractableLaw.setLIntegral_comp_reindex_eq_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {φ : ℕ → ℕ} {m C : ℕ}
    (hφ_mono : StrictMono φ) (hφ_add : ∀ n, m ≤ n → φ n = n + C)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {f : (ℕ → α) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in A, f (fun k => x (φ k)) ∂ρ = ∫⁻ x in A, f x ∂ρ :=
  _root_.TauCeti.Probability.setLIntegral_comp_reindex_eq_of_measurableSet_invariants
    (hρ.measurePreserving_reindex hφ_mono) hφ_add hA hf

end Probability

end TauCeti

end

end
