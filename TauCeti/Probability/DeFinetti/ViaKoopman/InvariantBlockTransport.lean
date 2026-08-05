/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import TauCeti.Probability.Exchangeability.PathSpace.InvariantTail
public import TauCeti.Probability.Exchangeability.PermutationExtension
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import TauCeti.Probability.Exchangeability.L2.LongTailAverages
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Moving a block through a reindexing, over an invariant event

The Koopman block argument needs to compare the integral of a block observable over a
shift-invariant event with the integral of a *displaced* block over the same event. Two independent
facts combine to allow that, and keeping them apart is the point:

* a strictly increasing reindexing preserves a contractable path law
  (`ContractableLaw.measurePreserving_reindex`) — this needs monotonicity;
* an eventually-translating reindexing fixes every shift-invariant event
  (`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`) — this needs no
  monotonicity, only exact shift invariance.

`exists_strictMono_nat_extending_fin_eventually_add` supplies a single reindexing with **both**
properties extending any strictly increasing finite selection, which is what makes the comparison
available for an arbitrary block.

⚠ This is specific to *invariant* events. A tail event need not satisfy `shift ⁻¹' A = A`, and
`invariants_shift_lt_pathTail` shows the inclusion is strict, so the tail-conditioned analogue
needs a different argument and is not obtained by weakening the hypothesis here.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **A strictly increasing finite selection can be displaced over an invariant event.** For a
contractable path law and a set `A` measurable in `MeasurableSpace.invariants (shift α)`, the
set-integral of a block observable over `A` is unchanged when the block is read through any
strictly increasing extension of the selection that is eventually a translation. -/
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

omit [MeasurableSpace α] in
/-- **The Birkhoff average of a coordinate observable is a prefix average of the process.** For the
one-sided shift, `birkhoffAverage ℝ (shift α) (fun x => f (x 0)) n` is exactly
`prefixAverage (fun i x => f (x i)) n`.

This is the bridge from the generic mean-ergodic theorem — which speaks of Birkhoff averages of a
single observable under a measure-preserving map — to the block-average API, which speaks of
averages of a process over a selection of coordinates. Neither side needs to know about the other:
they are the same function. -/
theorem birkhoffAverage_coord_eq_prefixAverage (f : α → ℝ) (n : ℕ) :
    birkhoffAverage ℝ (shift α) (fun x => f (x 0)) n
      = prefixAverage (fun i (x : ℕ → α) => f (x i)) n := by
  funext x
  rw [birkhoffAverage, birkhoffSum, prefixAverage_apply, smul_eq_mul]
  congr 1
  rw [← Finset.sum_range fun i => f (x i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shift_iterate_apply]
  simp

end Probability

end TauCeti
