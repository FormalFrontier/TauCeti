/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Transport
import TauCeti.Probability.Exchangeability.PermutationExtension
public import TauCeti.Probability.Exchangeability.L2.LongTailAverages
public import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# Moving a finite block through a reindexing, over an invariant event

The Koopman block argument needs two things: to compare the integral of a block observable over a
shift-invariant event with the integral of the *prefix* block over the same event, and to read
Mathlib's mean ergodic theorem — stated for Birkhoff averages — in terms of prefix averages of the
process.

## Main results

* `ContractableLaw.setLIntegral_block_eq_prefix_of_measurableSet_invariants` — over an invariant
  event, a strictly increasing finite selection may be replaced by the prefix `0, 1, …, m - 1`.
* `birkhoffAverage_shift_eq_prefixAverage` — the Birkhoff average of a coordinate observable *is*
  the prefix average of the process.

The block comparison is the finite-selection form of
`ContractableLaw.setLIntegral_comp_reindex_eq_of_measurableSet_invariants`, which transports an
arbitrary path functional through a reindexing that is strictly increasing and eventually a
translation. `exists_strictMono_nat_extending_fin_eventually_add` supplies such a reindexing
extending any strictly increasing finite selection, which is what turns the global statement into
one about an arbitrary block.

## Source

The Koopman block-factorization strategy follows the earlier `cameronfreer/exchangeability`
development, which carries related block-reindexing and factorization material. The transport
lemmas here are not line-by-line ports: they are assembled from Tau Ceti's eventual-translation
extension (`exists_strictMono_nat_extending_fin_eventually_add`), invariant-event preimage
(`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`), contractable reindexing
(`ContractableLaw.measurePreserving_reindex`), and Birkhoff-average APIs. The generic transport
theorem they rest on, in `PathSpace/Invariant/Transport.lean`, is Tau Ceti-native.

⚠ The block-transport results rest on *invariance*, not tail-measurability: a tail event need not
satisfy `shift ⁻¹' A = A`, and `invariants_shift_lt_pathTail` shows the inclusion is strict. The
Birkhoff/prefix-average identity carries no such caveat — it mentions no event at all and is an
unconditional identity of functions.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **A strictly increasing finite selection can be displaced to the prefix over an invariant
event.** For a contractable path law and a set `A` measurable in
`MeasurableSpace.invariants (shift α)`, the set-integral over `A` of a block observable read along
a strictly increasing selection `k` equals the set-integral of the same observable read along the
prefix `0, 1, …, m - 1`. -/
theorem ContractableLaw.setLIntegral_block_eq_prefix_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {g : (Fin m → α) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in A, g (fun i => x (k i)) ∂ρ = ∫⁻ x in A, g (prefixProj α m x) ∂ρ := by
  obtain ⟨φ, C, hφ_mono, hφ_eq, hφ_add⟩ := exists_strictMono_nat_extending_fin_eventually_add hk
  have hf : Measurable fun x : ℕ → α => g (prefixProj α m x) :=
    hg.comp (measurable_prefixProj m)
  have hcomp : ∀ x : ℕ → α,
      prefixProj α m (fun j => x (φ j)) = fun i : Fin m => x (k i) := by
    intro x; funext i; simp only [prefixProj_apply, hφ_eq]
  simpa only [hcomp] using
    hρ.setLIntegral_comp_reindex_eq_of_measurableSet_invariants hφ_mono hφ_add hA hf

omit [MeasurableSpace α] in
/-- **The Birkhoff average of a coordinate observable is a prefix average of the process.** For the
one-sided shift, `birkhoffAverage ℝ (shift α) (fun x => f (x 0)) n` is exactly
`prefixAverage (fun i x => f (x i)) n`.

This is the bridge from the generic mean-ergodic theorem — which speaks of Birkhoff averages of a
single observable under a measure-preserving map — to the block-average API, which speaks of
averages of a process over a selection of coordinates. Neither side needs to know about the other:
they are the same function. -/
@[simp]
theorem birkhoffAverage_shift_eq_prefixAverage (f : α → ℝ) (n : ℕ) :
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

end

end
