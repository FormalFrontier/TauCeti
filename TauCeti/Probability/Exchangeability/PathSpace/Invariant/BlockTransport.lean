/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Tail
public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import TauCeti.Probability.Exchangeability.PermutationExtension
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Moving a block through a reindexing, over an invariant event

Over a shift-invariant event, a reindexing that is eventually a translation changes no
set-integral, and a strictly increasing finite selection may therefore be displaced onto the
prefix `0, 1, …, m - 1`.

## Main results

* `setLIntegral_comp_reindex_eq_of_measurableSet_invariants` — the general form, for any
  reindexing that preserves the law and is eventually a translation;
* `ContractableLaw.setLIntegral_comp_reindex_eq_of_measurableSet_invariants` — its contractable
  instance, where strict monotonicity supplies the measure preservation;
* `ContractableLaw.setLIntegral_block_eq_prefix_of_measurableSet_invariants` — the finite-selection
  form: a strictly increasing block becomes the prefix.

Nothing here is specific to a de Finetti route. The statements mention a contractable path law, a
shift-invariant event and a finite selection, and no Koopman operator; the Koopman route is the
motivating consumer and imports this.

## Invariance, not tail-measurability

⚠ These results rest on *invariance*: `shift ⁻¹' A = A`, in the
`MeasurableSpace.invariants`-measurable form. A tail event need not satisfy it, and
`invariants_shift_lt_pathTail` shows the inclusion is strict. This is the substantive difference
from the `L²` route, whose block comparison is distributional — an equality of conditional laws
given the tail — rather than an actual invariance of the test event.

The general statement asks only that the reindexing preserve the law. Contractability and strict
monotonicity are one way to obtain that, not requirements: a merely shift-invariant law with
`φ = (· + C)` qualifies.

## Source

The block-reindexing strategy follows the earlier `cameronfreer/exchangeability` development,
which carries related block-reindexing and factorization material. These lemmas are not
line-by-line ports: they are assembled from Tau Ceti's eventual-translation extension
(`exists_strictMono_nat_extending_fin_eventually_add`), the invariant-event preimage identity
(`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`), and contractable reindexing
(`ContractableLaw.measurePreserving_reindex`). The transport theorem itself is Tau Ceti-native.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

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

end Probability

end TauCeti

end
