/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.Tail
public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Moving a block through a reindexing, over an invariant event

Over a shift-invariant event, a **law-preserving** reindexing that is eventually a translation
changes no set-integral; so for a **contractable** law, where strict monotonicity supplies that
preservation, a strictly increasing finite selection may be displaced onto the prefix
`0, 1, …, m - 1`.

Measure preservation cannot be dropped: without it the first claim fails outright — take `ρ` a
point mass at an alternating path, `A = univ` and `φ = (· + 1)`. Eventual translation is a
*sufficient* condition for the reindexing to fix every invariant event, not a necessary one for the
integral identity, which needs only `T ⁻¹' A = A`.

## Main results

* `measurePreserving_restrict_reindex_of_measurableSet_invariants_of_eventually_add` — the
  primitive: such a reindexing preserves the restricted law, so Koopman-side consumers get a
  `MeasurePreserving`, not only an integral identity;
* `ContractableLaw.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants` — the
  finite-selection form as a measure equality on the **restricted** law: reading a strictly
  increasing block and reading the prefix push `ρ.restrict A` to the same measure, so Bochner and
  `Lᵖ` statements follow as well. The unrestricted counterpart is the existing
  `ContractableLaw.map_prefixProj_of_strictMono`.

* `ContractableLaw.setIntegral_mul_block_eq_prefix_of_strictMono_of_measurableSet_invariants` —
  the same displacement against an **invariant weight**. A measure equality cannot carry a weight,
  but an invariants-measurable one is unchanged by the reindexing
  (`comp_reindex_eq_of_measurable_invariants_of_eventually_add`), so it rides through the change of
  variables. This is the form an induction peeling one coordinate at a time needs, since the
  factors already peeled accumulate as exactly such a weight.

`ℝ≥0∞` statements are not restated here: a consumer wanting one applies `.lintegral_comp` to the
`MeasurePreserving` above, or rewrites with `lintegral_map` through the measure equality.

The endomorphism-level facts are Mathlib's: `MeasurePreserving.restrict_preimage` gives the
restricted measure preservation once the invariant event is rewritten by
`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`, and
`MeasurePreserving.lintegral_comp` gives the integral identity. This module supplies only the
reindexing-and-invariant-event instance, and restates no Mathlib API.

Nothing here is specific to a de Finetti route. The statements mention a contractable path law, a
shift-invariant event and a finite selection, and no Koopman operator; the Koopman route is the
motivating consumer and will import this; nothing imports it yet.

## Invariance, not tail-measurability

⚠ These results rest on *invariance*: `shift ⁻¹' A = A`, in the
`MeasurableSpace.invariants`-measurable form. A tail event need not satisfy it, and
`invariants_shift_lt_pathTail` shows the inclusion is strict already over `Bool`. This is the
substantive difference from the `L²` route, whose block comparison is distributional — an equality
of conditional laws given the tail — rather than an actual invariance of the test event.

The general statement asks only that the reindexing preserve the law. Contractability and strict
monotonicity are one way to obtain that, not requirements: a merely shift-invariant law with
`φ = (· + C)` qualifies.

## Source

No material is adapted from `cameronfreer/exchangeability`. That development carries its own
block-reindexing and factorization material for the Koopman argument; the statements here were
assembled from Tau Ceti's own pieces — the eventual-translation extension
`exists_strictMono_nat_extending_fin_eventually_add`, the invariant-event preimage identity
`preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add`, contractable reindexing
`ContractableLaw.measurePreserving_reindex`, and Mathlib's `MeasurePreserving.restrict_preimage`.

-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- **Such a reindexing preserves the restricted law.** The primitive form: consumers needing the
Koopman operator on `Lp (ρ.restrict A)`, or a Bochner integral, get a `MeasurePreserving` rather
than only an `ℝ≥0∞` identity.

Only measure preservation by *this* reindexing is used; contractability and strict monotonicity are
one way to obtain it, not requirements. In particular a merely shift-invariant law with
`φ = (· + C)` qualifies. -/
theorem measurePreserving_restrict_reindex_of_measurableSet_invariants_of_eventually_add
    {ρ : Measure (ℕ → α)} {φ : ℕ → ℕ} {m C : ℕ}
    (hmp : MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ)
    (hφ_add : ∀ n, m ≤ n → φ n = n + C)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (ρ.restrict A) (ρ.restrict A) := by
  have h := hmp.restrict_preimage (MeasurableSpace.measurableSet_invariants.1 hA).1
  rwa [preimage_reindex_eq_of_measurableSet_invariants_of_eventually_add hA hφ_add] at h

/-- **The primitive measure equality.** Over an invariant event, reading a strictly increasing
block and reading the prefix push the restricted law to the same measure on `Fin m → α`.

This is the form that gives Bochner integrals and `Lᵖ` statements as well; an `ℝ≥0∞` identity
follows by rewriting with `lintegral_map`, and is not restated here. -/
theorem ContractableLaw.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    (ρ.restrict A).map (fun x : ℕ → α => fun i : Fin m => x (k i))
      = (ρ.restrict A).map (prefixProj α m) := by
  obtain ⟨φ, C, hφ_mono, hφ_eq, hφ_add⟩ := exists_strictMono_nat_extending_fin_eventually_add hk
  have hmp := measurePreserving_restrict_reindex_of_measurableSet_invariants_of_eventually_add
    (hρ.measurePreserving_reindex hφ_mono) hφ_add hA
  have hcomp : (fun x : ℕ → α => fun i : Fin m => x (k i))
      = prefixProj α m ∘ fun x : ℕ → α => fun j => x (φ j) := by
    funext x i
    simp only [Function.comp_apply, prefixProj_apply, hφ_eq]
  rw [hcomp, ← Measure.map_map (measurable_prefixProj m) hmp.measurable, hmp.map_eq]

/-- **A block may be displaced onto the prefix even against an invariant weight.** The
unweighted statement is a measure equality, which a weight would break; but an invariants-measurable
weight is itself unchanged by the reindexing
(`comp_reindex_eq_of_measurable_invariants_of_eventually_add`), so it may be carried through the
measure-preserving change of variables along with the block observable.

This is what an induction peeling one coordinate at a time needs: the factors already peeled
accumulate as exactly such a weight. -/
theorem ContractableLaw.setIntegral_mul_block_eq_prefix_of_strictMono_of_measurableSet_invariants
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {w : (ℕ → α) → ℝ} (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    {f : (Fin m → α) → ℝ} (hf : Measurable f) :
    ∫ x in A, w x * f (fun i => x (k i)) ∂ρ = ∫ x in A, w x * f (prefixProj α m x) ∂ρ := by
  obtain ⟨φ, C, hφ_mono, hφ_eq, hφ_add⟩ := exists_strictMono_nat_extending_fin_eventually_add hk
  have hmp := measurePreserving_restrict_reindex_of_measurableSet_invariants_of_eventually_add
    (hρ.measurePreserving_reindex hφ_mono) hφ_add hA
  have hw' : Measurable w := hw.mono (MeasurableSpace.invariants_le _) le_rfl
  have hgm : Measurable fun x : ℕ → α => w x * f (prefixProj α m x) :=
    hw'.mul (hf.comp (measurable_prefixProj m))
  -- The weight is invariant under the reindexing, and the reindexed prefix is the block.
  have hpt : ∀ x : ℕ → α,
      w (fun j => x (φ j)) * f (prefixProj α m fun j => x (φ j)) = w x * f (fun i => x (k i)) := by
    intro x
    have harg : (prefixProj α m fun j => x (φ j)) = fun i => x (k i) := by
      funext i
      simp only [prefixProj_apply, hφ_eq]
    rw [comp_reindex_eq_of_measurable_invariants_of_eventually_add hw hφ_add, harg]
  -- Change variables along the reindexing, which preserves the restricted law.
  have key : ∫ x, w x * f (prefixProj α m x) ∂ρ.restrict A
      = ∫ x, w (fun j => x (φ j)) * f (prefixProj α m fun j => x (φ j)) ∂ρ.restrict A := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hgm.aestronglyMeasurable
  rw [key]
  exact (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm

end Probability

end TauCeti

end
