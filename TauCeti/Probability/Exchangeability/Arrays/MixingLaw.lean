/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Basic
import TauCeti.Probability.Exchangeability.MixedIID.Map
import TauCeti.Probability.Exchangeability.MixedIID.Mixture

/-!
# Mixing laws of separately exchangeable arrays

Applying de Finetti's theorem to the rows of a separately exchangeable array gives a random
probability measure on row paths. The remaining column symmetry does not generally make this
random measure exchangeable almost surely. For example, if every row equals one common i.i.d.
random path `Y`, then the row directing measure is `δ_Y`, which is almost surely not an
exchangeable measure.

The correct inherited symmetry is at the level of the **mixing law**. If `ν` is any mixing
representative for the row process, then the law of `ν` is invariant under pushing every measure
forward by a permutation of path coordinates:

```text
μ.map (ω ↦ (ν ω).map (permReindex τ)) = μ.map ν.
```

The proof uses the opposite-axis half of separate exchangeability. Mapping each row path by
`permReindex τ`
preserves the row process's finite-dimensional laws by column exchangeability. The
coordinatewise-map API for `MixedIIDWith` therefore supplies a second mixing representative for
the original row process, and uniqueness of the mixing law identifies their laws. The column
statement is the symmetric argument using row exchangeability.

The existential corollaries retain genuine directing measures: de Finetti supplies
`ConditionallyIIDWith`, while the invariance follows after forgetting only to its mixture
identity. These results are the next law-level input to the separately exchangeable-array branch
of the Aldous–Hoover milestone in `TauCetiRoadmap/Exchangeability/README.md`, Layer 8.

## Main results

* `SeparatelyExchangeable.mixingLaw_map_permReindex_arrayRow_eq` — the row mixing law is invariant
  under coordinate permutations;
* `SeparatelyExchangeable.mixingLaw_map_permReindex_arrayCol_eq` — the symmetric column statement;
* `SeparatelyExchangeable.exists_directing_arrayRow_mixingLaw_invariant` and
  `SeparatelyExchangeable.exists_directing_arrayCol_mixingLaw_invariant` — directing-measure
  versions supplied by de Finetti.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581–598.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- If a measurable coordinatewise map preserves every finite-dimensional law of a mixed i.i.d.
process, then it preserves the law of any mixing representative. This is the uniqueness argument
shared by the row and column statements below. -/
private theorem mixingLaw_map_eq_of_blockLaw_map_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ℕ → Ω → (ℕ → α)}
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : MixedIIDWith μ Y ν)
    {f : (ℕ → α) → (ℕ → α)} (hf : Measurable f)
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (hblock : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      blockLaw μ (fun i ω ↦ f (Y i ω)) k = blockLaw μ Y k) :
    μ.map (fun ω ↦ (ν ω).map hf.aemeasurable) = μ.map ν := by
  have hmap := hν.map_values hf hY
  have hmap' : MixedIIDWith μ Y (fun ω ↦ (ν ω).map hf.aemeasurable) :=
    MixedIIDWith.intro hmap.measurable_mixingRepresentative fun m k hk ↦ by
      rw [← hblock m k hk]
      exact hmap.blockLaw_eq_mixture k hk
  exact mixedIID_mixingLaw_unique hY hmap' hν

/-- **The row mixing law inherits column symmetry.** For any mixing representative `ν` of the
row process, invariance of the array law under the column permutation `τ` implies that pushing
`ν` forward by `τ` does not change its law under `μ`.

This is a statement about the law `μ.map ν`, not an almost-sure assertion that each measure
`ν ω` is exchangeable. The latter is false in general. -/
theorem mixingLaw_map_permReindex_arrayRow_eq_of_col_invariant
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α} {τ : Equiv.Perm ℕ}
    (hcol : (μ.map fun ω p ↦ X (p.1, τ p.2) ω) = μ.map fun ω p ↦ X p ω)
    (hX : ∀ p, AEMeasurable (X p) μ)
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : MixedIIDWith μ (arrayRow X) ν) :
    μ.map (fun ω ↦ (ν ω).map (measurable_reindex τ).aemeasurable) = μ.map ν := by
  apply mixingLaw_map_eq_of_blockLaw_map_eq hν (measurable_reindex τ)
    (aemeasurable_arrayRow hX)
  intro m k _
  rw [blockLaw_def, blockLaw_def]
  have hleft :
      (fun ω ↦ fun i : Fin m ↦ fun j ↦ arrayRow X (k i) ω (τ j)) =
        fun ω ↦ fun i : Fin m ↦ fun j ↦ X (k i, τ j) ω := by
    funext ω i j
    rw [arrayRow_apply]
  have hright :
      (fun ω ↦ fun i : Fin m ↦ arrayRow X (k i) ω) =
        fun ω ↦ fun i : Fin m ↦ fun j ↦ X (k i, j) ω := by
    funext ω i j
    rw [arrayRow_apply]
  rw [hleft, hright]
  let F : (ℕ × ℕ → α) → (Fin m → ℕ → α) := fun x i j ↦ x (k i, j)
  have hF : Measurable F := measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦
    measurable_pi_apply (k i, j)
  rw [← map_map_array (X := fun p ↦ X (p.1, τ p.2)) (fun p ↦ hX _) hF,
    ← map_map_array hX hF, hcol]

/-- **The row mixing law of a separately exchangeable array inherits the column symmetry.** -/
theorem SeparatelyExchangeable.mixingLaw_map_permReindex_arrayRow_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : MixedIIDWith μ (arrayRow X) ν)
    (τ : Equiv.Perm ℕ) :
    μ.map (fun ω ↦ (ν ω).map (measurable_reindex τ).aemeasurable) = μ.map ν :=
  mixingLaw_map_permReindex_arrayRow_eq_of_col_invariant
    (separatelyExchangeable_iff.mp h 1 τ) hX hν

/-- **The column mixing law inherits row symmetry.** This is the transpose of
`mixingLaw_map_permReindex_arrayRow_eq_of_col_invariant`. -/
theorem mixingLaw_map_permReindex_arrayCol_eq_of_row_invariant
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α} {σ : Equiv.Perm ℕ}
    (hrow : (μ.map fun ω p ↦ X (σ p.1, p.2) ω) = μ.map fun ω p ↦ X p ω)
    (hX : ∀ p, AEMeasurable (X p) μ)
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : MixedIIDWith μ (arrayCol X) ν) :
    μ.map (fun ω ↦ (ν ω).map (measurable_reindex σ).aemeasurable) = μ.map ν := by
  apply mixingLaw_map_eq_of_blockLaw_map_eq hν (measurable_reindex σ)
    (aemeasurable_arrayCol hX)
  intro m k _
  rw [blockLaw_def, blockLaw_def]
  have hleft :
      (fun ω ↦ fun j : Fin m ↦ fun i ↦ arrayCol X (k j) ω (σ i)) =
        fun ω ↦ fun j : Fin m ↦ fun i ↦ X (σ i, k j) ω := by
    funext ω j i
    rw [arrayCol_apply]
  have hright :
      (fun ω ↦ fun j : Fin m ↦ arrayCol X (k j) ω) =
        fun ω ↦ fun j : Fin m ↦ fun i ↦ X (i, k j) ω := by
    funext ω j i
    rw [arrayCol_apply]
  rw [hleft, hright]
  let F : (ℕ × ℕ → α) → (Fin m → ℕ → α) := fun x j i ↦ x (i, k j)
  have hF : Measurable F := measurable_pi_lambda _ fun j ↦ measurable_pi_lambda _ fun i ↦
    measurable_pi_apply (i, k j)
  rw [← map_map_array (X := fun p ↦ X (σ p.1, p.2)) (fun p ↦ hX _) hF,
    ← map_map_array hX hF, hrow]

/-- **The column mixing law of a separately exchangeable array inherits the row symmetry.** -/
theorem SeparatelyExchangeable.mixingLaw_map_permReindex_arrayCol_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : MixedIIDWith μ (arrayCol X) ν)
    (σ : Equiv.Perm ℕ) :
    μ.map (fun ω ↦ (ν ω).map (measurable_reindex σ).aemeasurable) = μ.map ν :=
  mixingLaw_map_permReindex_arrayCol_eq_of_row_invariant
    (separatelyExchangeable_iff.mp h σ 1) hX hν

/-- **De Finetti for the rows, with the inherited mixing-law symmetry.** A separately
exchangeable array has a directing measure for its row process whose law is invariant under every
permutation of the path coordinates. -/
theorem SeparatelyExchangeable.exists_directing_arrayRow_mixingLaw_invariant
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayRow X) ν ∧
      ∀ τ : Equiv.Perm ℕ,
        μ.map (fun ω ↦ (ν ω).map (measurable_reindex τ).aemeasurable) = μ.map ν := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayRow hX).exists_directing
  exact ⟨ν, hν, fun τ ↦
    h.mixingLaw_map_permReindex_arrayRow_eq hX (mixedIIDWith_of_conditionallyIIDWith hν) τ⟩

/-- **De Finetti for the columns, with the inherited mixing-law symmetry.** -/
theorem SeparatelyExchangeable.exists_directing_arrayCol_mixingLaw_invariant
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayCol X) ν ∧
      ∀ σ : Equiv.Perm ℕ,
        μ.map (fun ω ↦ (ν ω).map (measurable_reindex σ).aemeasurable) = μ.map ν := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayCol hX).exists_directing
  exact ⟨ν, hν, fun σ ↦
    h.mixingLaw_map_permReindex_arrayCol_eq hX (mixedIIDWith_of_conditionallyIIDWith hν) σ⟩

end Probability

end TauCeti
