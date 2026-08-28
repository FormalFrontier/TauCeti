/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.DeFinetti
public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
-- Non-public: the closure of the conditional predicate under a coordinatewise map is used only to
-- produce the directing measure of a reindexed array.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map
-- Non-public: the Giry-measurability of a pushforward is used only inside the proofs below.
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# The directing measure of a separately exchangeable array is equivariant

Applying de Finetti to the rows of a separately exchangeable array produces a directing measure
`ν` on row paths, and `Arrays.MixingLaw` records the symmetry it inherits from the remaining column
freedom: the *law* of `ν` is invariant under pushing every row path forward by a permutation `τ` of
the time coordinate. That statement forgets how `ν` is coupled to the array, and the coupling is
exactly what the next step of the Aldous--Hoover argument has to work with: the column randomness
of the array is carried by `ν`, not by the conditionally i.i.d. rows, so column symmetry has to be
available *after* conditioning on `ν`.

This file supplies the coupled statement. For all permutations `σ` of the rows and `τ` of the
columns,

```text
Law (ν.map (permReindex τ),  (i, j) ↦ X (σ i, τ j))  =  Law (ν,  (i, j) ↦ X (i, j)).
```

Row permutations leave the directing measure alone and column permutations push it forward. Taking
the first marginal recovers the conclusion of
`SeparatelyExchangeable.mixingLaw_map_permReindex_arrayRow_eq` at a directing measure, and taking
the second recovers separate exchangeability itself.

Both refinements are genuine. The statement is *conditional-side*: it is false for an arbitrary
mixing representative, since an independent copy of a directing measure is another mixing
representative with a different coupling to the array, so it must be read off the joint law rather
than the mixture identity. And it is *equivariant* rather than invariant: `ν` is almost surely not
an exchangeable measure — if every row is one common i.i.d. path `Y`, then `ν = δ_Y` — so the
column permutation cannot simply be dropped.

## Main results

* `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayRow_pairReindex_eq` — the displayed
  identity;
* `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayRow_rowReindex_eq` and
  `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayRow_colReindex_eq` — its two axes
  separately;
* `TauCeti.Probability.SeparatelyExchangeable.exists_directing_arrayRow_jointLaw_equivariant` —
  de Finetti supplies a directing measure with this symmetry;
* `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayCol_pairReindex_eq` — the transposed
  statement for the column directing measure, again with its two axes separately as
  `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayCol_rowReindex_eq` and
  `TauCeti.Probability.SeparatelyExchangeable.jointLaw_arrayCol_colReindex_eq`.

## Implementation

Everything is deduced from one general fact, `ConditionallyIIDWith.jointPathLaw_eq_of_pathLaw_eq`:
a conditionally i.i.d. process determines the joint law of its directing measure and its path
through the path law alone. The reindexed array has a directing measure for its rows by the two
closure lemmas `ConditionallyIIDWith.comp_injective` (permute the rows) and
`ConditionallyIIDWith.map_values` (permute the time coordinate of each row path), and separate
exchangeability says its row process has the original path law. Transporting the resulting identity
of joint path laws along a measurable reassembly of the array from its row — or column — process
gives the array-level statements.

`arrayRow` and `arrayCol` are ordinary definitions rather than reducible abbreviations, so the
proofs move between a process of paths and the entries of the array through their `@[simp]`
evaluation lemmas rather than by definitional unfolding.

These results advance the exchangeable-arrays milestone in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581–598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable sequences
rather than exchangeable arrays.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure Ω} {X : ℕ × ℕ → Ω → α} {ν : Ω → ProbabilityMeasure (ℕ → α)}

/-! ### Transporting a joint path law to the array -/

omit [MeasurableSpace α] [MeasurableSpace Ω] in
/-- The row process of an array, with `arrayRow` eliminated in favour of the entries. `arrayRow` is
an ordinary definition, so the proofs below normalise with this rather than unfold it. -/
private theorem arrayRow_eq_entries (X : ℕ × ℕ → Ω → α) :
    arrayRow X = fun i ω j => X (i, j) ω := by
  funext i ω j
  simp

omit [MeasurableSpace α] [MeasurableSpace Ω] in
/-- The column process of an array, with `arrayCol` eliminated in favour of the entries. -/
private theorem arrayCol_eq_entries (X : ℕ × ℕ → Ω → α) :
    arrayCol X = fun j ω i => X (i, j) ω := by
  funext j ω i
  simp

/-- Currying an array-shaped path into its rows. -/
private theorem measurable_rowsOf :
    Measurable fun x : ℕ × ℕ → α => fun i j => x (i, j) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_apply (i, j)

/-- Currying an array-shaped path into its columns. -/
private theorem measurable_colsOf :
    Measurable fun x : ℕ × ℕ → α => fun j i => x (i, j) :=
  measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => measurable_pi_apply (i, j)

/-- Reassembling an array from its columns. -/
private theorem measurable_uncurrySwap :
    Measurable fun x : ℕ → ℕ → α => fun p : ℕ × ℕ => x p.2 p.1 :=
  measurable_pi_lambda _ fun p => (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)

omit [MeasurableSpace Ω] in
/-- Pushing a probability measure on path space forward by the identity permutation of time does
nothing. This is what specialises the pair-reindexing laws below to a single axis. -/
private theorem map_permReindex_one (P : ProbabilityMeasure (ℕ → α)) :
    P.map (measurable_reindex (α := α) (1 : Equiv.Perm ℕ)).aemeasurable = P :=
  ProbabilityMeasure.toMeasure_injective (by simp)

/-- Reassembling the array from its row process turns the joint law of a random measure and the row
process into the joint law of that random measure and the array. -/
theorem map_uncurry_jointPathLaw_arrayRow (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : Measurable ν) :
    (jointPathLaw μ (arrayRow X) ν).map (Prod.map id Function.uncurry)
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  rw [jointPathLaw_def, AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap measurable_uncurry).aemeasurable
    (hν.aemeasurable.prodMk (aemeasurable_pi_lambda _ (aemeasurable_arrayRow hX)))]
  refine congrArg (Measure.map · _) (funext fun ω => Prod.ext rfl (funext fun p => ?_))
  simp [Function.uncurry]

/-- Reassembling the array from its column process turns the joint law of a random measure and the
column process into the joint law of that random measure and the array. -/
theorem map_uncurrySwap_jointPathLaw_arrayCol (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : Measurable ν) :
    (jointPathLaw μ (arrayCol X) ν).map
        (Prod.map id fun x : ℕ → ℕ → α => fun p : ℕ × ℕ => x p.2 p.1)
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  rw [jointPathLaw_def, AEMeasurable.map_map_of_aemeasurable
    (measurable_id.prodMap measurable_uncurrySwap).aemeasurable
    (hν.aemeasurable.prodMk (aemeasurable_pi_lambda _ (aemeasurable_arrayCol hX)))]
  refine congrArg (Measure.map · _) (funext fun ω => Prod.ext rfl (funext fun p => ?_))
  simp

/-! ### The row directing measure -/

/-- **Equivariance of the row directing measure, at the level of the row process.** Reindexing the
rows of a separately exchangeable array by `σ` and the columns by `τ`, and pushing the directing
measure forward by `τ`, leaves the joint law of the directing measure and the row process
unchanged. -/
theorem SeparatelyExchangeable.jointPathLaw_arrayRow_pairReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (σ τ : Equiv.Perm ℕ) :
    jointPathLaw μ (arrayRow fun p => X (σ p.1, τ p.2))
        (fun ω => (ν ω).map (measurable_reindex τ).aemeasurable)
      = jointPathLaw μ (arrayRow X) ν := by
  simp only [arrayRow_eq_entries] at hν ⊢
  exact ((hν.comp_injective σ.injective).map_values
    (measurable_reindex (α := α) τ)).jointPathLaw_eq_of_pathLaw_eq hν
    (h.map_comp hX σ τ measurable_rowsOf)

/-- **Equivariance of the row directing measure.** For a separately exchangeable array with row
directing measure `ν`, the joint law of `ν` and the array is unchanged when the rows are reindexed
by `σ`, the columns by `τ`, and `ν` is pushed forward by `τ`.

Rows and columns enter differently, and both asymmetries are real: the rows are the coordinates of
the conditionally i.i.d. process that `ν` directs, so permuting them does not disturb `ν`, while
the columns are coordinates *inside* each row path, so permuting them acts on `ν`. -/
theorem SeparatelyExchangeable.jointLaw_arrayRow_pairReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (σ τ : Equiv.Perm ℕ) :
    (μ.map fun ω => ((ν ω).map (measurable_reindex τ).aemeasurable,
        fun p : ℕ × ℕ => X (σ p.1, τ p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  have hν' : Measurable fun ω => (ν ω).map (measurable_reindex (α := α) τ).aemeasurable :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)).comp
      hν.measurable_directing
  rw [← map_uncurry_jointPathLaw_arrayRow (X := fun p => X (σ p.1, τ p.2)) (fun p => hX _) hν',
    ← map_uncurry_jointPathLaw_arrayRow hX hν.measurable_directing,
    h.jointPathLaw_arrayRow_pairReindex_eq hX hν σ τ]

/-- **Row permutations leave the row directing measure alone.** The rows are the coordinates of the
process that `ν` directs, so a permutation of them is absorbed by conditional i.i.d.-ness.

This is `SeparatelyExchangeable.jointLaw_arrayRow_pairReindex_eq` at the identity column
permutation, whose pushforward of `ν` is the identity. -/
theorem SeparatelyExchangeable.jointLaw_arrayRow_rowReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (σ : Equiv.Perm ℕ) :
    (μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X (σ p.1, p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  have key := h.jointLaw_arrayRow_pairReindex_eq hX hν σ 1
  simp only [map_permReindex_one] at key
  simpa only [Equiv.Perm.coe_one, id_eq] using key

/-- **Column permutations push the row directing measure forward.** This is the half of
`SeparatelyExchangeable.jointLaw_arrayRow_pairReindex_eq` that carries information about `ν`. -/
theorem SeparatelyExchangeable.jointLaw_arrayRow_colReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (τ : Equiv.Perm ℕ) :
    (μ.map fun ω => ((ν ω).map (measurable_reindex τ).aemeasurable,
        fun p : ℕ × ℕ => X (p.1, τ p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) :=
  h.jointLaw_arrayRow_pairReindex_eq hX hν 1 τ

/-- **De Finetti for the rows, with the inherited joint symmetry.** Over a nonempty standard Borel
state space a separately exchangeable array has a row directing measure whose joint law with the
array is equivariant for the two axis permutations.

This refines `SeparatelyExchangeable.exists_directing_arrayRow_mixingLaw_invariant`, whose
conclusion is the first marginal of this one. -/
theorem SeparatelyExchangeable.exists_directing_arrayRow_jointLaw_equivariant
    [StandardBorelSpace α] [Nonempty α] [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayRow X) ν ∧
      ∀ σ τ : Equiv.Perm ℕ,
        (μ.map fun ω => ((ν ω).map (measurable_reindex τ).aemeasurable,
            fun p : ℕ × ℕ => X (σ p.1, τ p.2) ω))
          = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayRow hX).exists_directing
  exact ⟨ν, hν, fun σ τ => h.jointLaw_arrayRow_pairReindex_eq hX hν σ τ⟩

/-! ### The column directing measure -/

/-- **Equivariance of the column directing measure, at the level of the column process.** The
transpose of `SeparatelyExchangeable.jointPathLaw_arrayRow_pairReindex_eq`: now the row permutation
acts on the directing measure and the column permutation is absorbed. -/
theorem SeparatelyExchangeable.jointPathLaw_arrayCol_pairReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayCol X) ν) (σ τ : Equiv.Perm ℕ) :
    jointPathLaw μ (arrayCol fun p => X (σ p.1, τ p.2))
        (fun ω => (ν ω).map (measurable_reindex σ).aemeasurable)
      = jointPathLaw μ (arrayCol X) ν := by
  simp only [arrayCol_eq_entries] at hν ⊢
  exact ((hν.comp_injective τ.injective).map_values
    (measurable_reindex (α := α) σ)).jointPathLaw_eq_of_pathLaw_eq hν
    (h.map_comp hX σ τ measurable_colsOf)

/-- **Equivariance of the column directing measure.** The transpose of
`SeparatelyExchangeable.jointLaw_arrayRow_pairReindex_eq`. -/
theorem SeparatelyExchangeable.jointLaw_arrayCol_pairReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayCol X) ν) (σ τ : Equiv.Perm ℕ) :
    (μ.map fun ω => ((ν ω).map (measurable_reindex σ).aemeasurable,
        fun p : ℕ × ℕ => X (σ p.1, τ p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  have hν' : Measurable fun ω => (ν ω).map (measurable_reindex (α := α) σ).aemeasurable :=
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex σ)).comp
      hν.measurable_directing
  rw [← map_uncurrySwap_jointPathLaw_arrayCol (X := fun p => X (σ p.1, τ p.2)) (fun p => hX _) hν',
    ← map_uncurrySwap_jointPathLaw_arrayCol hX hν.measurable_directing,
    h.jointPathLaw_arrayCol_pairReindex_eq hX hν σ τ]

/-- **Row permutations push the column directing measure forward.** This is the half of
`SeparatelyExchangeable.jointLaw_arrayCol_pairReindex_eq` that carries information about `ν`. -/
theorem SeparatelyExchangeable.jointLaw_arrayCol_rowReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayCol X) ν) (σ : Equiv.Perm ℕ) :
    (μ.map fun ω => ((ν ω).map (measurable_reindex σ).aemeasurable,
        fun p : ℕ × ℕ => X (σ p.1, p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) :=
  h.jointLaw_arrayCol_pairReindex_eq hX hν σ 1

/-- **Column permutations leave the column directing measure alone.** The columns are the
coordinates of the process that `ν` directs, so a permutation of them is absorbed by conditional
i.i.d.-ness. -/
theorem SeparatelyExchangeable.jointLaw_arrayCol_colReindex_eq [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ)
    (hν : ConditionallyIIDWith μ (arrayCol X) ν) (τ : Equiv.Perm ℕ) :
    (μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X (p.1, τ p.2) ω))
      = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  have key := h.jointLaw_arrayCol_pairReindex_eq hX hν 1 τ
  simp only [map_permReindex_one] at key
  simpa only [Equiv.Perm.coe_one, id_eq] using key

/-- **De Finetti for the columns, with the inherited joint symmetry.** -/
theorem SeparatelyExchangeable.exists_directing_arrayCol_jointLaw_equivariant
    [StandardBorelSpace α] [Nonempty α] [IsFiniteMeasure μ]
    (h : SeparatelyExchangeable μ X) (hX : ∀ p, AEMeasurable (X p) μ) :
    ∃ ν : Ω → ProbabilityMeasure (ℕ → α), ConditionallyIIDWith μ (arrayCol X) ν ∧
      ∀ σ τ : Equiv.Perm ℕ,
        (μ.map fun ω => ((ν ω).map (measurable_reindex σ).aemeasurable,
            fun p : ℕ × ℕ => X (σ p.1, τ p.2) ω))
          = μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω) := by
  obtain ⟨ν, hν⟩ := (h.conditionallyIID_arrayCol hX).exists_directing
  exact ⟨ν, hν, fun σ τ => h.jointLaw_arrayCol_pairReindex_eq hX hν σ τ⟩

end Probability

end TauCeti

end

end
