/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the directing-measure equivariance is transported to the canonical coding law.
public import TauCeti.Probability.Exchangeability.Arrays.JointLaw
-- Public: the canonical coding map occurs in the definition and every main statement.
public import TauCeti.Probability.Exchangeability.Arrays.Coding
-- Non-public: measurability of pushforward on probability measures is used in the symmetry proof.
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Coupled row coding for separately exchangeable arrays

The first functional representation of a separately exchangeable array writes each row as a
sample from one random path law, using independent uniform noise for the rows.  For the second
level of the Aldous--Hoover argument, it is essential to retain that random path law as a
coordinate: column permutations act on it by pushforward, rather than leaving it fixed.

This file packages the resulting canonical joint law.  If `π` is a law on probability measures on
path space, `arrayRowCodingLaw π` is the law of

```text
(P, (i, j) ↦ unitIntervalCoding (ℕ → α) P (Uᵢ) j),
```

where `P` has law `π` and the `Uᵢ` are independent uniform variables.  A directing measure for
the row process of an array identifies its joint law with this canonical law.  For a separately
exchangeable array, the canonical law retains the full two-axis symmetry: row permutations act
on the coded array alone, while column permutations act simultaneously on the array and by
pushforward on `P`.

This is the coupled interface needed by the second level of the exchangeable-arrays milestone in
`TauCetiRoadmap/Exchangeability/README.md`, Layer 8.  It does not assert the final
Aldous--Hoover representation: resolving the random path law into column and cell noise remains
the next step.

## Main definitions and results

* `TauCeti.Probability.arrayRowCodingLaw` -- the canonical joint law of the random row law and the
  coded array;
* `TauCeti.Probability.ConditionallyIIDWith.jointLaw_arrayRow_eq_arrayRowCodingLaw` -- a row
  directing measure identifies the original coupled law with the canonical coding law;
* `TauCeti.Probability.SeparatelyExchangeable.map_pairReindex_arrayRowCodingLaw_eq` -- the coupled
  coding law inherits the two-axis equivariance of the directing measure and the array.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for randomization by a
  uniform variable.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
arrays.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section CodingLaw

variable [StandardBorelSpace α] [Nonempty α]

omit [StandardBorelSpace α] [Nonempty α] in
/-- A row-process witness supplies measurability of every array entry. -/
private theorem aemeasurable_entries_of_conditionallyIIDWith_arrayRow
    {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (h : ConditionallyIIDWith μ (arrayRow X) ν) (p : ℕ × ℕ) :
    AEMeasurable (X p) μ := by
  have hentry : AEMeasurable (fun ω => arrayRow X p.1 ω p.2) μ :=
    (measurable_pi_apply p.2).comp_aemeasurable (h.aemeasurable p.1)
  simpa [arrayRow_apply] using hentry

/-- The measurable map which retains a path law and uses one independent uniform variable to
sample each row from it. -/
theorem measurable_arrayRowCoding :
    Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) =>
      (q.1, fun p : ℕ × ℕ => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun p => measurable_unitIntervalCoding_entry p)

/-- The canonical coupled law of a random path measure and the array obtained by independently
sampling its rows. -/
def arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    Measure (ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α)) :=
  (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
    fun q => (q.1,
      fun p : ℕ × ℕ => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2)

/-- The defining pushforward formula for `arrayRowCodingLaw`. -/
theorem arrayRowCodingLaw_def (π : Measure (ProbabilityMeasure (ℕ → α))) :
    arrayRowCodingLaw π =
      (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
        fun q => (q.1,
          fun p : ℕ × ℕ => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) :=
  (rfl)

/-- Coding a probability law of random path measures gives a probability law of the coupled
parameter and array. -/
instance instIsProbabilityMeasureArrayRowCodingLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (arrayRowCodingLaw π) := by
  rw [arrayRowCodingLaw_def]
  exact Measure.isProbabilityMeasure_map measurable_arrayRowCoding.aemeasurable

/-- The first marginal of the coupled coding law is the supplied law of the random path measure. -/
@[simp]
theorem map_fst_arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (arrayRowCodingLaw π).map Prod.fst = π := by
  rw [arrayRowCodingLaw_def, Measure.map_map measurable_fst measurable_arrayRowCoding]
  have hcomp :
      Prod.fst ∘ (fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) =>
        (q.1, fun p : ℕ × ℕ => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2)) =
          Prod.fst := rfl
  rw [hcomp, Measure.map_fst_prod, measure_univ, one_smul]

/-- The array marginal of the coupled coding law is the uncurried de Finetti barycenter of the
law of the random path measure. -/
@[simp]
theorem map_snd_arrayRowCodingLaw (π : Measure (ProbabilityMeasure (ℕ → α))) :
    (arrayRowCodingLaw π).map Prod.snd =
      (deFinettiBarycenter π).map Function.uncurry := by
  rw [arrayRowCodingLaw_def, Measure.map_map measurable_snd measurable_arrayRowCoding,
    ← map_prod_unitIntervalCoding_eq_deFinettiBarycenter (α := ℕ → α),
    Measure.map_map measurable_uncurry measurable_unitIntervalCodingPath]
  refine congrArg (Measure.map · _) ?_
  funext q p
  rfl

/-- A directing measure for the row process identifies its joint law with the canonical coupled
row-coding law.  Unlike the array-law-only coding theorem, this keeps the directing measure as a
coordinate, so its transformation under column permutations remains visible. -/
theorem ConditionallyIIDWith.jointLaw_arrayRow_eq_arrayRowCodingLaw
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (h : ConditionallyIIDWith μ (arrayRow X) ν) :
    (μ.map fun ω => (ν ω, fun p : ℕ × ℕ => X p ω)) =
      arrayRowCodingLaw (μ.map ν) := by
  have hX : ∀ p, AEMeasurable (X p) μ :=
    aemeasurable_entries_of_conditionallyIIDWith_arrayRow h
  rw [← map_uncurry_jointPathLaw_arrayRow hX h.measurable_directing,
    h.jointPathLaw_eq_map_unitIntervalCoding, arrayRowCodingLaw_def]
  have hinner : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) =>
      (q.1, fun i => unitIntervalCoding (ℕ → α) q.1 (q.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  rw [Measure.map_map (measurable_id.prodMap measurable_uncurry) hinner]
  refine congrArg (Measure.map · _) ?_
  funext q
  apply Prod.ext rfl
  funext p
  rfl

/-- The coupled row-coding law of a separately exchangeable array retains both symmetries.  A row
permutation reindexes only the coded array.  A column permutation also pushes the random path law
forward by the same coordinate permutation. -/
theorem SeparatelyExchangeable.map_pairReindex_arrayRowCodingLaw_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (h : SeparatelyExchangeable μ X)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (σ τ : Equiv.Perm ℕ) :
    (arrayRowCodingLaw (μ.map ν)).map
        (fun q =>
          (q.1.map (measurable_reindex τ).aemeasurable, pairReindex σ τ q.2)) =
      arrayRowCodingLaw (μ.map ν) := by
  have hX : ∀ p, AEMeasurable (X p) μ :=
    aemeasurable_entries_of_conditionallyIIDWith_arrayRow hν
  rw [← hν.jointLaw_arrayRow_eq_arrayRowCodingLaw,
    AEMeasurable.map_map_of_aemeasurable]
  · have hfun :
        ((fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) =>
            (q.1.map (measurable_reindex τ).aemeasurable, pairReindex σ τ q.2)) ∘
          fun ω => (ν ω, fun p : ℕ × ℕ => X p ω)) =
            fun ω => ((ν ω).map (measurable_reindex τ).aemeasurable,
              fun p : ℕ × ℕ => X (σ p.1, τ p.2) ω) := by
          funext ω
          rw [Function.comp_apply]
          refine Prod.ext rfl ?_
          funext p
          simp only [pairReindex_apply]
    rw [hfun]
    exact h.jointLaw_arrayRow_pairReindex_eq hX hν σ τ
  · exact ((TauCeti.MeasureTheory.measurable_probabilityMeasure_map
      (measurable_reindex τ)).comp measurable_fst).prodMk
        ((measurable_pairReindex σ τ).comp measurable_snd) |>.aemeasurable
  · exact hν.measurable_directing.aemeasurable.prodMk
      (aemeasurable_pi_lambda _ hX)

end CodingLaw

end Probability

end TauCeti

end

end
