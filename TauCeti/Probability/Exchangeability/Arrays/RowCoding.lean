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
-- Non-public: the general symmetry proof transports the canonical conditional law on row paths.
import TauCeti.Probability.Exchangeability.ConditionallyIID.Map

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
* `TauCeti.Probability.map_pairReindex_arrayRowCodingLaw_eq` -- an invariant parameter law gives
  the coupled coding law its two-axis equivariance;
* `TauCeti.Probability.SeparatelyExchangeable.map_pairReindex_arrayRowCodingLaw_eq` -- the coupled
  coding law of a separately exchangeable array satisfies that general criterion.

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
  rw [arrayRowCodingLaw_def, Measure.map_map measurable_snd measurable_arrayRowCoding]
  change
    ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))).map
        fun q p => unitIntervalCoding (ℕ → α) q.1 (q.2 p.1) p.2) =
      (deFinettiBarycenter π).map Function.uncurry
  exact map_prod_unitIntervalCoding_array π

/-- The coupled coding law is the canonical conditionally i.i.d. law on rows, with the row paths
uncurried into an array. -/
private theorem arrayRowCodingLaw_eq_map_iidMixtureLaw
    (π : Measure (ProbabilityMeasure (ℕ → α))) :
    arrayRowCodingLaw π =
      (iidMixtureLaw π id).map (Prod.map id Function.uncurry) := by
  rw [arrayRowCodingLaw_def, ← map_prod_unitIntervalCoding_eq_iidMixtureLaw,
    Measure.map_map (measurable_id.prodMap measurable_uncurry)
      (measurable_fst.prodMk measurable_unitIntervalCodingPath)]
  refine congrArg (Measure.map · _) ?_
  funext q
  apply Prod.ext rfl
  funext p
  rfl

/-- The coupled row-coding law is equivariant whenever its parameter law is invariant under the
column pushforward. Row permutations require no invariance hypothesis; column permutations act on
both the parameter and the coded array. -/
theorem map_pairReindex_arrayRowCodingLaw_eq
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsFiniteMeasure π]
    (σ τ : Equiv.Perm ℕ)
    (hπ : π.map (fun P => P.map (measurable_reindex (α := α) τ).aemeasurable) = π) :
    (arrayRowCodingLaw π).map
        (fun q =>
          (q.1.map (measurable_reindex τ).aemeasurable, pairReindex σ τ q.2)) =
      arrayRowCodingLaw π := by
  let ρ := iidMixtureLaw π (id : ProbabilityMeasure (ℕ → α) → ProbabilityMeasure (ℕ → α))
  have hfst : ρ.map Prod.fst = π := by
    simpa only [ρ] using iidMixtureLaw_map_fst (π := π) (P := id) measurable_id
  have hρ : IsFiniteMeasure ρ := ⟨by
    calc
      ρ Set.univ = (ρ.map Prod.fst) Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        simp only [Set.preimage_univ]
      _ = π Set.univ := by rw [hfst]
      _ < ⊤ := measure_lt_top π Set.univ⟩
  let _ := hρ
  have hpush : Measurable fun P : ProbabilityMeasure (ℕ → α) =>
      P.map (measurable_reindex (α := α) τ).aemeasurable :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)
  have hbase : ConditionallyIIDWith ρ (fun i q => q.2 i) (fun q => q.1) := by
    simpa only [ρ, id_eq] using
      conditionallyIIDWith_iidMixtureLaw
        (π := π) (P := id) (α := ℕ → α) measurable_id
  have htrans : ConditionallyIIDWith ρ
      (fun i q j => q.2 (σ i) (τ j))
      (fun q => q.1.map (measurable_reindex τ).aemeasurable) := by
    simpa only using
      (hbase.comp_injective σ.injective).map_values (measurable_reindex (α := α) τ)
  have hνlaw :
      ρ.map (fun q => q.1.map (measurable_reindex (α := α) τ).aemeasurable) = π := by
    change (iidMixtureLaw π id).map
      ((fun P => P.map (measurable_reindex (α := α) τ).aemeasurable) ∘ Prod.fst) = π
    rw [← Measure.map_map hpush measurable_fst,
      iidMixtureLaw_map_fst (π := π) (P := id) measurable_id, hπ]
  have hjoint :
      ρ.map (fun q =>
        (q.1.map (measurable_reindex (α := α) τ).aemeasurable,
          fun i j => q.2 (σ i) (τ j))) =
        iidMixtureLaw π id := by
    rw [← jointPathLaw_def, htrans.jointPathLaw_eq_iidMixtureLaw, hνlaw]
  have hK : Measurable
      (Prod.map (id : ProbabilityMeasure (ℕ → α) → ProbabilityMeasure (ℕ → α))
        (Function.uncurry : (ℕ → ℕ → α) → (ℕ × ℕ → α))) :=
    measurable_id.prodMap measurable_uncurry
  have hF : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) =>
      (q.1.map (measurable_reindex (α := α) τ).aemeasurable,
        pairReindex σ τ q.2) :=
    (hpush.comp measurable_fst).prodMk
      ((measurable_pairReindex σ τ).comp measurable_snd)
  have htransform : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → ℕ → α) =>
      (q.1.map (measurable_reindex (α := α) τ).aemeasurable,
        fun i j => q.2 (σ i) (τ j)) :=
    (hpush.comp measurable_fst).prodMk <|
      measurable_pi_lambda _ fun i =>
        (measurable_reindex τ).comp ((measurable_pi_apply (σ i)).comp measurable_snd)
  calc
    (arrayRowCodingLaw π).map
          (fun q =>
            (q.1.map (measurable_reindex τ).aemeasurable, pairReindex σ τ q.2))
        = ρ.map (fun q =>
            (q.1.map (measurable_reindex τ).aemeasurable,
              pairReindex σ τ (Function.uncurry q.2))) := by
            rw [arrayRowCodingLaw_eq_map_iidMixtureLaw, Measure.map_map hF hK]
            rfl
    _ = ρ.map (fun q =>
          (q.1.map (measurable_reindex τ).aemeasurable,
            Function.uncurry fun i j => q.2 (σ i) (τ j))) := by
          refine congrArg (ρ.map ·) (funext fun q => Prod.ext rfl ?_)
          funext ⟨i, j⟩
          change pairReindex σ τ (Function.uncurry q.2) (i, j) = q.2 (σ i) (τ j)
          rw [pairReindex_apply]
          rfl
    _ = (ρ.map fun q =>
          (q.1.map (measurable_reindex τ).aemeasurable,
            fun i j => q.2 (σ i) (τ j))).map
          (Prod.map id Function.uncurry) := by
            rw [Measure.map_map hK htransform]
            refine congrArg (ρ.map ·) ?_
            funext q
            rfl
    _ = (iidMixtureLaw π id).map (Prod.map id Function.uncurry) := by rw [hjoint]
    _ = arrayRowCodingLaw π := (arrayRowCodingLaw_eq_map_iidMixtureLaw π).symm

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
    aemeasurable_entry_of_arrayRow h.aemeasurable
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
  apply TauCeti.Probability.map_pairReindex_arrayRowCodingLaw_eq (μ.map ν) σ τ
  have hpush : Measurable fun P : ProbabilityMeasure (ℕ → α) =>
      P.map (measurable_reindex (α := α) τ).aemeasurable :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_reindex τ)
  rw [Measure.map_map hpush hν.measurable_directing]
  exact h.mixingLaw_map_permReindex_arrayRow_eq
    (mixedIIDWith_of_conditionallyIIDWith hν) τ

end CodingLaw

end Probability

end TauCeti

end

end
