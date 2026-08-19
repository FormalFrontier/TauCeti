/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat

/-!
# Projective limits on countable products

This file extends the sequence-indexed Kolmogorov extension theorem from
`TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat` to an arbitrary countable index type. Finite
index types are handled directly by the law on all coordinates; infinite countable types are
enumerated and reduced to the sequence theorem.

## Main result

* `TauCeti.Measure.exists_isProjectiveLimit_of_countable` realizes every projective family of
  probability laws on finite subsets of a countable family of standard Borel spaces.

The proof transports finite-dimensional laws along measurable equivalences of dependent products.
This is the arbitrary-countable-index existence bridge required by
`TauCetiRoadmap/OptimalTransport/README.md`, Layer 0, item 4.
-/

public section

noncomputable section

open Finset MeasureTheory

namespace TauCeti

namespace Measure

universe u v

variable {ι : Type u} {κ : Type v} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Reindex a finite dependent product along an equivalence of its coordinate types. -/
private def finitePiCongrLeft (e : κ ≃ ι) (J : Finset κ) :
    (∀ j : J, X (e j)) ≃ᵐ (∀ i : J.map e.toEmbedding, X i) :=
  MeasurableEquiv.piCongrLeft (fun i : J.map e.toEmbedding ↦ X i)
    (J.equivMap e.toEmbedding)

private theorem finitePiCongrLeft_apply (e : κ ≃ ι) (J : Finset κ)
    (x : ∀ j : J, X (e j)) (j : J) :
    finitePiCongrLeft e J x (J.equivMap e.toEmbedding j) = x j := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun i : J.map e.toEmbedding ↦ X i) (J.equivMap e.toEmbedding) x j

private theorem finitePiCongrLeft_symm_apply (e : κ ≃ ι) (J : Finset κ)
    (x : ∀ i : J.map e.toEmbedding, X i) (j : J) :
    (finitePiCongrLeft e J).symm x j = x (J.equivMap e.toEmbedding j) := by
  exact Equiv.piCongrLeft_symm_apply
    (fun i : J.map e.toEmbedding ↦ X i) (J.equivMap e.toEmbedding) x j

/-- Reindex the finite-dimensional laws of a projective family along an equivalence. -/
private def reindexProjectiveFamily (e : κ ≃ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    Measure (∀ j : J, X (e j)) :=
  (P (J.map e.toEmbedding)).map (finitePiCongrLeft e J).symm

private instance reindexProjectiveFamily.instIsProbabilityMeasure (e : κ ≃ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (J : Finset κ) : IsProbabilityMeasure (reindexProjectiveFamily e P J) :=
  MeasureTheory.Measure.isProbabilityMeasure_map
    (finitePiCongrLeft e J).symm.measurable.aemeasurable

private theorem isProjectiveMeasureFamily_reindex (e : κ ≃ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) (reindexProjectiveFamily e P) := by
  intro I J hJI
  have hmapJI : J.map e.toEmbedding ⊆ I.map e.toEmbedding :=
    Finset.map_subset_map.mpr hJI
  rw [reindexProjectiveFamily, reindexProjectiveFamily,
    hP (I.map e.toEmbedding) (J.map e.toEmbedding) hmapJI]
  rw [MeasureTheory.Measure.map_map (finitePiCongrLeft e J).symm.measurable
      (Finset.measurable_restrict₂ hmapJI)]
  have hfun :
      ((finitePiCongrLeft e J).symm ∘ Finset.restrict₂ hmapJI :
        (∀ i : I.map e.toEmbedding, X i) → (∀ j : J, X (e j))) =
      Finset.restrict₂ (π := fun i ↦ X (e i)) hJI ∘
        (finitePiCongrLeft e I).symm := by
    funext x j
    simp only [Function.comp_apply, Finset.restrict₂_def, finitePiCongrLeft_symm_apply]
    congr 1
  rw [hfun]
  exact (MeasureTheory.Measure.map_map (Finset.measurable_restrict₂ hJI)
    (finitePiCongrLeft e I).symm.measurable).symm

/-- A projective family on a finite coordinate type is realized by its law on the full finite
product. -/
private theorem exists_isProjectiveLimit_of_finite [Finite ι]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  let _ := Fintype.ofFinite ι
  let e : (Finset.univ : Finset ι) ≃ ι :=
    { toFun := fun i ↦ i
      invFun := fun i ↦ ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let E : (∀ j : (Finset.univ : Finset ι), X j) ≃ᵐ (∀ i, X i) :=
    MeasurableEquiv.piCongrLeft X e
  refine ⟨(P Finset.univ).map E,
    MeasureTheory.Measure.isProbabilityMeasure_map E.measurable.aemeasurable, fun I ↦ ?_⟩
  rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict I) E.measurable]
  have hrestrict : I.restrict ∘ E =
      Finset.restrict₂ (Finset.subset_univ I) := by
    funext x i
    simpa [Function.comp_apply, Finset.restrict_def, Finset.restrict₂_def, E, e] using
      MeasurableEquiv.piCongrLeft_apply_apply
        (β := X) e x ⟨i, Finset.mem_univ (i : ι)⟩
  rw [hrestrict, hP Finset.univ I (Finset.subset_univ I)]

/-- An infinite countable projective family is realized by enumerating its coordinates and
applying the sequence-indexed extension theorem. -/
private theorem exists_isProjectiveLimit_of_countable_infinite [Countable ι] [Infinite ι]
    [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  let e : ℕ ≃ ι := Classical.choice (inferInstance : Nonempty (ℕ ≃ ι))
  let Q : ∀ J : Finset ℕ, Measure (∀ j : J, X (e j)) := reindexProjectiveFamily e P
  have hQ : IsProjectiveMeasureFamily (α := fun j ↦ X (e j)) Q :=
    isProjectiveMeasureFamily_reindex e P hP
  let _ : ∀ n, StandardBorelSpace (X (e (n + 1))) := fun _ ↦ inferInstance
  obtain ⟨ν, hνprob, hν⟩ :=
    exists_isProjectiveLimit_nat (X := fun n ↦ X (e n)) Q hQ
  let E : (∀ n, X (e n)) ≃ᵐ (∀ i, X i) := MeasurableEquiv.piCongrLeft X e
  refine ⟨ν.map E, MeasureTheory.Measure.isProbabilityMeasure_map E.measurable.aemeasurable,
    fun I ↦ ?_⟩
  let J : Finset ℕ := I.map e.symm.toEmbedding
  have hmap : J.map e.toEmbedding = I := by
    simp [J, Finset.map_map]
  have hcomm : (J.map e.toEmbedding).restrict ∘ E =
      finitePiCongrLeft e J ∘ J.restrict := by
    funext x i
    let j : J := (J.equivMap e.toEmbedding).symm i
    rw [Function.comp_apply, Function.comp_apply,
      ← (J.equivMap e.toEmbedding).apply_symm_apply i,
      finitePiCongrLeft_apply]
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := X) e x j
  have hlimit : (ν.map E).map (J.map e.toEmbedding).restrict =
      P (J.map e.toEmbedding) := by
    rw [MeasureTheory.Measure.map_map (Finset.measurable_restrict (J.map e.toEmbedding))
      E.measurable, hcomm,
      ← MeasureTheory.Measure.map_map (finitePiCongrLeft e J).measurable
        (Finset.measurable_restrict J), hν J]
    simpa only [Q, reindexProjectiveFamily] using
      MeasurableEquiv.map_map_symm (ν := P (J.map e.toEmbedding))
        (finitePiCongrLeft e J)
  exact hmap ▸ hlimit

/-- **Kolmogorov extension on an arbitrary countable index type.** Every projective family of
probability laws on the finite subproducts of a countable family of standard Borel spaces has a
projective limit, which is again a probability measure.

For finite index types the full-dimensional member of the family is already the desired law. For
infinite countable types, an enumeration reduces the result to
`TauCeti.Measure.exists_isProjectiveLimit_nat`. Mathlib's
`MeasureTheory.IsProjectiveLimit.unique` gives uniqueness. -/
theorem exists_isProjectiveLimit_of_countable [Countable ι]
    [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  rcases finite_or_infinite ι with hι | hι
  · exact exists_isProjectiveLimit_of_finite P hP
  · exact exists_isProjectiveLimit_of_countable_infinite P hP

end Measure

end TauCeti
