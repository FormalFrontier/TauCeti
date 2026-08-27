/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Data.Setoid.Partition

/-!
# Integrals split by finite measurable partitions

A measurable finite partition of a measure space decomposes integrals on the product space into
finite sums over partition rectangles.  This file also records that measurable bipartitions and
common refinements have measurable parts.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Finpartition

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Every part of a bipartition along a measurable set is measurable. -/
theorem measurableSet_of_mem_bipartition {s p : Set Ω} (hs : MeasurableSet s)
    (hp : p ∈ (bipartition s).parts) : MeasurableSet p := by
  rw [parts_bipartition, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp.2 with rfl | rfl
  · exact hs
  · exact hs.compl

/-- The common refinement of two measurable finite partitions is measurable. -/
theorem measurableSet_of_mem_inf {u : Set Ω} {P Q : Finpartition u}
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (hQ : ∀ q ∈ Q.parts, MeasurableSet q)
    {r : Set Ω} (hr : r ∈ (P ⊓ Q).parts) : MeasurableSet r := by
  rw [Finpartition.parts_inf, Finset.mem_erase, Finset.mem_image] at hr
  obtain ⟨_, pq, hpq, rfl⟩ := hr
  rw [Finset.mem_product] at hpq
  exact (hP pq.1 hpq.1).inter (hQ pq.2 hpq.2)

/-- A finite measurable partition of the carrier cuts a rectangle into finitely many disjoint
subrectangles, splitting any integral over it into a finite sum. -/
theorem setIntegral_prod_eq_sum_parts (R : Finpartition (Set.univ : Set Ω))
    (hR : ∀ r ∈ R.parts, MeasurableSet r) {S T : Set Ω} (hS : MeasurableSet S)
    (hT : MeasurableSet T) {f : Ω × Ω → ℝ} (hf : IntegrableOn f (S ×ˢ T) (μ.prod μ)) :
    ∫ z in S ×ˢ T, f z ∂(μ.prod μ)
      = ∑ rs : R.parts × R.parts,
          ∫ z in ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T), f z ∂(μ.prod μ) := by
  have hmeas : ∀ rs : R.parts × R.parts,
      MeasurableSet (((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T)) := fun rs =>
    ((hR _ rs.1.property).inter hS).prod ((hR _ rs.2.property).inter hT)
  have hdisj : Pairwise (Function.onFun Disjoint fun rs : R.parts × R.parts =>
      ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T)) := by
    intro rs rs' hne
    have key : ∀ {u v : R.parts} {A : Set Ω}, u ≠ v →
        ((u : Set Ω) ∩ A) ∩ ((v : Set Ω) ∩ A) = ∅ := by
      intro u v A huv
      refine disjoint_iff_inter_eq_empty.mp ?_
      exact (R.disjoint u.property v.property fun h => huv (Subtype.ext h)).mono
        inter_subset_left inter_subset_left
    simp only [Function.onFun, disjoint_iff_inter_eq_empty, prod_inter_prod, prod_eq_empty_iff]
    by_cases h1 : rs.1 = rs'.1
    · refine Or.inr (key ?_)
      intro h2
      exact hne (Prod.ext h1 h2)
    · exact Or.inl (key h1)
  have hcover : ⋃ r : R.parts, (r : Set Ω) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃₀ (R.parts : Set (Set Ω)) := by
      rw [R.isPartition_parts.sUnion_eq_univ]
      exact Set.mem_univ x
    obtain ⟨r, hr, hxr⟩ := Set.mem_sUnion.mp hx
    exact Set.mem_iUnion.2 ⟨⟨r, hr⟩, hxr⟩
  have hunion : (⋃ rs : R.parts × R.parts, ((rs.1 : Set Ω) ∩ S) ×ˢ ((rs.2 : Set Ω) ∩ T))
      = S ×ˢ T := by
    rw [iUnion_prod (fun r : R.parts => (r : Set Ω) ∩ S) fun r : R.parts => (r : Set Ω) ∩ T,
      ← iUnion_inter, ← iUnion_inter, hcover, univ_inter, univ_inter]
  rw [← hunion, integral_iUnion_fintype hmeas hdisj fun _ =>
    hf.mono_set (prod_mono inter_subset_right inter_subset_right)]

/-- A finite measurable partition of the carrier splits an integral over the whole product carrier
into a finite sum over its rectangles. -/
theorem integral_eq_sum_parts (R : Finpartition (Set.univ : Set Ω))
    (hR : ∀ r ∈ R.parts, MeasurableSet r) {f : Ω × Ω → ℝ} (hf : Integrable f (μ.prod μ)) :
    ∫ z, f z ∂(μ.prod μ)
      = ∑ rs : R.parts × R.parts, ∫ z in (rs.1 : Set Ω) ×ˢ (rs.2 : Set Ω), f z ∂(μ.prod μ) := by
  rw [← setIntegral_univ (μ := μ.prod μ), ← univ_prod_univ,
    setIntegral_prod_eq_sum_parts μ R hR MeasurableSet.univ MeasurableSet.univ hf.integrableOn]
  simp

end Finpartition
