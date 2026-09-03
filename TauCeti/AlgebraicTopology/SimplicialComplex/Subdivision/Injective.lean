/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Surjective

/-!
# Injectivity of the barycentric-subdivision realization map

The canonical realization map sends a face-vertex of the barycentric subdivision to the
barycenter of that face. This file proves that the map is injective, and hence bijective by the
surjectivity theorem in `Subdivision.Surjective`.

The key point is positivity. A point of a subdivision simplex is a nonnegative linear combination
of the barycenters of a chain of faces. The greatest face in the support is exactly the support of
the resulting point in the original realization. Moreover, that greatest face has a vertex which
belongs to no smaller face in the chain; evaluating there recovers its coefficient. Removing the
greatest face and inducting proves uniqueness of all the coefficients.

This is the second bijectivity step in the subdivision-realization milestone in Layer 11 of the
GeometricTopology roadmap. `Subdivision.Homeomorph` proves continuity of the inverse and packages
the resulting bijection as a homeomorphism.

The argument follows the standard uniqueness proof for barycentric subdivision in
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2, "Derived Subdivisions".

## Main results

* `AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_injective`: the canonical
  realization map is one-to-one.
* `AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_bijective`: the canonical
  realization map is a bijection.
-/

public section

noncomputable section

open Finset Set TauCeti TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- A finite nonempty chain in a partial order has a greatest element. -/
private theorem exists_greatest_of_isChain {α : Type*} [PartialOrder α] (s : Finset α)
    (hs : s.Nonempty) (hchain : IsChain (· ≤ ·) (s : Set α)) :
    ∃ a ∈ s, ∀ b ∈ s, b ≤ a := by
  classical
  obtain ⟨a, hmax⟩ := s.exists_maximal hs
  refine ⟨a, hmax.prop, fun b hb => ?_⟩
  rcases hchain.total hb hmax.prop with hba | hab
  · exact hba
  · exact hmax.le_of_ge hb hab

/-- A face is nonempty, so the reciprocal of its cardinality is positive. -/
private theorem inv_card_pos (K : AbstractSimplicialComplex ι) (σ : Face K) :
    0 < (σ.1.card : ℝ)⁻¹ := by
  have : 0 < σ.1.card := Finset.card_pos.mpr (K.isRelLowerSet_faces.prop_of_mem σ.2)
  positivity

/-- The greatest face of a nonnegative chain-supported combination is exactly the coordinate
support of its image under the barycentric-subdivision linear map. -/
private theorem support_barycentricSubdivisionLinearMap_eq_greatest
    (K : AbstractSimplicialComplex ι) {a : Face K →₀ ℝ} (ha : ∀ σ, 0 ≤ a σ)
    {σ : Face K} (hσ : σ ∈ a.support) (hmax : ∀ τ ∈ a.support, τ ≤ σ) :
    (barycentricSubdivisionLinearMap K a).support = σ.1 := by
  ext v
  simp only [Finsupp.mem_support_iff]
  constructor
  · intro hv
    by_contra hvσ
    apply hv
    rw [barycentricSubdivisionLinearMap_apply]
    apply Finset.sum_eq_zero
    intro τ hτ
    have hvτ : v ∉ τ.1 := fun h => hvσ (hmax τ hτ h)
    simp [hvτ]
  · intro hvσ
    have hcard : 0 < (σ.1.card : ℝ)⁻¹ := inv_card_pos K σ
    have hapos : 0 < a σ := lt_of_le_of_ne (ha σ) (Finsupp.mem_support_iff.mp hσ).symm
    apply ne_of_gt
    rw [barycentricSubdivisionLinearMap_apply]
    apply Finset.sum_pos'
    · intro τ hτ
      exact mul_nonneg (ha τ) (by positivity)
    · exact ⟨σ, hσ, by simp [hvσ, hapos, hcard]⟩

/-- A nonzero nonnegative combination supported on a chain of faces has nonzero image. -/
private theorem barycentricSubdivisionLinearMap_ne_zero (K : AbstractSimplicialComplex ι)
    {a : Face K →₀ ℝ} (ha : ∀ σ, 0 ≤ a σ)
    (hchain : IsChain (· ≤ ·) (a.support : Set (Face K))) (ha0 : a ≠ 0) :
    barycentricSubdivisionLinearMap K a ≠ 0 := by
  obtain ⟨σ, hσ, hσmax⟩ := exists_greatest_of_isChain a.support
    (Finsupp.support_nonempty_iff.mpr ha0) hchain
  intro hzero
  have hne := K.isRelLowerSet_faces.prop_of_mem σ.2
  rw [← support_barycentricSubdivisionLinearMap_eq_greatest K ha hσ hσmax, hzero,
    Finsupp.support_zero] at hne
  simp at hne

private theorem exists_mem_greatest_not_mem_of_ne_face (K : AbstractSimplicialComplex ι)
    {a : Face K →₀ ℝ} (hchain : IsChain (· ≤ ·) (a.support : Set (Face K)))
    {σ : Face K} (hmax : ∀ τ ∈ a.support, τ ≤ σ) :
    ∃ v ∈ σ.1, ∀ τ ∈ a.support, v ∈ τ.1 → τ = σ := by
  by_cases herase : (a.support.erase σ).Nonempty
  · obtain ⟨τ, hτerase, hτmax⟩ := exists_greatest_of_isChain (a.support.erase σ) herase
      (hchain.mono (by simp))
    have hτa : τ ∈ a.support := Finset.mem_of_mem_erase hτerase
    have hτσ : τ.1 ⊂ σ.1 := (Finset.ssubset_iff_subset_ne).2
      ⟨hmax τ hτa, fun h => Finset.ne_of_mem_erase hτerase (Subtype.ext h)⟩
    obtain ⟨v, hvσ, hvτ⟩ := Finset.exists_of_ssubset hτσ
    refine ⟨v, hvσ, fun ρ hρa hvρ => ?_⟩
    by_contra hρσ
    have hρerase : ρ ∈ a.support.erase σ := Finset.mem_erase.2 ⟨hρσ, hρa⟩
    exact hvτ (hτmax ρ hρerase hvρ)
  · obtain ⟨v, hvσ⟩ := K.isRelLowerSet_faces.prop_of_mem σ.2
    refine ⟨v, hvσ, fun τ hτ _ => ?_⟩
    by_contra hτσ
    exact herase ⟨τ, Finset.mem_erase.2 ⟨hτσ, hτ⟩⟩

private theorem barycentricSubdivisionLinearMap_apply_eq_of_exposed
    (K : AbstractSimplicialComplex ι) {a : Face K →₀ ℝ} {σ : Face K} {v : ι}
    (hσ : σ ∈ a.support) (hvσ : v ∈ σ.1)
    (hv : ∀ τ ∈ a.support, v ∈ τ.1 → τ = σ) :
    barycentricSubdivisionLinearMap K a v = a σ * (σ.1.card : ℝ)⁻¹ := by
  rw [barycentricSubdivisionLinearMap_apply]
  rw [Finset.sum_eq_single σ]
  · simp [hvσ]
  · intro τ hτ hτσ
    have hvτ : v ∉ τ.1 := fun h => hτσ (hv τ hτ h)
    simp [hvτ]
  · exact fun h => (h hσ).elim

private theorem barycentricSubdivisionLinearMap_injective_of_nonneg_of_isChain
    (K : AbstractSimplicialComplex ι) (a b : Face K →₀ ℝ)
    (ha : ∀ σ, 0 ≤ a σ) (hb : ∀ σ, 0 ≤ b σ)
    (hca : IsChain (· ≤ ·) (a.support : Set (Face K)))
    (hcb : IsChain (· ≤ ·) (b.support : Set (Face K)))
    (hab : barycentricSubdivisionLinearMap K a = barycentricSubdivisionLinearMap K b) : a = b := by
  induction hmeasure : a.support.card + b.support.card using Nat.strong_induction_on
    generalizing a b with
  | h n ih =>
      -- A nonzero nonnegative combination has nonzero image, so the zero cases agree.
      by_cases ha0 : a = 0
      · subst a
        by_cases hb0 : b = 0
        · exact hb0.symm
        · exact absurd (by simpa using hab.symm)
            (barycentricSubdivisionLinearMap_ne_zero K hb hcb hb0)
      · by_cases hb0 : b = 0
        · subst b
          exact absurd (by simpa using hab)
            (barycentricSubdivisionLinearMap_ne_zero K ha hca ha0)
        · obtain ⟨σ, hσa, hσmaxa⟩ := exists_greatest_of_isChain a.support
            (Finsupp.support_nonempty_iff.mpr ha0) hca
          obtain ⟨τ, hτb, hτmaxb⟩ := exists_greatest_of_isChain b.support
            (Finsupp.support_nonempty_iff.mpr hb0) hcb
          -- The common image support identifies the greatest face in the two chains.
          have hsuppa := support_barycentricSubdivisionLinearMap_eq_greatest K ha hσa hσmaxa
          have hsuppb := support_barycentricSubdivisionLinearMap_eq_greatest K hb hτb hτmaxb
          have hστ : σ = τ := by
            apply Subtype.ext
            rw [← hsuppa, hab, hsuppb]
          subst τ
          obtain ⟨v, hvσ, hva⟩ :=
            exists_mem_greatest_not_mem_of_ne_face K hca hσmaxa
          obtain ⟨w, hwσ, hwb⟩ :=
            exists_mem_greatest_not_mem_of_ne_face K hcb hτmaxb
          have hcard : 0 < (σ.1.card : ℝ)⁻¹ := inv_card_pos K σ
          have habσ : a σ = b σ := by
            -- Evaluate at an exposed vertex for each chain to compare the greatest coefficients
            -- in both directions.
            have hab_le : b σ * (σ.1.card : ℝ)⁻¹ ≤ a σ * (σ.1.card : ℝ)⁻¹ := by
              rw [← barycentricSubdivisionLinearMap_apply_eq_of_exposed K hσa hvσ hva, hab]
              rw [barycentricSubdivisionLinearMap_apply]
              have hsum := Finset.single_le_sum (s := b.support)
                (f := fun ρ => b ρ * if v ∈ ρ.1 then (ρ.1.card : ℝ)⁻¹ else 0)
                (fun ρ _ => mul_nonneg (hb ρ) (by positivity)) hτb
              simpa [hvσ] using hsum
            have hba_le : a σ * (σ.1.card : ℝ)⁻¹ ≤ b σ * (σ.1.card : ℝ)⁻¹ := by
              rw [← barycentricSubdivisionLinearMap_apply_eq_of_exposed K hτb hwσ hwb, ← hab]
              rw [barycentricSubdivisionLinearMap_apply]
              have hsum := Finset.single_le_sum (s := a.support)
                (f := fun ρ => a ρ * if w ∈ ρ.1 then (ρ.1.card : ℝ)⁻¹ else 0)
                (fun ρ _ => mul_nonneg (ha ρ) (by positivity)) hσa
              simpa [hwσ] using hsum
            nlinarith
          -- Erase the common greatest term and apply the strict induction hypothesis.
          have hmapErase : barycentricSubdivisionLinearMap K (a.erase σ) =
              barycentricSubdivisionLinearMap K (b.erase σ) := by
            rw [Finsupp.erase_eq_sub_single, Finsupp.erase_eq_sub_single, map_sub, map_sub,
              hab, habσ]
          have hcardErase : (a.erase σ).support.card + (b.erase σ).support.card < n := by
            have hcaPos : 0 < a.support.card := Finset.card_pos.mpr
              (Finsupp.support_nonempty_iff.mpr ha0)
            have hcbPos : 0 < b.support.card := Finset.card_pos.mpr
              (Finsupp.support_nonempty_iff.mpr hb0)
            rw [Finsupp.support_erase, Finsupp.support_erase, Finset.card_erase_of_mem hσa,
              Finset.card_erase_of_mem hτb, ← hmeasure]
            omega
          have herase := ih _ hcardErase (a.erase σ) (b.erase σ)
            (fun ρ => by by_cases h : ρ = σ <;> simp [h, ha ρ])
            (fun ρ => by by_cases h : ρ = σ <;> simp [h, hb ρ])
            (hca.mono (by simp)) (hcb.mono (by simp)) hmapErase rfl
          rw [← Finsupp.single_add_erase σ a, ← Finsupp.single_add_erase σ b, habσ, herase]

/-- The canonical map from the realization of the barycentric subdivision to the realization of
the original complex is injective. -/
theorem barycentricSubdivisionRealizationMap_injective (K : AbstractSimplicialComplex ι) :
    Function.Injective (barycentricSubdivisionRealizationMap K) := by
  intro x y hxy
  apply Subtype.ext
  apply barycentricSubdivisionLinearMap_injective_of_nonneg_of_isChain K x.1 y.1
  · exact Realization.nonneg _ x
  · exact Realization.nonneg _ y
  · exact (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp
      (support_mem _ x)).2
  · exact (TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff.mp
      (support_mem _ y)).2
  · simpa only [barycentricSubdivisionRealizationMap_val] using congrArg Subtype.val hxy

/-- The canonical map from the realization of the barycentric subdivision to the realization of
the original complex is bijective. -/
theorem barycentricSubdivisionRealizationMap_bijective (K : AbstractSimplicialComplex ι) :
    Function.Bijective (barycentricSubdivisionRealizationMap K) :=
  ⟨barycentricSubdivisionRealizationMap_injective K,
    barycentricSubdivisionRealizationMap_surjective K⟩

end AbstractSimplicialComplex
