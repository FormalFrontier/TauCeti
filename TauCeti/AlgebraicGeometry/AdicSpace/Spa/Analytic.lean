/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Valuation.CofinalIdeal.Greatest
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion
public import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Analytic points and the analytic locus of `Spa(A, A⁺)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), Definition 7.39, Remark 7.40(3), and
Proposition 7.49.**

This file formalizes the analytic locus of the adic spectrum `Spa(A, A⁺)`.

## Main definitions

* `TauCeti.ValuationSpectrum.IsAnalyticPoint` : extends Wedhorn's analytic-point predicate from
  `Cont A` to `Spv A`; on continuous points it is Definition 7.39.
* `TauCeti.ValuationSpectrum.spaAnalytic` : **Wedhorn's `Spa(A, A⁺)ᵃ`**, the analytic locus of
  `Spa(A, A⁺)` as a `Set (Spv A)`.
* `TauCeti.ValuationSpectrum.spaAnalytic_def` : the analytic locus as a set intersection.

## Main results

* `TauCeti.ValuationSpectrum.isAnalyticPoint_of_isTateRing` : over a Tate ring every point of
  `Spv A` (and hence `Spa(A, A⁺)`) is analytic.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_spa_of_isTateRing` : **Wedhorn Remark 7.40(3)**,
  for a Tate ring `A`, the analytic locus is the entire adic spectrum.
* `TauCeti.ValuationSpectrum.isOpen_val_preimage_spaAnalytic` : the analytic locus is open.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_biUnion_rationalSubset` : generators of an ideal of
  definition give a finite rational cover of the analytic locus.
* `TauCeti.ValuationSpectrum.isTateRing_completion_locTopology_of_mem_generators` : the completed
  coordinate ring of each chart in that cover is Tate.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.39, Remark 7.40(3), and
  Proposition 7.49.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti TauCeti.Huber TauCeti.Huber.PairOfDefinition Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Analytic points of `Spv A`.** A point `v : Spv A` is *analytic* if its support `v.supp` is
not an open ideal of `A`. This extends Wedhorn's Definition 7.39 from `Cont A` to all of `Spv A`;
its restriction to continuous points is his predicate. -/
def IsAnalyticPoint (v : Spv A) : Prop :=
  ¬ IsOpen (v.supp : Set A)

/-- A point of `Spv A` is analytic exactly when its support is not open. -/
@[simp]
theorem isAnalyticPoint_def (v : Spv A) :
    IsAnalyticPoint v ↔ ¬ IsOpen (v.supp : Set A) :=
  Iff.rfl

/-- **Wedhorn's Analytic Locus `Spa(A, A⁺)ᵃ`**: the subset of `spa Aplus` consisting of analytic
points (Definition 7.39). -/
def spaAnalytic (Aplus : Subring A) : Set (Spv A) :=
  spa Aplus ∩ {v : Spv A | IsAnalyticPoint v}

/-- The analytic locus as a set intersection. -/
theorem spaAnalytic_def (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus ∩ {v : Spv A | IsAnalyticPoint v} := (rfl)

/-- Membership in the analytic locus: `v ∈ Spa(A, A⁺)ᵃ` iff `v ∈ Spa(A, A⁺)` and `v` is an
analytic point. -/
@[simp]
theorem mem_spaAnalytic_iff (Aplus : Subring A) (v : Spv A) :
    v ∈ spaAnalytic Aplus ↔ v ∈ spa Aplus ∧ IsAnalyticPoint v :=
  Iff.rfl

/-- The analytic locus is contained in the adic spectrum. -/
theorem spaAnalytic_subset_spa (Aplus : Subring A) :
    spaAnalytic Aplus ⊆ spa Aplus :=
  Set.inter_subset_left

/-- Enlarging the plus ring shrinks the analytic locus. -/
theorem spaAnalytic_antitone : Antitone (spaAnalytic (A := A)) := fun _ _ hle ↦
  Set.inter_subset_inter_left _ (spa_antitone hle)

section TopologicalRing

variable [IsTopologicalRing A]

/-- A point is analytic exactly when some element of the extended ideal of definition is outside
its support. This is Wedhorn Proposition 7.49(2)(i), expressed using Lemma 6.6. -/
theorem isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp
    (P : PairOfDefinition A) (v : Spv A) :
    IsAnalyticPoint v ↔ ∃ a ∈ P.extendedIdealOfDefinition, a ∉ v.supp := by
  rw [isAnalyticPoint_def, P.isOpen_iff_le_radical]
  have hsupp : v.supp.radical = v.supp :=
    (inferInstance : v.supp.IsPrime).isRadical.radical
  rw [hsupp]
  exact Set.not_subset

/-- The analytic locus is open in the adic spectrum. It is the union, over the extended ideal of
definition, of the loci on which an element does not vanish. -/
theorem isOpen_val_preimage_spaAnalytic (P : PairOfDefinition A) (Aplus : Subring A) :
    IsOpen (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) := by
  have hset : (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) =
      ⋃ a ∈ P.extendedIdealOfDefinition,
        Subtype.val ⁻¹' basicOpen a a := by
    ext v
    simp only [Set.mem_preimage, mem_spaAnalytic_iff, v.property, true_and, Set.mem_iUnion,
      mem_basicOpen_iff, exists_prop, ValuativeRel.vle_refl]
    rw [isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P]
    simp only [mem_supp_iff]
  rw [hset]
  exact isOpen_biUnion fun a _ ↦ (isOpen_basicOpen a a).preimage continuous_subtype_val

/-- A rational subset whose denominator belongs to the extended ideal of definition consists of
analytic points. -/
theorem rationalSubset_subset_spaAnalytic_of_mem_extendedIdealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) {s : A}
    (hs : s ∈ P.extendedIdealOfDefinition) :
    rationalSubset Aplus T s ⊆ spaAnalytic Aplus := by
  intro v hv
  have hmem := (mem_rationalSubset_iff Aplus T s v).mp hv
  refine (mem_spaAnalytic_iff Aplus v).mpr ⟨hmem.1, ?_⟩
  rw [isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P]
  exact ⟨s, hs, fun hsupp ↦ hmem.2.2 ((mem_supp_iff v s).mp hsupp)⟩

open scoped Classical in
/-- **A finite rational cover of the analytic locus.** If `T` generates the extended ideal of
definition, then the rational subsets `R(T/t)`, for `t ∈ T`, cover exactly the analytic locus.
This is the cover in Wedhorn Proposition 7.49(2). -/
theorem spaAnalytic_eq_biUnion_rationalSubset_of_span_eq_extendedIdealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A)
    (hspan : Ideal.span (T : Set A) = P.extendedIdealOfDefinition) :
    spaAnalytic Aplus =
      ⋃ t ∈ T, rationalSubset Aplus T t := by
  apply Set.Subset.antisymm
  · intro v hv
    have hvSpa := spaAnalytic_subset_spa Aplus hv
    obtain ⟨a, haI, haSupp⟩ :=
      (isAnalyticPoint_iff_exists_mem_extendedIdealOfDefinition_notMem_supp P v).mp
        ((mem_spaAnalytic_iff Aplus v).mp hv).2
    have ha0 : (MonoidWithZeroHom.ofClass v.valuation) a ≠ 0 := by
      intro ha0
      apply haSupp
      rw [v.supp_eq_valuation_supp, v.valuation.mem_supp_iff]
      exact ha0
    obtain ⟨t, htT, ht0, hmax⟩ :=
      Valuation.exists_mem_max_restrict_ne_zero (v := v.valuation)
        (I := P.extendedIdealOfDefinition) hspan rfl haI ha0
    refine Set.mem_iUnion₂_of_mem htT
      ((mem_rationalSubset_iff Aplus T t v).mpr ⟨hvSpa, ?_, ?_⟩)
    · intro u huT
      exact (valuation_le_iff v u t).mp (v.valuation.restrict_le_iff.mp (hmax u huT))
    · intro hzero
      exact ht0 (by simpa using (valuation_le_iff v t 0).mpr hzero)
  · refine Set.iUnion₂_subset fun t ht ↦ ?_
    apply rationalSubset_subset_spaAnalytic_of_mem_extendedIdealOfDefinition P Aplus
    rw [← hspan]
    exact Ideal.subset_span (Finset.mem_coe.mpr ht)

open scoped Classical in
/-- **The finite standard rational cover of the analytic locus.** If `G` generates an ideal of
definition, then the rational subsets `R(G/g)`, for `g ∈ G`, cover exactly the analytic locus.
This is the cover in Wedhorn Proposition 7.49(2). -/
theorem spaAnalytic_eq_biUnion_rationalSubset (P : PairOfDefinition A) (Aplus : Subring A)
    (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition) :
    spaAnalytic Aplus =
      ⋃ g ∈ G, rationalSubset Aplus
        (G.image ((↑) : P.ringOfDefinition → A)) (g : A) := by
  let T : Finset A := G.image ((↑) : P.ringOfDefinition → A)
  have hspan : Ideal.span (T : Set A) = P.extendedIdealOfDefinition :=
    P.span_image_eq_extendedIdealOfDefinition G hG
  rw [spaAnalytic_eq_biUnion_rationalSubset_of_span_eq_extendedIdealOfDefinition
    P Aplus T hspan]
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun t ht ↦ ?_
    have ht' : t ∈ G.image ((↑) : P.ringOfDefinition → A) := by
      simpa only [T] using ht
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht'
    exact Set.subset_iUnion₂_of_subset g hg Set.Subset.rfl
  · refine Set.iUnion₂_subset fun g hg ↦ ?_
    have hg' : (g : A) ∈ T := by
      simpa only [T] using Finset.mem_image.mpr ⟨g, hg, rfl⟩
    exact Set.subset_iUnion₂_of_subset (g : A) hg' Set.Subset.rfl

open scoped Classical in
/-- Every set in the standard analytic cover is a member of the rational basis: its numerator
ideal is the extended ideal of definition, hence open. -/
theorem val_preimage_rationalSubset_mem_spaRationalFamily_of_span_eq_idealOfDefinition
    (P : PairOfDefinition A) (Aplus : Subring A) (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition)
    (g : P.ringOfDefinition) :
    (Subtype.val ⁻¹' rationalSubset Aplus
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) : Set (spa Aplus)) ∈
        spaRationalFamily Aplus := by
  refine mem_spaRationalFamily_iff.mpr ⟨_, (g : A), ?_, rfl⟩
  rw [P.span_image_eq_extendedIdealOfDefinition G hG]
  exact (P.isOpen_iff_le_radical P.extendedIdealOfDefinition).mpr Ideal.le_radical

open scoped Classical in
/-- The completed coordinate ring of a chart in the standard analytic cover is a Tate ring.
The denominator belongs to the ideal of definition, hence is topologically nilpotent, and
localization makes it a unit. The localization's standing hypothesis is constructed from the
same generating set. -/
theorem isTateRing_completion_locTopology_of_mem_generators (P : PairOfDefinition A)
    (G : Finset P.ringOfDefinition)
    (hG : Ideal.span (G : Set P.ringOfDefinition) = P.idealOfDefinition)
    {g : P.ringOfDefinition} (hg : g ∈ G)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away (g : A) S] :
    let hden := hasDenominatorPower_of_idealOfDefinition_le_span P
      (G.image ((↑) : P.ringOfDefinition → A))
      (fun _ hx ↦ Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)) hG.ge g S
    letI := locUniformSpace P (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    letI := isUniformAddGroup_locUniformSpace P
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    letI := isTopologicalRing_locUniformSpace P
      (G.image ((↑) : P.ringOfDefinition → A)) (g : A) S hden
    IsTateRing (UniformSpace.Completion S) := by
  let hden := hasDenominatorPower_of_idealOfDefinition_le_span P
    (G.image ((↑) : P.ringOfDefinition → A))
    (fun _ hx ↦ Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx)) hG.ge g S
  exact isTateRing_completion_locTopology_of_isTopologicallyNilpotent P _ (g : A) S hden
    (P.isTopologicallyNilpotent_of_mem_idealOfDefinition
      (hG ▸ Ideal.subset_span (Finset.mem_coe.mpr hg)))

end TopologicalRing

section TateRing

variable [IsTopologicalRing A] [IsTateRing A]

/-- Over a Tate ring, every point of `Spv A` is analytic, extending Wedhorn Remark 7.40(3) beyond
continuous points. -/
theorem isAnalyticPoint_of_isTateRing (v : Spv A) : IsAnalyticPoint v :=
  fun h ↦ (instIsPrimeSupp v).ne_top (IsTateRing.eq_top_of_isOpen h)

/-- **Wedhorn Remark 7.40(3).** Over a Tate ring, the analytic locus is the entire adic
spectrum: `Spa (A, A⁺)ᵃ = Spa (A, A⁺)`. -/
@[simp]
theorem spaAnalytic_eq_spa_of_isTateRing (Aplus : Subring A) :
    spaAnalytic Aplus = spa Aplus := by
  ext v
  rw [mem_spaAnalytic_iff]
  exact and_iff_left (isAnalyticPoint_of_isTateRing v)

end TateRing

end TauCeti.ValuationSpectrum
