/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Presentation

import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Remark 7.55: the Laurent quotient *is* `A⟨T'/s⟩`

`TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Presentation` constructs the two maps
between the Laurent quotient `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` and the enlarged rational localisation
`A⟨T'/s⟩`. This file proves them mutually inverse, so that Wedhorn's Remark 7.55 is available as
an isomorphism of topological rings.

The identification holds under the same `hsplit` the second map needs — `T'` adjoins no numerator
beyond `t` — together with closedness of the relation ideal. For a general enlargement no
identification is expected, since `T'` may adjoin other numerators.

A consumer transports a statement about one side to the other: Proposition 8.30 uses it to carry
flatness of the Laurent quotient over `A⟨T/s⟩` across to `A⟨T'/s⟩`.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv` : the identification itself.

## Main results

* `TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom`
  and `TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom`
  : the two composites, public in their own right.
* `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv_coe` and its `symm`, `apply` and
  `symm_apply` companions : the equivalence and its inverse are the two named maps.
* `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingEquiv` and its `symm` : the
  identification is one of *topological* rings.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.55.
-/

public section

namespace TauCeti.Huber

open TauCeti.Localization

open scoped Uniformity

namespace PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s t : A)
  (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

section OneStep

variable (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

-- The structure map of the Laurent quotient, `a ↦ [a]` on constants: `weightedC` followed by the
-- quotient map. The two composite identities below are both proved by comparing against it.
private noncomputable abbrev laurentStructureHom :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    UniformSpace.Completion S →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)).comp
    (weightedC _ isWeightFamily_one_weight)

-- The fraction `t/s` downstairs goes to the class of the variable. This is where the Laurent
-- relation is used, and it needs nothing of the target beyond the ring structure: expand both
-- fractions, move the inverse across with `IsUnit.unit_inv_map`, and read off the relation.
private theorem apply_divBy_eq_quotientMk_weightedX :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
          laurentRelationIdeal P T s t S hden),
      g.comp (toCompletionLoc P T' s S' hden')
          = (laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden) →
        g ((divBy t s : S') : UniformSpace.Completion S')
          = Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
            (weightedX _ isWeightFamily_one_weight 0) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  intro g hge
  rw [map_divBy_of_comp_toCompletionLoc_eq P T s S hden T' S' hden' t g _ hge]
  exact laurentRelationIdeal_quotientMk_weightedC P T s t S hden

-- Agreement on the image of `A` propagates to all of `A⟨T/s⟩`: two continuous ring homomorphisms
-- out of a completion that agree after the structure map are equal.
private theorem comp_restrictionRingHomOfSubset_eq (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ g : UniformSpace.Completion S' →+* (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
          laurentRelationIdeal P T s t S hden), Continuous g →
      g.comp (toCompletionLoc P T' s S' hden')
          = (laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden) →
        g.comp (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
          = laurentStructureHom P T s t S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have _ : T1Space (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    (Ideal.Quotient.t1Space_iff _).mpr hcl
  intro g hgc hge
  exact (eq_comp_of_comp_toCompletionLoc_eq P T s S hden (toCompletionLoc P T' s S' hden')
    ((laurentStructureHom P T s t S hden).comp (toCompletionLoc P T s S hden))
    (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
    (continuous_restrictionRingHomOfSubset P T s S hden T' S' hden' hTT')
    (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S hden T' S' hden' hTT') g hgc hge
    (laurentStructureHom P T s t S hden)
    (continuous_quotient_mk'.comp (continuous_weightedC isWeightFamily_one_weight)) rfl).symm

/-- **The two maps of Remark 7.55 compose to the identity of `A⟨T'/s⟩`**: going into the Laurent
quotient and back out again is the identity of the enlarged rational localisation. -/
@[simp]
theorem laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht).comp
        (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl)
      = RingHom.id (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have hψc := continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
  have hψC :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedC P T s t S hden T' S' hden' hTT' ht
  have hgc := continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hge := laurentQuotientRingHom_comp_toCompletionLoc P T s t S hden T' S' hden' hsplit hcl
  refine eq_id_of_comp_toCompletionLoc_eq_self P T' s S' hden' _ (hψc.comp hgc) ?_
  rw [RingHom.comp_assoc, hge]
  exact RingHom.ext fun a ↦ (hψC _).trans <| DFunLike.congr_fun
    (restrictionRingHomOfSubset_comp_toCompletionLoc P T s S hden T' S' hden' hTT') a

/-- **The two maps of Remark 7.55 compose to the identity of the Laurent quotient**: going out of
`A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` and back in again is its identity. -/
@[simp]
theorem laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl).comp
        (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht)
      = RingHom.id (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have _ := IsHuberRing.quotient (laurentRelationIdeal P T s t S hden)
  have _ : T1Space (_ ⧸ laurentRelationIdeal P T s t S hden) :=
    (Ideal.Quotient.t1Space_iff _).mpr hcl
  have hψc := continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht
  have hψC :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedC P T s t S hden T' S' hden' hTT' ht
  have hψX :=
    laurentQuotientRestrictionRingHom_quotientMk_weightedX P T s t S hden T' S' hden' hTT' ht
  set g := laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hgc := continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl
  have hge := laurentQuotientRingHom_comp_toCompletionLoc P T s t S hden T' S' hden' hsplit hcl
  refine Ideal.Quotient.ringHom_ext <|
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      ((hgc.comp hψc).comp continuous_quot_mk) continuous_quot_mk ?_ ?_
  · intro a
    exact (congrArg g (hψC a)).trans <| DFunLike.congr_fun
      (comp_restrictionRingHomOfSubset_eq P T s t S hden T' S' hden' hTT' hcl _ hgc hge) a
  · intro i
    rw [Subsingleton.elim i 0]
    exact (congrArg g (hψX 0)).trans
      (apply_divBy_eq_quotientMk_weightedX P T s t S hden T' S' hden' _ hge)

/-- **Wedhorn's Remark 7.55**: when the numerators of `T'` are those of `T` together with `t`, the
Laurent quotient *is* `A⟨T'/s⟩`,

```text
A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)  ≃  A⟨T'/s⟩
```

the two maps already constructed being mutually inverse. This is the identification Proposition
8.30 consumes: it turns a statement about the Laurent quotient, such as its flatness over
`A⟨T/s⟩`, into the same statement about `A⟨T'/s⟩`.

Use `TauCeti.Huber.PairOfDefinition.continuous_laurentQuotientRingEquiv` and its `symm` form for
continuity, and the `@[simp]` lemmas below to compute: the equivalence is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRestrictionRingHom` and its inverse is
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`. -/
noncomputable def laurentQuotientRingEquiv (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) ≃+* UniformSpace.Completion S' :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  letI := isHuberRing_locUniformSpace P T s S hden
  letI := locUniformSpace P T' s S' hden'
  letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
  letI := isTopologicalRing_locUniformSpace P T' s S' hden'
  letI := isHuberRing_locUniformSpace P T' s S' hden'
  RingEquiv.ofRingHom (laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht)
    (laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl)
    (laurentQuotientRestrictionRingHom_comp_laurentQuotientRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)
    (laurentQuotientRingHom_comp_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden'
      hTT' ht hsplit hcl)

/-- **The identification is `laurentQuotientRestrictionRingHom`**, as a ring homomorphism: it
packages that map together with the inverse supplied by
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingHom`, rather than introducing a new one. -/
@[simp]
theorem laurentQuotientRingEquiv_coe (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ((laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl :
        (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) ≃+* UniformSpace.Completion S') :
        (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden) →+* UniformSpace.Completion S')
      = laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht := by
  simp only [laurentQuotientRingEquiv, RingEquiv.coe_ringHom_ofRingHom]
/-- The pointwise form of `TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv_coe`. -/
@[simp]
theorem laurentQuotientRingEquiv_apply (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ x, laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl x
      = laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht x :=
  fun x ↦ DFunLike.congr_fun
    (laurentQuotientRingEquiv_coe P T s t S hden T' S' hden' hTT' ht hsplit hcl) x


/-- **The inverse of the identification is `laurentQuotientRingHom`**, as a ring homomorphism. -/
@[simp]
theorem laurentQuotientRingEquiv_symm_coe (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    (((laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm :
        UniformSpace.Completion S' ≃+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden)) :
        UniformSpace.Completion S' →+* (weightedRestrictedSubring
      (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight ⧸
        laurentRelationIdeal P T s t S hden))
      = laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl := by
  simp only [laurentQuotientRingEquiv, RingEquiv.ofRingHom_symm,
    RingEquiv.coe_ringHom_ofRingHom]
/-- The pointwise form of
`TauCeti.Huber.PairOfDefinition.laurentQuotientRingEquiv_symm_coe`. -/
@[simp]
theorem laurentQuotientRingEquiv_symm_apply (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    ∀ x, (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm x
      = laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl x :=
  fun x ↦ DFunLike.congr_fun
    (laurentQuotientRingEquiv_symm_coe P T s t S hden T' S' hden' hTT' ht hsplit hcl) x


/-- The identification is continuous. -/
theorem continuous_laurentQuotientRingEquiv (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl) := by
  simpa only [funext (laurentQuotientRingEquiv_apply P T s t S hden T' S' hden' hTT' ht hsplit hcl)]
    using continuous_laurentQuotientRestrictionRingHom P T s t S hden T' S' hden' hTT' ht

/-- The inverse of the identification is continuous, so it is a homeomorphism. -/
theorem continuous_laurentQuotientRingEquiv_symm (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hcl : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsClosed (laurentRelationIdeal P T s t S hden : Set (weightedRestrictedSubring
        (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S))) isWeightFamily_one_weight))) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    Continuous (laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl).symm := by
  simpa only
    [funext (laurentQuotientRingEquiv_symm_apply P T s t S hden T' S' hden' hTT' ht hsplit hcl)]
    using continuous_laurentQuotientRingHom P T s t S hden T' S' hden' hsplit hcl

end OneStep

end PairOfDefinition

end TauCeti.Huber

end
