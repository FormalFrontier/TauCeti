/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Presentation
public import TauCeti.RingTheory.Huber.Restricted.Laurent
public import TauCeti.RingTheory.Huber.StronglyNoetherian

/-!
# Flatness of the Laurent quotient

`A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` is a flat `A⟨T/s⟩`-module.

Over a complete noetherian Tate ring `B`, the quotient `B⟨X⟩ ⧸ (f - X)` is flat over `B`
(Wedhorn, Lemma 8.31(2)). Taking `B = A⟨T/s⟩` and `f = t/s` gives the flatness of the Laurent
quotient of a numerator enlargement, which is the elementary case that Proposition 8.30 reduces a
general restriction map to.

## Main results

* `TauCeti.Huber.PairOfDefinition.flat_quotient_laurentRelationIdeal` : flatness over a base that
  is a noetherian Tate ring.
* `TauCeti.Huber.PairOfDefinition.flat_quotient_laurentRelationIdeal_of_isStronglyNoetherian` :
  flatness for a topologically nilpotent denominator over a strongly noetherian base, the form in
  which the hypotheses are met in practice.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Lemma 8.31 and
  Proposition 8.30.
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

/-- **The Laurent quotient is flat over `A⟨T/s⟩`**: `A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` is a flat
`A⟨T/s⟩`-module.

This is Wedhorn's Lemma 8.31(2) over the base `A⟨T/s⟩`, whose remaining standing hypotheses —
completeness, separation, non-archimedeanness and countable generation of the uniformity — hold
of `A⟨T/s⟩` unconditionally. -/
theorem flat_quotient_laurentRelationIdeal
    (hTate : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsTateRing (UniformSpace.Completion S))
    (hnoeth : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsNoetherianRing (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Module.Flat (UniformSpace.Completion S)
      (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S)))
        isWeightFamily_one_weight ⧸ laurentRelationIdeal P T s t S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have _ := hTate
  have _ := hnoeth
  have _ : (𝓤 (UniformSpace.Completion S)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  -- the comparison of the two rings, as an equivalence of `A⟨T/s⟩`-algebras
  let e := AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr
    (weightedRestrictedSubring_one_weight (k := 1) (A := UniformSpace.Completion S)))
    (fun x ↦ subringCongr_one_weight_weightedC x)
  -- it carries the relation ideal to the ideal of Lemma 8.31
  have hmap : Ideal.span {algebraMap (UniformSpace.Completion S)
        (restrictedMvPowerSeriesSubring 1 (UniformSpace.Completion S))
        ((divBy t s : S) : UniformSpace.Completion S) - restrictedX 0}
      = (laurentRelationIdeal P T s t S hden).map (RingEquiv.subringCongr
        (weightedRestrictedSubring_one_weight (k := 1)
          (A := UniformSpace.Completion S)) : _ →+* _) := by
    rw [laurentRelationIdeal_def, Ideal.map_span, Set.image_singleton, map_sub]
    simp only [Fin.isValue, RingHom.coe_coe, subringCongr_one_weight_weightedC,
      subringCongr_one_weight_weightedX]
  have _ := flat_quotient_algebraMap_sub_restrictedX (UniformSpace.Completion S)
    ((divBy t s : S) : UniformSpace.Completion S)
  exact Module.Flat.of_linearEquiv
    (Ideal.quotientEquivAlg _ _ e hmap).toLinearEquiv

/-- **The Laurent quotient is flat over `A⟨T/s⟩`**, for a topologically nilpotent denominator over
a strongly noetherian base.

A topologically nilpotent `s` makes `A⟨T/s⟩` a Tate ring, and a strongly noetherian `A⟨T/s⟩` is in
particular noetherian, so this is
`TauCeti.Huber.PairOfDefinition.flat_quotient_laurentRelationIdeal` with its two hypotheses
discharged. -/
theorem flat_quotient_laurentRelationIdeal_of_isStronglyNoetherian
    (hnil : IsTopologicallyNilpotent s)
    (hSN : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    Module.Flat (UniformSpace.Completion S)
      (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set (UniformSpace.Completion S)))
        isWeightFamily_one_weight ⧸ laurentRelationIdeal P T s t S hden) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have _ := hSN
  exact flat_quotient_laurentRelationIdeal P T s t S hden
    (isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s S hden hnil)
    (isNoetherianRing_of_isStronglyNoetherian
      (by rw [IsUniformAddGroup.rightUniformSpace_eq]; infer_instance))

end PairOfDefinition

end TauCeti.Huber

end
