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
# Flatness of the Laurent quotient, and of every numerator enlargement

`A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` is a flat `A⟨T/s⟩`-module, and so — this is **Wedhorn's Proposition 8.30**
at the ring level — is `A⟨T'/s⟩` for any enlargement `T ⊆ T'` of the numerators.

The argument runs in three steps. Over a complete noetherian Tate ring `B` the quotient
`B ⟨X⟩ ⧸ (f - X)` is flat over `B` (Wedhorn, Lemma 8.31(2)); with `B = A⟨T/s⟩` and `f = t/s` that
is the flatness of the Laurent quotient. Remark 7.55 identifies that quotient with `A⟨T'/s⟩`
whenever the numerators of `T'` are those of `T` together with `t`, which turns the first step
into flatness of the restriction map itself for a one-numerator enlargement. A general `T ⊆ T'` is
then reached by adjoining the elements of `T' \ T` one at a time, and flatness composes along the
tower.

## Main results

* `TauCeti.Huber.PairOfDefinition.flat_quotient_laurentRelationIdeal` : flatness over a base that
  is a noetherian Tate ring.
* `TauCeti.Huber.PairOfDefinition.flat_quotient_laurentRelationIdeal_of_isStronglyNoetherian` :
  flatness for a topologically nilpotent denominator over a strongly noetherian base, the form in
  which the hypotheses are met in practice.
* `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset` : **Proposition 8.30's
  elementary case** — the restriction map `A⟨T/s⟩ → A⟨T'/s⟩` is flat when `T'` adds the single
  numerator `t`; the `..._of_isStronglyNoetherian` variant takes the hypotheses in their usual
  form.
* `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_of_subset` : **Proposition 8.30**
  — the restriction map of an arbitrary enlargement `T ⊆ T'` is flat. Strong noetherianity is
  asked of every intermediate `A⟨U/s⟩`, since the elementary step needs it at its own base and it
  does not descend along an enlargement; see that theorem's docstring.

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
  (T' : Finset A) (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
  (hden' : HasDenominatorPower P T' s S') (hTT' : ∀ u ∈ T, u ∈ T')

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

/-- **Proposition 8.30, the elementary case**: the restriction map `A⟨T/s⟩ → A⟨T'/s⟩` of a
one-numerator enlargement is flat.

The Laurent quotient is flat over `A⟨T/s⟩`, and Remark 7.55 identifies it with `A⟨T'/s⟩`
compatibly with the two structure maps, so the flatness transports. -/
theorem flat_restrictionRingHomOfSubset (ht : t ∈ T') (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t)
    (hTate : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsTateRing (UniformSpace.Completion S))
    (hnoeth : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsNoetherianRing (UniformSpace.Completion S))
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
    letI := (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').toAlgebra
    Module.Flat (UniformSpace.Completion S) (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have hecomm : ∀ a, laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl
      (Ideal.Quotient.mk (laurentRelationIdeal P T s t S hden)
        (weightedC _ isWeightFamily_one_weight a))
      = restrictionRingHomOfSubset P T s S hden T' S' hden' hTT' a := fun a ↦ by
    rw [laurentQuotientRingEquiv_apply, laurentQuotientRestrictionRingHom_quotientMk_weightedC]
  set e := laurentQuotientRingEquiv P T s t S hden T' S' hden' hTT' ht hsplit hcl
  have _ := flat_quotient_laurentRelationIdeal P T s t S hden hTate hnoeth
  let _ := (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').toAlgebra
  -- the inverse identification is a map of `A⟨T/s⟩`-algebras, so flatness crosses it
  have hsymm : ∀ r, e.symm (algebraMap (UniformSpace.Completion S) _ r)
      = algebraMap (UniformSpace.Completion S) _ r := by
    intro r
    rw [RingHom.algebraMap_toAlgebra, ← hecomm, RingEquiv.symm_apply_apply]
    rfl
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofRingEquiv (f := e.symm) hsymm).toLinearEquiv

/-- **Proposition 8.30, the elementary case**, for a topologically nilpotent denominator over a
strongly noetherian base: the hypotheses of
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset` in the form they are met in. -/
theorem flat_restrictionRingHomOfSubset_of_isStronglyNoetherian (ht : t ∈ T')
    (hsplit : ∀ u ∈ T', u ∈ T ∨ u = t) (hnil : IsTopologicallyNilpotent s)
    (hSN : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := isHuberRing_locUniformSpace P T s S hden
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := isHuberRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    letI := isHuberRing_locUniformSpace P T' s S' hden'
    letI := (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').toAlgebra
    Module.Flat (UniformSpace.Completion S) (UniformSpace.Completion S') := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s S' hden'
  have _ := isHuberRing_locUniformSpace P T' s S' hden'
  have _ := hSN
  exact flat_restrictionRingHomOfSubset P T s t S hden T' S' hden' hTT' ht hsplit
    (isTateRing_completion_locTopology_of_isTopologicallyNilpotent P T s S hden hnil)
    (isNoetherianRing_of_isStronglyNoetherian
      (by rw [IsUniformAddGroup.rightUniformSpace_eq]; infer_instance))
    (isClosed_laurentRelationIdeal_of_isStronglyNoetherian P T s t S hden hnil hSN)

/-- **A chain of numerator sets is a tower of coordinate rings.** For `T ⊆ U ⊆ V` the restriction
map out of `A⟨T/s⟩` to `A⟨V/s⟩` factors through `A⟨U/s⟩` — that is
`TauCeti.Huber.PairOfDefinition.restrictionRingHomOfSubset_comp_restrictionRingHomOfSubset` — so
the three form a scalar tower. It is what lets flatness compose along a chain of enlargements. -/
theorem isScalarTower_restrictionRingHomOfSubset (U V : Finset A) (hTU : T ⊆ U) (hUV : U ⊆ V) :
    letI iT := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI iU := locUniformSpace P U s S (hden.mono hTU)
    letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
    letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
    letI iV := locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := isTopologicalRing_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := (restrictionRingHomOfSubset P T s S hden U S (hden.mono hTU) hTU).toAlgebra
    letI := (restrictionRingHomOfSubset P U s S (hden.mono hTU) V S
      (hden.mono (hTU.trans hUV)) hUV).toAlgebra
    letI := (restrictionRingHomOfSubset P T s S hden V S
      (hden.mono (hTU.trans hUV)) (hTU.trans hUV)).toAlgebra
    IsScalarTower (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iU)
      (@UniformSpace.Completion S iV) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P U s S (hden.mono hTU)
  have _ := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
  have _ := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
  let _ := locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  have _ := isUniformAddGroup_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  have _ := isTopologicalRing_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  let _ := (restrictionRingHomOfSubset P T s S hden U S (hden.mono hTU) hTU).toAlgebra
  let _ := (restrictionRingHomOfSubset P U s S (hden.mono hTU) V S
    (hden.mono (hTU.trans hUV)) hUV).toAlgebra
  let _ := (restrictionRingHomOfSubset P T s S hden V S
    (hden.mono (hTU.trans hUV)) (hTU.trans hUV)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      ← RingHom.comp_apply, restrictionRingHomOfSubset_comp_restrictionRingHomOfSubset P T s S
        hden U S (hden.mono hTU) hTU V S (hden.mono (hTU.trans hUV)) hUV]

/-- **Flatness composes along a chain of numerator sets.** For `T ⊆ U ⊆ V`, if `A⟨U/s⟩` is flat
over `A⟨T/s⟩` and `A⟨V/s⟩` is flat over `A⟨U/s⟩`, then `A⟨V/s⟩` is flat over `A⟨T/s⟩`. This is
`Module.Flat.trans` across the tower of
`TauCeti.Huber.PairOfDefinition.isScalarTower_restrictionRingHomOfSubset`; it is the composition
step of Proposition 8.30's induction, and it carries all of that argument's instance
bookkeeping. -/
theorem flat_restrictionRingHomOfSubset_trans (U V : Finset A) (hTU : T ⊆ U) (hUV : U ⊆ V)
    (h₁ : letI iT := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI iU := locUniformSpace P U s S (hden.mono hTU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
      letI := (restrictionRingHomOfSubset P T s S hden U S (hden.mono hTU) hTU).toAlgebra
      Module.Flat (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iU))
    (h₂ : letI iU := locUniformSpace P U s S (hden.mono hTU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
      letI iV := locUniformSpace P V s S (hden.mono (hTU.trans hUV))
      letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
      letI := isTopologicalRing_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
      letI := (restrictionRingHomOfSubset P U s S (hden.mono hTU) V S
        (hden.mono (hTU.trans hUV)) hUV).toAlgebra
      Module.Flat (@UniformSpace.Completion S iU) (@UniformSpace.Completion S iV)) :
    letI iT := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI iV := locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := isTopologicalRing_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
    letI := (restrictionRingHomOfSubset P T s S hden V S
      (hden.mono (hTU.trans hUV)) (hTU.trans hUV)).toAlgebra
    Module.Flat (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iV) := by
  let iT := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let iU := locUniformSpace P U s S (hden.mono hTU)
  have _ := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
  have _ := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
  let iV := locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  have _ := isUniformAddGroup_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  have _ := isTopologicalRing_locUniformSpace P V s S (hden.mono (hTU.trans hUV))
  let _ := (restrictionRingHomOfSubset P T s S hden U S (hden.mono hTU) hTU).toAlgebra
  let _ := (restrictionRingHomOfSubset P U s S (hden.mono hTU) V S
    (hden.mono (hTU.trans hUV)) hUV).toAlgebra
  let _ := (restrictionRingHomOfSubset P T s S hden V S
    (hden.mono (hTU.trans hUV)) (hTU.trans hUV)).toAlgebra
  have _ := h₁
  have _ := h₂
  have _ := isScalarTower_restrictionRingHomOfSubset P T s S hden U V hTU hUV
  exact Module.Flat.trans (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iU)
    (@UniformSpace.Completion S iV)

/-- **Proposition 8.30 at the ring level**: the restriction map `A⟨T/s⟩ → A⟨T'/s⟩` of an arbitrary
enlargement of the numerators is flat.

Any `T ⊆ T'` is reached from `T` by adjoining the elements of `T' \ T` one at a time, each step is
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_of_isStronglyNoetherian`, and
flatness composes. The intermediate presentations all live on the one localisation `S`, at the
uniformity their own numerator set determines; `TauCeti.Huber.HasDenominatorPower.mono` supplies
each of their standing hypotheses from the one at `T`.

Strong noetherianity is asked of every intermediate `A⟨U/s⟩`, not only of `A⟨T/s⟩`: the elementary
step needs it at its own base, and it does not descend along an enlargement. Wedhorn has it from
the standing hypothesis of his §8.2 — that rational localisations of a strongly noetherian ring
are again strongly noetherian — which is not formalised here. -/
theorem flat_restrictionRingHomOfSubset_of_subset (hnil : IsTopologicallyNilpotent s)
    (hSN : ∀ (U : Finset A) (hU : T ⊆ U), U ⊆ T' →
      letI := locUniformSpace P U s S (hden.mono hU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hU)
      letI := isHuberRing_locUniformSpace P U s S (hden.mono hU)
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI iT := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI iT' := locUniformSpace P T' s S (hden.mono hTT')
    letI := isUniformAddGroup_locUniformSpace P T' s S (hden.mono hTT')
    letI := isTopologicalRing_locUniformSpace P T' s S (hden.mono hTT')
    letI := (restrictionRingHomOfSubset P T s S hden T' S (hden.mono hTT') hTT').toAlgebra
    Module.Flat (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iT') := by
  classical
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- every set reached from `T` by adjoining elements of `T' \ T` is flat over `A⟨T/s⟩`
  have key : ∀ (W V : Finset A), V = T ∪ W → W ⊆ T' \ T → ∀ hV : T ⊆ V,
      letI iT := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI iV := locUniformSpace P V s S (hden.mono hV)
      letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono hV)
      letI := isTopologicalRing_locUniformSpace P V s S (hden.mono hV)
      letI := (restrictionRingHomOfSubset P T s S hden V S (hden.mono hV) hV).toAlgebra
      Module.Flat (@UniformSpace.Completion S iT) (@UniformSpace.Completion S iV) := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      intro V hVdef _ hV
      rw [Finset.union_empty] at hVdef
      subst hVdef
      -- the restriction of a presentation to itself is the identity, so the algebra structure
      -- it induces is the canonical one and the goal is flatness of a ring over itself
      have hid := restrictionRingHomOfSubset_self P _ s S hden
      have halg : (restrictionRingHomOfSubset P _ s S hden _ S (hden.mono hV) hV).toAlgebra
          = Algebra.id (UniformSpace.Completion S) :=
        Algebra.algebra_ext _ _ fun r ↦ by
          rw [RingHom.algebraMap_toAlgebra, hid]
          rfl
      rw [halg]
      exact Module.Flat.self
    | @insert a W haW ih =>
      intro V hVdef hW hV
      rw [Finset.union_insert] at hVdef
      subst hVdef
      have hTU : T ⊆ T ∪ W := Finset.subset_union_left
      have hUV : T ∪ W ⊆ insert a (T ∪ W) := Finset.subset_insert _ _
      have hWsub : W ⊆ T' \ T := fun x hx ↦ hW (Finset.mem_insert_of_mem hx)
      -- the previous step, then the elementary step onto it, composed
      exact flat_restrictionRingHomOfSubset_trans P T s S hden (T ∪ W) (insert a (T ∪ W)) hTU hUV
        (ih (T ∪ W) rfl hWsub hTU)
        (flat_restrictionRingHomOfSubset_of_isStronglyNoetherian P (T ∪ W) s a S
          (hden.mono hTU) (insert a (T ∪ W)) S (hden.mono hV) hUV (Finset.mem_insert_self _ _)
          (fun u hu ↦ (Finset.mem_insert.mp hu).symm.imp id id) hnil
          (hSN (T ∪ W) hTU fun x hx ↦ (Finset.mem_union.mp hx).elim (hTT' x)
            fun h ↦ (Finset.mem_sdiff.mp (hWsub h)).1))
  exact key (T' \ T) T' (Finset.union_sdiff_of_subset hTT').symm le_rfl hTT'


end PairOfDefinition

end TauCeti.Huber

end
