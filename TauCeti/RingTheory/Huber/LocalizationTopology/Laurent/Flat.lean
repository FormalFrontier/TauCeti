/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Presentation
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.Huber.Restricted.Laurent
public import TauCeti.RingTheory.Huber.StronglyNoetherian

import TauCeti.RingTheory.Huber.LocalizationTopology.Laurent.Identification

/-!
# Flatness of the Laurent quotient, and of a numerator enlargement

`A⟨T/s⟩⟨X⟩ ⧸ (t/s - X)` is a flat `A⟨T/s⟩`-module over a complete noetherian Tate ring, and so —
the elementary case of **Wedhorn's Proposition 8.30** at the ring level — is `A⟨T'/s⟩` when `T'`
adjoins the single numerator `t` and the Laurent relation ideal is closed. The
`..._of_isStronglyNoetherian` variants supply closedness and Tate-ness from a topologically
nilpotent `s` over a strongly noetherian base, which is how the hypotheses are met in practice.

The enlargement `T ⊆ T'` is then reached one numerator at a time. That chain result carries the
hypotheses its induction needs, and only for a *proper* enlargement: `s` topologically nilpotent,
and `A⟨U/s⟩` strongly noetherian for every `U` with `T ⊆ U ⊂ T'`. It is therefore **not** Wedhorn's
Proposition 8.30, which assumes strong noetherianity of `A` alone; see *What this is not*.

The results stand in one line. The Laurent quotient's flatness is the base; the elementary case is
that statement transported along Remark 7.55's identification; the chain is the elementary case
iterated; and the identity enlargement — `flat_restrictionRingHomOfSubset_self`, which assumes
nothing — is both the chain's `T = T'` case and what carries its conclusion to an arbitrary
localisation of `T'`.

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
* `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_self` : the identity
  enlargement — two presentations with the same numerator set, on possibly different localisations,
  are compared by a flat map. This one is hypothesis-free.
* `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_of_forall_isStronglyNoetherian`
  : the chain form — the restriction map of an arbitrary enlargement `T ⊆ T'` is flat, **assuming
  `A⟨U/s⟩` strongly noetherian for every `U` with `T ⊆ U ⊂ T'`**. That family hypothesis is what
  separates this from Wedhorn's Proposition 8.30, which assumes it of `A` alone; see *What this is
  not*.

## What this is not

The chain result is **not** Wedhorn's Proposition 8.30 as he states it. His standing hypothesis is
that `A` is strongly noetherian; the hypothesis here is that `A⟨U/s⟩` is, for every `U` with
`T ⊆ U ⊂ T'`. What separates the two is the standing hypothesis of Wedhorn's §8.2 — that rational
localisations of a strongly noetherian ring are again strongly noetherian. The family hypothesis
is carried rather than derived from that, and the theorem is named for what it assumes.

The elementary case is unaffected: it needs strong noetherianity only at its own base, which is
where Lemma 8.31 needs it too.

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

`hsplit` says that `T'` is the numerators of `T` together with the single `t`; `hTate` and
`hnoeth` are Lemma 8.31's hypotheses on the base `A⟨T/s⟩`, and `hcl` asks the Laurent relation
ideal to be closed. The `..._of_isStronglyNoetherian` variant below takes them in the form they
are met in. -/
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
    (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').Flat := by
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
  -- the Laurent quotient is flat over `A⟨T/s⟩` and Remark 7.55 identifies it with `A⟨T'/s⟩`;
  -- the inverse identification is a map of `A⟨T/s⟩`-algebras, so the flatness crosses it
  have hsymm : ∀ r, e.symm (algebraMap (UniformSpace.Completion S) _ r)
      = algebraMap (UniformSpace.Completion S) _ r := by
    intro r
    rw [RingHom.algebraMap_toAlgebra, ← hecomm, RingEquiv.symm_apply_apply,
      ← Ideal.Quotient.mk_algebraMap,
      RingHom.algebraMap_toAlgebra (weightedC _ isWeightFamily_one_weight)]
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
    (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').Flat := by
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

/-- **Flatness composes along `T ⊆ U ⊆ V`**: if the restriction maps of `T ⊆ U` and of `U ⊆ V` are
flat then so is the one of `T ⊆ V`. The far end may be carried by a different localisation of `A`
from the first two. -/
private theorem flat_comp_restrictionRingHomOfSubset (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (U : Finset A) (hTU : T ⊆ U) (V : Finset A)
    (SV : Type*) [CommRing SV] [Algebra A SV] [IsLocalization.Away s SV]
    (hdenV : HasDenominatorPower P V s SV) (hUV : U ⊆ V)
    (h₁ : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      letI := locUniformSpace P U s S (hden.mono hTU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
      (restrictionRingHomOfSubset P T s S hden U S (hden.mono hTU) hTU).Flat)
    (h₂ : letI := locUniformSpace P U s S (hden.mono hTU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
      letI := locUniformSpace P V s SV hdenV
      letI := isUniformAddGroup_locUniformSpace P V s SV hdenV
      letI := isTopologicalRing_locUniformSpace P V s SV hdenV
      (restrictionRingHomOfSubset P U s S (hden.mono hTU) V SV hdenV hUV).Flat) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P V s SV hdenV
    letI := isUniformAddGroup_locUniformSpace P V s SV hdenV
    letI := isTopologicalRing_locUniformSpace P V s SV hdenV
    (restrictionRingHomOfSubset P T s S hden V SV hdenV (hTU.trans hUV)).Flat := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P U s S (hden.mono hTU)
  have _ := isUniformAddGroup_locUniformSpace P U s S (hden.mono hTU)
  have _ := isTopologicalRing_locUniformSpace P U s S (hden.mono hTU)
  let _ := locUniformSpace P V s SV hdenV
  have _ := isUniformAddGroup_locUniformSpace P V s SV hdenV
  have _ := isTopologicalRing_locUniformSpace P V s SV hdenV
  -- `RingHom.Flat.comp` then the composition law; this is a separate declaration only because
  -- the instance chain for three presentations does not fit inside the induction step
  have hcomp := RingHom.Flat.comp h₁ h₂
  rwa [restrictionRingHomOfSubset_comp_restrictionRingHomOfSubset P T s S hden U S
    (hden.mono hTU) hTU V SV hdenV hUV] at hcomp

/-- **Changing the localisation that carries a presentation is flat.** Two presentations with the
same numerator set are compared by restriction maps that are mutually inverse, so each is bijective.

This is the identity enlargement, and it assumes nothing: no nilpotence, no noetherianity. It is
what lets the chain below end at an arbitrary localisation of `T'` rather than the one its
induction runs on, and it is the `T = T'` case of that chain. -/
theorem flat_restrictionRingHomOfSubset_self (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s S']
    (hden' : HasDenominatorPower P T s S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T s S' hden'
    letI := isTopologicalRing_locUniformSpace P T s S' hden'
    (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu).Flat := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T s S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T s S' hden'
  have _ := isTopologicalRing_locUniformSpace P T s S' hden'
  have h : (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu).comp
      (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu) = RingHom.id _ := by
    simp
  have h' : (restrictionRingHomOfSubset P T s S hden T S' hden' fun _ hu ↦ hu).comp
      (restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu) = RingHom.id _ := by
    simp
  refine RingHom.Flat.of_bijective (Function.bijective_iff_has_inverse.mpr
    ⟨restrictionRingHomOfSubset P T s S' hden' T S hden fun _ hu ↦ hu, fun x ↦ ?_, fun x ↦ ?_⟩)
  · simpa only [RingHom.comp_apply, RingHom.id_apply] using DFunLike.congr_fun h x
  · simpa only [RingHom.comp_apply, RingHom.id_apply] using DFunLike.congr_fun h' x

-- The induction behind Proposition 8.30: for every `W ⊆ T' \ T`, the restriction map of
-- `T ⊆ T ∪ W` is flat.

private theorem flat_restrictionRingHomOfSubset_union [DecidableEq A]
    (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) (T' : Finset A) (hTT' : T ⊆ T')
    (hnil : T ⊂ T' → IsTopologicallyNilpotent s)
    (hSN : ∀ (U : Finset A) (hU : T ⊆ U), U ⊂ T' →
      letI := locUniformSpace P U s S (hden.mono hU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hU)
      letI := isHuberRing_locUniformSpace P U s S (hden.mono hU)
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    ∀ (W V : Finset A), V = T ∪ W → W ⊆ T' \ T → ∀ hV : T ⊆ V,
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P V s S (hden.mono hV)
    letI := isUniformAddGroup_locUniformSpace P V s S (hden.mono hV)
    letI := isTopologicalRing_locUniformSpace P V s S (hden.mono hV)
    (restrictionRingHomOfSubset P T s S hden V S (hden.mono hV) hV).Flat := by
  classical
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- on `W`: the empty case is the self-restriction, the identity ring homomorphism, and each
  -- step composes the previous one with an elementary enlargement
  intro W
  induction W using Finset.induction_on with
  | empty =>
    intro V hVdef _ hV
    rw [Finset.union_empty] at hVdef
    subst hVdef
    -- the restriction of a presentation to itself is the identity ring homomorphism
    rw [restrictionRingHomOfSubset_self P _ s S hden]
    exact RingHom.Flat.id _
  | @insert a W haW ih =>
    intro V hVdef hW hV
    rw [Finset.union_insert] at hVdef
    subst hVdef
    have hTU : T ⊆ T ∪ W := Finset.subset_union_left
    have hUV : T ∪ W ⊆ insert a (T ∪ W) := Finset.subset_insert _ _
    have hWsub : W ⊆ T' \ T := fun x hx ↦ hW (Finset.mem_insert_of_mem hx)
    -- `a` is a numerator of `T'` outside `T ∪ W`, so that union is a *proper* subset of `T'`,
    -- which is all the strong-noetherianity hypothesis is asked of
    have ha := Finset.mem_sdiff.mp (hW (Finset.mem_insert_self a W))
    have hlt : T ∪ W ⊂ T' :=
      ⟨fun x hx ↦ (Finset.mem_union.mp hx).elim (@hTT' x)
        fun h ↦ (Finset.mem_sdiff.mp (hWsub h)).1,
        fun hall ↦ (Finset.mem_union.mp (hall ha.1)).elim ha.2 haW⟩
    -- the previous step, then the elementary step onto it; flat ring maps compose
    exact flat_comp_restrictionRingHomOfSubset P T s S hden (T ∪ W) hTU (insert a (T ∪ W)) S
      (hden.mono hV) hUV (ih (T ∪ W) rfl hWsub hTU)
      (flat_restrictionRingHomOfSubset_of_isStronglyNoetherian P (T ∪ W) s a S
        (hden.mono hTU) (insert a (T ∪ W)) S (hden.mono hV) hUV (Finset.mem_insert_self _ _)
        (fun u hu ↦ (Finset.mem_insert.mp hu).symm.imp id id)
        (hnil ⟨hTT', fun h ↦ ha.2 (h ha.1)⟩) (hSN (T ∪ W) hTU hlt))

/-- **The chain form of Proposition 8.30, with strong noetherianity assumed at every proper
intermediate presentation**: the restriction map `A⟨T/s⟩ → A⟨T'/s⟩` of an arbitrary enlargement is
flat.

**This is not Wedhorn's Proposition 8.30, and should not be cited as it.** He assumes strong
noetherianity of `A` alone; `hSN` here asks it of `A⟨U/s⟩` for every `U` with `T ⊆ U ⊂ T'`. What
separates the two is the standing hypothesis of his §8.2 — that rational localisations of a
strongly noetherian ring are again strongly noetherian — which `hSN` assumes case by case rather
than deriving.

The enlargement is arbitrary and so is the localisation `S'` carrying the target, matching
`TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset` and the rest of the restriction
API.

Both hypotheses are asked only of a *proper* enlargement, and for the same reason: the identity
enlargement is `TauCeti.Huber.PairOfDefinition.flat_restrictionRingHomOfSubset_self`, which assumes
nothing. Strong noetherianity is then asked at every `U` with `T ⊆ U ⊂ T'`, not only at `T`, because
the elementary step needs it at its own base and it does not descend along an enlargement. -/
theorem flat_restrictionRingHomOfSubset_of_forall_isStronglyNoetherian
    (hnil : T ⊂ T' → IsTopologicallyNilpotent s)
    (hSN : ∀ (U : Finset A) (hU : T ⊆ U), U ⊂ T' →
      letI := locUniformSpace P U s S (hden.mono hU)
      letI := isUniformAddGroup_locUniformSpace P U s S (hden.mono hU)
      letI := isTopologicalRing_locUniformSpace P U s S (hden.mono hU)
      letI := isHuberRing_locUniformSpace P U s S (hden.mono hU)
      IsStronglyNoetherian (UniformSpace.Completion S)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s S' hden'
    (restrictionRingHomOfSubset P T s S hden T' S' hden' hTT').Flat := by
  classical
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- the chain runs on the one localisation `S`, adjoining the elements of `T' \ T` one at a time
  -- with `HasDenominatorPower.mono` supplying each intermediate standing hypothesis; the result is
  -- then carried to `S'` by the bijective restriction map between two presentations of `T'`
  exact flat_comp_restrictionRingHomOfSubset P T s S hden T' hTT' T' S' hden' le_rfl
    (flat_restrictionRingHomOfSubset_union P T s S hden T' hTT' hnil hSN (T' \ T) T'
      (Finset.union_sdiff_of_subset hTT').symm le_rfl hTT')
    (flat_restrictionRingHomOfSubset_self P T' s S (hden.mono hTT') S' hden')


end PairOfDefinition

end TauCeti.Huber

end
