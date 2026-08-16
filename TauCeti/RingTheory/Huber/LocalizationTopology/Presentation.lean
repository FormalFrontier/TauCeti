/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Completion

/-!
# Comparing two presentations of a rational localisation

A rational subset `U = R(T/s)` of `Spa(A,A⁺)` has many presentations `(T,s)`, and the roadmap's
Layer 3.1 asks for the canonical isomorphism between the localisations they give, together with
compatibility for three presentations. **This file does not discharge that target.** It supplies
the conditional half: *given* comparison maps compatible with the structure maps from `A`, they
are mutually inverse and compose correctly.

What is missing is the passage from equality of two rational subsets to the existence of those
maps — the step Mathlib-side `rationalSubset_subset_rationalSubset_iff` stops short of, in its own
words "leaving the passage from those facts to invertibility of `s` and power-boundedness of `t/s`
in the coordinate ring as a separate, genuinely algebraic step" (Wedhorn §8.2). Until that exists,
nothing here can be instantiated at two presentations of one subset.

Everything here is uniqueness, in the sense that no comparison map is constructed: given maps in
both directions that commute with the structure maps, they are mutually inverse, and given three
presentations the comparison through the middle one is the direct comparison. That is exactly
what `TauCeti.Huber.PairOfDefinition.eq_id_of_comp_toCompletionLoc_eq_self` and
`…eq_comp_of_comp_toCompletionLoc_eq` say about maps out of `A⟨T/s⟩`, so each proof here is a
single application of one of them.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.presentationRingEquiv`: the canonical isomorphism
  `A⟨T/s⟩ ≃+* A⟨T'/s'⟩` assembled from compatible comparison maps in both directions.

## Main results

* `TauCeti.Huber.PairOfDefinition.comp_eq_id_of_comp_toCompletionLoc_eq`: compatible comparison
  maps in both directions compose to the identity.
* `TauCeti.Huber.PairOfDefinition.eq_comp_of_comp_toCompletionLoc_eq_three`: compatibility for
  three presentations — the comparison from the first to the third is the composite through the
  second.
* `TauCeti.Huber.PairOfDefinition.presentationRingEquiv_coe` and
  `…_symm_coe`: the characteristic equations — the isomorphism is the forward map it was
  built from, and its inverse is the backward one, so it introduces nothing new.
* `TauCeti.Huber.PairOfDefinition.continuous_presentationRingEquiv` and
  `…_coe_comp_toCompletionLoc`: it is continuous, and compatible with the structure maps
  from `A` — the property that determines it.

## What this file does not do

It does not show that two presentations *of the same rational subset* satisfy the compatibility
hypotheses. That is the remaining input: from `R(T/s) = R(T'/s')` one must deduce that `s'`
becomes a unit in `A⟨T/s⟩` and each `t'/s'` power-bounded there, which is where the universal
property is applied to produce the comparison maps this file consumes. Until that is available
the isomorphism is stated from the hypotheses rather than from equality of subsets.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.1–8.2.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-- **Compatible comparison maps between two presentations are mutually inverse.** If `g` carries
the structure map of `A⟨T/s⟩` to that of `A⟨T'/s'⟩` and `h` carries it back, then `h ∘ g` fixes
the structure map of `A⟨T/s⟩`, so it is the identity. -/
theorem comp_eq_id_of_comp_toCompletionLoc_eq [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S),
      Continuous g → Continuous h →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden →
      h.comp g = RingHom.id (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro g h hg hh hgc hhc
  refine eq_id_of_comp_toCompletionLoc_eq_self P T s S hden (h.comp g) (hh.comp hg) ?_
  rw [RingHom.comp_assoc, hgc, hhc]

/-- **The comparison isomorphism between two presentations.** Comparison maps in both directions
that are compatible with the structure maps from `A` assemble into a ring isomorphism, because
each composite fixes a structure map and is therefore the identity.

This is the *canonical* half of presentation independence: it says the comparison is an
isomorphism and is determined by compatibility, not that the compatibility hypotheses hold for
two presentations of the same rational subset. Supplying those is a separate step. -/
noncomputable def presentationRingEquiv [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S),
      Continuous g → Continuous h →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden →
      UniformSpace.Completion S ≃+* UniformSpace.Completion S' := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro g h hg hh hgc hhc
  exact RingEquiv.ofRingHom g h
    (comp_eq_id_of_comp_toCompletionLoc_eq P T' s' S' hden' T s S hden h g hh hg hhc hgc)
    (comp_eq_id_of_comp_toCompletionLoc_eq P T s S hden T' s' S' hden' g h hg hh hgc hhc)

/-- **Compatibility for three presentations.** A comparison map from the first presentation to
the third is the composite of the comparisons through the second, whenever all three are
compatible with the structure maps from `A`. This is the cocycle condition that makes the
comparisons a coherent system rather than a family of unrelated isomorphisms. -/
theorem eq_comp_of_comp_toCompletionLoc_eq_three [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (T'' : Finset A) (s'' : A)
    (S'' : Type*) [CommRing S''] [Algebra A S''] [IsLocalization.Away s'' S'']
    (hden'' : HasDenominatorPower P T'' s'' S'') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    letI := locUniformSpace P T'' s'' S'' hden''
    letI := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
    letI := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S'')
      (k : UniformSpace.Completion S →+* UniformSpace.Completion S''),
      Continuous g → Continuous h → Continuous k →
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T'' s'' S'' hden'' →
      k.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T'' s'' S'' hden'' →
      k = h.comp g := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  have _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  have _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := locUniformSpace P T'' s'' S'' hden''
  have _ := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
  have _ := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
  intro g h k hg hh hk hgc hhc hkc
  exact eq_comp_of_comp_toCompletionLoc_eq P T s S hden _ _ g hg hgc h hh hhc k hk hkc

/-- **The comparison isomorphism is the map it was built from.** The characteristic equation of
`presentationRingEquiv`: it does not introduce a new map, it packages `g` together with the
inverse supplied by `h`. -/
@[simp]
theorem presentationRingEquiv_coe [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S)
      (hg : Continuous g) (hh : Continuous h)
      (hgc : g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden')
      (hhc : h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden),
      ((presentationRingEquiv P T s S hden T' s' S' hden' g h hg hh hgc hhc :
        UniformSpace.Completion S ≃+* UniformSpace.Completion S') :
          UniformSpace.Completion S →+* UniformSpace.Completion S') = g := by
  intro g h hg hh hgc hhc
  rfl

/-- The inverse of the comparison isomorphism is the backward map it was built from. -/
@[simp]
theorem presentationRingEquiv_symm_coe [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S)
      (hg : Continuous g) (hh : Continuous h)
      (hgc : g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden')
      (hhc : h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden),
      (((presentationRingEquiv P T s S hden T' s' S' hden' g h hg hh hgc hhc).symm :
        UniformSpace.Completion S' ≃+* UniformSpace.Completion S) :
          UniformSpace.Completion S' →+* UniformSpace.Completion S) = h := by
  intro g h hg hh hgc hhc
  rfl

/-- The comparison isomorphism is continuous, being `g`. -/
theorem continuous_presentationRingEquiv [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S)
      (hg : Continuous g) (hh : Continuous h)
      (hgc : g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden')
      (hhc : h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden),
      Continuous (presentationRingEquiv P T s S hden T' s' S' hden' g h hg hh hgc hhc) := by
  intro g h hg hh hgc hhc
  exact hg

/-- The comparison isomorphism is compatible with the structure maps from `A`, which is the
property that determines it. -/
theorem presentationRingEquiv_coe_comp_toCompletionLoc [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type*) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S')
      (h : UniformSpace.Completion S' →+* UniformSpace.Completion S)
      (hg : Continuous g) (hh : Continuous h)
      (hgc : g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden')
      (hhc : h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T s S hden),
      (((presentationRingEquiv P T s S hden T' s' S' hden' g h hg hh hgc hhc :
        UniformSpace.Completion S ≃+* UniformSpace.Completion S') :
          UniformSpace.Completion S →+* UniformSpace.Completion S')).comp
        (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' := by
  intro g h hg hh hgc hhc
  exact hgc

end PairOfDefinition

end TauCeti.Huber
