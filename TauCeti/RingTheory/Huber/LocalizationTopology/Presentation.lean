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

The file has two halves. The first bundles a presentation as `Presentation` and orders those
bundles by refinement — the `Preorder` and `IsDirected` instances,
`Presentation.commonRefinement` as the common refinement, and `le_def` as the route from `p ≤ q`
to a cofactor.

The second is the comparison theory, and there **everything is uniqueness**: no comparison map is
constructed. Given maps in both directions that commute with the structure maps, they are mutually
inverse, and given three presentations the comparison through the middle one is the direct
comparison. That is exactly what
`TauCeti.Huber.PairOfDefinition.eq_id_of_comp_toCompletionLoc_eq_self` and
`…eq_comp_of_comp_toCompletionLoc_eq` say about maps out of `A⟨T/s⟩`, so each proof in that half
is a single application of one of them.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation`: the bundle `(num, den, hasDenominatorPower)` of
  a presentation, with the refinement preorder `Presentation.RefinedBy` and the common
  refinement `Presentation.commonRefinement` making refinement directed.
  `Presentation.commonRefinement_num` and `Presentation.commonRefinement_den` are its projection
  equations, since the body is not exported.
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

## Provenance

The bundle-and-refinement section is adapted from AINTLIB (see References): the idea of indexing
the structure presheaf by presentation data rather than by rational subsets, and the refinement
relation between presentations, are `StructurePresheafLimit.lean`'s. The bundling differs
deliberately — AINTLIB threads `RationalLocData` records through explicit hypotheses, while here
`Presentation` packs `(num, den, hasDenominatorPower)` so that refinement is a `Preorder` and
downstream constructions can be functorial. The comparison theory in the rest of this file is
original to this repository.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`, Apache-2.0.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], §8.1–8.2.
-/

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### The bundle of presentations, and refinement

The comparison theory below works with two presentations given separately; consumers indexing a
construction by *all* presentations — the intended structure presheaf — need them bundled and
ordered. Refinement here is a cofactor condition on the presentation data. It is sufficient for
containment of the rational subsets. The converse is not claimed, and the gap is *not* the
comparison-map step described above: `exists_refinement_of_subset` already produces numerator and
denominator data from a containment. What it does not supply is the standing `HasDenominatorPower`
hypothesis for the re-presented pair, which is what `Presentation` requires. -/

variable {P : PairOfDefinition A}

/-- **A presentation of a rational localization**: a numerator finset, a denominator, and the
standing `HasDenominatorPower` hypothesis for the localization away from the denominator. -/
@[ext]
structure Presentation (P : PairOfDefinition A) where
  /-- The numerators. -/
  num : Finset A
  /-- The denominator. -/
  den : A
  /-- The denominator-power hypothesis for `Localization.Away den`. -/
  hasDenominatorPower : HasDenominatorPower P num den (Localization.Away den)

/-- **The refinement relation**: `q` refines `p` when some cofactor `r` has
`q.den = p.den * r` and carries every numerator of `p` into a numerator of `q`. -/
def Presentation.RefinedBy (p q : Presentation P) : Prop :=
  ∃ r : A, q.den = p.den * r ∧ ∀ t ∈ p.num, t * r ∈ q.num

/-- The witness facts for the trivial refinement, with cofactor `1`. -/
theorem Presentation.refinedBy_witness_one (p : Presentation P) :
    p.den = p.den * 1 ∧ ∀ t ∈ p.num, t * 1 ∈ p.num :=
  ⟨(mul_one _).symm, fun t ht ↦ by rwa [mul_one]⟩

/-- The witness facts for a composite refinement: the cofactors multiply. -/
theorem Presentation.refinedBy_witness_mul {p q w : Presentation P} {r r₂ : A}
    (hr : q.den = p.den * r) (hT : ∀ t ∈ p.num, t * r ∈ q.num)
    (hr₂ : w.den = q.den * r₂) (hT₂ : ∀ t ∈ q.num, t * r₂ ∈ w.num) :
    w.den = p.den * (r * r₂) ∧ ∀ t ∈ p.num, t * (r * r₂) ∈ w.num :=
  ⟨by rw [hr₂, hr, mul_assoc],
    fun t ht ↦ by rw [← mul_assoc]; exact hT₂ _ (hT t ht)⟩

/-- Every presentation refines itself, with cofactor `1`. -/
theorem Presentation.RefinedBy.refl (p : Presentation P) : p.RefinedBy p :=
  ⟨1, p.refinedBy_witness_one.1, p.refinedBy_witness_one.2⟩

/-- Refinements compose: the cofactors multiply. -/
theorem Presentation.RefinedBy.trans {p q w : Presentation P} (hpq : p.RefinedBy q)
    (hqw : q.RefinedBy w) : p.RefinedBy w := by
  obtain ⟨r, hr, hT⟩ := hpq
  obtain ⟨r₂, hr₂, hT₂⟩ := hqw
  exact ⟨r * r₂, (Presentation.refinedBy_witness_mul hr hT hr₂ hT₂).1,
    (Presentation.refinedBy_witness_mul hr hT hr₂ hT₂).2⟩

/-- Refinement is a preorder, by `Presentation.RefinedBy.refl` and
`Presentation.RefinedBy.trans`.

These two stay as named theorems rather than being inlined into the fields below. The instance is
`public`, so its body is exposed for typeclass resolution and cannot unfold `RefinedBy`, whose
body this file deliberately does not export — inlining gives
`Invalid ⟨...⟩ notation: The expected type p.RefinedBy p is not an inductive type`. A theorem body
is not exposed, so it may unfold it; that asymmetry is what forces the two names. -/
instance : Preorder (Presentation P) where
  le := Presentation.RefinedBy
  le_refl := Presentation.RefinedBy.refl
  le_trans _ _ _ := Presentation.RefinedBy.trans

/-- **The refinement preorder, unfolded in one step**: the single introduction/elimination
lemma for `≤`. The body of `RefinedBy` is not exported, so this is the route from `p ≤ q` to a
cofactor.

`le_def`, not `le_iff`: this is the one-step definitional unfolding of a custom `≤`, which is
what Mathlib names `le_def` (`Order/Quotient.lean`, `Order/Hom/Basic.lean`,
`Order/Preorder/Finsupp.lean`, several of them `.rfl` as here). Bare `le_iff` there is reserved
for characterisations that are not the definition. -/
theorem Presentation.le_def {p q : Presentation P} :
    p ≤ q ↔ ∃ r : A, q.den = p.den * r ∧ ∀ t ∈ p.num, t * r ∈ q.num := Iff.rfl

open scoped Classical Pointwise in
/-- **The common refinement**, refining both factors: the numerators are the pairwise
products of the factors' numerator sets augmented by their own denominators, and the denominator
is the product. The augmentation matches `rationalSubset_inter`'s presentation of an
intersection.

`Presentation` carries no openness or admissibility field, so nothing here tracks or preserves
openness of the numerator ideal; a consumer that needs it — the structure presheaf's index — must
carry and re-establish it itself. -/
noncomputable def Presentation.commonRefinement (p q : Presentation P) : Presentation P where
  num := insert p.den p.num * insert q.den q.num
  den := p.den * q.den
  hasDenominatorPower := by
    classical
    exact hasDenominatorPower_mul P p.num q.num _ p.den q.den (Localization.Away p.den)
      (Localization.Away q.den) (Localization.Away (p.den * q.den))
      (fun _ ht ↦ Finset.mul_mem_mul (Finset.mem_insert_of_mem ht) (Finset.mem_insert_self _ _))
      (fun t ht ↦ mul_comm p.den t ▸
        Finset.mul_mem_mul (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ht))
      p.hasDenominatorPower q.hasDenominatorPower

open scoped Classical Pointwise in
/-- The numerator equation for the common refinement. The body of `commonRefinement` is not
exported, so this is how a consumer computes with it — in particular, how it is matched against
`rationalSubset_inter`'s presentation of an intersection. -/
@[simp]
theorem Presentation.commonRefinement_num (p q : Presentation P) :
    (p.commonRefinement q).num = insert p.den p.num * insert q.den q.num := (rfl)

/-- The denominator equation for the common refinement. -/
@[simp]
theorem Presentation.commonRefinement_den (p q : Presentation P) :
    (p.commonRefinement q).den = p.den * q.den := (rfl)

open scoped Classical Pointwise in
/-- The common refinement refines its left factor, with cofactor the right denominator. -/
theorem Presentation.le_commonRefinement_left (p q : Presentation P) : p ≤ p.commonRefinement q :=
  ⟨q.den, rfl, fun _ ht ↦
    Finset.mul_mem_mul (Finset.mem_insert_of_mem ht) (Finset.mem_insert_self _ _)⟩

open scoped Classical Pointwise in
/-- The common refinement refines its right factor, with cofactor the left denominator. -/
theorem Presentation.le_commonRefinement_right (p q : Presentation P) : q ≤ p.commonRefinement q :=
  ⟨p.den, mul_comm p.den q.den, fun t ht ↦ mul_comm p.den t ▸
    Finset.mul_mem_mul (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem ht)⟩

/-- **The refinement preorder is directed**: any two presentations admit a common refinement,
namely `Presentation.commonRefinement`. So presentations of the same rational subset never sit as
independent factors in a limit over this order — both map onwards to a common refinement. The
existential form is `exists_ge_ge`, which this instance supplies generically. -/
instance : IsDirected (Presentation P) (· ≤ ·) :=
  ⟨fun p q ↦ ⟨p.commonRefinement q, p.le_commonRefinement_left q,
    p.le_commonRefinement_right q⟩⟩

/-! ### Comparing two presentations of the same subset -/

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
