/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic

/-!
# `A⟨T/s⟩` is a complete separated topological ring

The adic structure presheaf (roadmap Layer 3.3) is intended to assign `A⟨T/s⟩` to the rational
subset `R(T/s)`, and its values are required to be *complete separated* topological rings
(*Adic Spaces*, arXiv:1910.05934v1, §8.1–§8.2). This module supplies the categorical packaging
that assignment needs: it exhibits `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`,
lifts continuous comparison maps to morphisms, and packages mutually compatible comparisons as
isomorphisms.

No presheaf exists yet, and the objects here remain *presentationwise*: they depend on the data
`(T, s, S, hden)` presenting the localisation, not only on the subset `R(T/s)`. The isomorphism
constructed here is conditional on compatible comparison maps in both directions. Producing those
maps from equality of rational subsets, and constructing restriction maps from containments, are
separate steps.

Nothing here is deep — `A⟨T/s⟩` is a separated completion, so it is complete and Hausdorff for its
own uniformity, and `CompleteSeparatedTopCommRingCat.of` bundles exactly that. What the module
supplies is the *bookkeeping*: `locTopology` is not an instance, so the uniform structures on `Aₛ`
are not in scope by inference, and a consumer would otherwise repeat the three-declaration preamble
`locUniformSpace`, `isUniformAddGroup_locUniformSpace`, `isTopologicalRing_locUniformSpace` at
every use. The definition below carries it once.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.completionLocObj` : `A⟨T/s⟩` as an object of
  `CompleteSeparatedTopCommRingCat`, presentationwise in `(T, s, S, hden)`.
* `TauCeti.Huber.PairOfDefinition.completionLocObjHom` : a continuous comparison map as a
  morphism between presentationwise objects.
* `TauCeti.Huber.PairOfDefinition.completionLocObjIso` : compatible comparisons in both
  directions as an isomorphism of complete separated topological rings.

## Main results

* `TauCeti.Huber.PairOfDefinition.completionLocObj_obj` : the underlying `TopCommRingCat` of that
  object is `UniformSpace.Completion S` with the topology `locUniformSpace` induces.
* `TauCeti.Huber.PairOfDefinition.completionLocObjHom_eq_id` and
  `TauCeti.Huber.PairOfDefinition.completionLocObjHom_eq_comp` : identity and composition for
  comparison morphisms compatible with the structure maps from `A`.
* `TauCeti.Huber.PairOfDefinition.completionLocObjHom_id` and
  `TauCeti.Huber.PairOfDefinition.completionLocObjHom_comp` : packaging preserves identity and
  composition.

## Provenance

The packaging here is this repository's own, built on the localisation topology of
`LocalizationTopology.Basic`, which is the AINTLIB port — see that module's Provenance section for
the source file and commit. AINTLIB's own structure-presheaf files supplied nothing here: it
carries the codomain fact inside its presheaf construction rather than as a separate object, so
there was nothing at this granularity to port.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2, where the structure
  presheaf of an adic space is built with complete separated topological rings as its codomain.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition and Definition 5.51, §5.6, for `A⟨T/s⟩`
  itself, which `LocalizationTopology.Completion` constructs.
-/

namespace TauCeti.Huber

open CategoryTheory TauCeti.TopCommRingCat

public section

universe u v

variable {A : Type v} [CommRing A] [TopologicalSpace A]

namespace PairOfDefinition

/-! ### `A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat` -/

/-- **`A⟨T/s⟩` as an object of `CompleteSeparatedTopCommRingCat`**: the separated completion of
`Aₛ` under `locTopology`, which is complete and Hausdorff for its own uniformity.

This is the object the adic structure presheaf is intended to take on the rational subset
`R(T/s)`; it is presentationwise, depending on `(T, s, S, hden)` and not yet known to depend only
on `R(T/s)`, and the restriction maps are later work.

`completionLocObj_obj` identifies the underlying object; the body is not exported, so that is how
a consumer computes with it. -/
noncomputable def completionLocObj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A)
    (s : A) (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) : CompleteSeparatedTopCommRingCat :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  CompleteSeparatedTopCommRingCat.of (UniformSpace.Completion S)

/-- The underlying topological ring of `completionLocObj` is `A⟨T/s⟩` itself: the completion of
`Aₛ` for the uniformity `locUniformSpace`. -/
@[simp]
theorem completionLocObj_obj [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (completionLocObj P T s S hden).obj = TopCommRingCat.of (UniformSpace.Completion S) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  exact CompleteSeparatedTopCommRingCat.of_obj _

/-! ### Comparison morphisms between presentationwise objects -/

/-- A continuous ring homomorphism between two completed localisations, as a morphism between
their presentationwise objects in `CompleteSeparatedTopCommRingCat`.

No compatibility with the structure maps from `A` is required merely to form the morphism. That
compatibility is used by `completionLocObjHom_eq_id`, `completionLocObjHom_eq_comp`, and
`completionLocObjIso`. -/
noncomputable def completionLocObjHom [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    (g : UniformSpace.Completion S →+* UniformSpace.Completion S') → Continuous g →
      (completionLocObj P T s S hden ⟶ completionLocObj P T' s' S' hden') := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  let _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  let _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro g hg
  exact InducedCategory.homMk
    (eqToHom (completionLocObj_obj P T s S hden) ≫
      (⟨g, hg⟩ : TopCommRingCat.of (UniformSpace.Completion S) ⟶
        TopCommRingCat.of (UniformSpace.Completion S')) ≫
      eqToHom (completionLocObj_obj P T' s' S' hden').symm)

/-- The underlying morphism of `completionLocObjHom` is the given ring homomorphism, transported
across `completionLocObj_obj` at its source and target. -/
@[simp]
theorem completionLocObjHom_hom [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S') :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P T' s' S' hden'
    letI := isUniformAddGroup_locUniformSpace P T' s' S' hden'
    letI := isTopologicalRing_locUniformSpace P T' s' S' hden'
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S') (hg : Continuous g),
      (completionLocObjHom P T s S hden T' s' S' hden' g hg).hom =
        eqToHom (completionLocObj_obj P T s S hden) ≫
          (⟨g, hg⟩ : TopCommRingCat.of (UniformSpace.Completion S) ⟶
            TopCommRingCat.of (UniformSpace.Completion S')) ≫
          eqToHom (completionLocObj_obj P T' s' S' hden').symm := by
  intro g hg
  rfl

/-- Packaging a composite of continuous ring homomorphisms gives the categorical composite of
their packaged morphisms. -/
@[simp]
theorem completionLocObjHom_comp [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (T'' : Finset A) (s'' : A)
    (S'' : Type u) [CommRing S''] [Algebra A S''] [IsLocalization.Away s'' S'']
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
      (hg : Continuous g) (hh : Continuous h),
      completionLocObjHom P T s S hden T'' s'' S'' hden'' (h.comp g) (hh.comp hg) =
        completionLocObjHom P T s S hden T' s' S' hden' g hg ≫
          completionLocObjHom P T' s' S' hden' T'' s'' S'' hden'' h hh := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  let _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  let _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := locUniformSpace P T'' s'' S'' hden''
  let _ := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
  let _ := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
  intro g h hg hh
  apply InducedCategory.hom_ext
  rw [completionLocObjHom_hom, ObjectProperty.FullSubcategory.comp_hom,
    completionLocObjHom_hom, completionLocObjHom_hom]
  let G : TopCommRingCat.of (UniformSpace.Completion S) ⟶
      TopCommRingCat.of (UniformSpace.Completion S') := ⟨g, hg⟩
  let H : TopCommRingCat.of (UniformSpace.Completion S') ⟶
      TopCommRingCat.of (UniformSpace.Completion S'') := ⟨h, hh⟩
  -- The public object equation is the only way to expose the transports surrounding `G` and `H`;
  -- `completionLocObj` itself is deliberately not exposed.
  change eqToHom _ ≫ (G ≫ H) ≫ eqToHom _ =
    (eqToHom _ ≫ G ≫ eqToHom _) ≫ eqToHom _ ≫ H ≫ eqToHom _
  simp [Category.assoc]

/-- A comparison endomorphism compatible with the structure map from `A` is the identity
morphism of the presentationwise complete separated object. -/
@[simp]
theorem completionLocObjHom_eq_id [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (g : UniformSpace.Completion S →+* UniformSpace.Completion S) (hg : Continuous g),
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T s S hden →
      completionLocObjHom P T s S hden T s S hden g hg =
        𝟙 (completionLocObj P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  intro g hg hgc
  have hg_id : g = RingHom.id (UniformSpace.Completion S) :=
    eq_id_of_comp_toCompletionLoc_eq_self P T s S hden g hg hgc
  apply InducedCategory.hom_ext
  rw [completionLocObjHom_hom]
  have hG : (⟨g, hg⟩ : TopCommRingCat.of (UniformSpace.Completion S) ⟶
      TopCommRingCat.of (UniformSpace.Completion S)) =
      𝟙 (TopCommRingCat.of (UniformSpace.Completion S)) := by
    apply Subtype.ext
    exact hg_id
  rw [hG]
  simp

/-- Packaging the identity ring homomorphism gives the identity morphism.

This is the special case of `completionLocObjHom_eq_id` where the compatibility hypothesis holds
definitionally, so it is deliberately not a `simp` lemma: `simp` already closes it using the
general statement. -/
theorem completionLocObjHom_id [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completionLocObjHom P T s S hden T s S hden (RingHom.id _) continuous_id =
      𝟙 (completionLocObj P T s S hden) := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  exact completionLocObjHom_eq_id P T s S hden (RingHom.id _) continuous_id rfl

/-- Comparison morphisms compatible with the structure maps from `A` compose categorically.
This is the cocycle law for presentationwise objects in `CompleteSeparatedTopCommRingCat`. -/
theorem completionLocObjHom_eq_comp [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
    (hden' : HasDenominatorPower P T' s' S')
    (T'' : Finset A) (s'' : A)
    (S'' : Type u) [CommRing S''] [Algebra A S''] [IsLocalization.Away s'' S'']
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
      (k : UniformSpace.Completion S →+* UniformSpace.Completion S'')
      (hg : Continuous g) (hh : Continuous h) (hk : Continuous k),
      g.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T' s' S' hden' →
      h.comp (toCompletionLoc P T' s' S' hden') = toCompletionLoc P T'' s'' S'' hden'' →
      k.comp (toCompletionLoc P T s S hden) = toCompletionLoc P T'' s'' S'' hden'' →
      completionLocObjHom P T s S hden T'' s'' S'' hden'' k hk =
        completionLocObjHom P T s S hden T' s' S' hden' g hg ≫
          completionLocObjHom P T' s' S' hden' T'' s'' S'' hden'' h hh := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  let _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  let _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  let _ := locUniformSpace P T'' s'' S'' hden''
  let _ := isUniformAddGroup_locUniformSpace P T'' s'' S'' hden''
  let _ := isTopologicalRing_locUniformSpace P T'' s'' S'' hden''
  intro g h k hg hh hk hgc hhc hkc
  have hk_comp : k = h.comp g :=
    eq_comp_of_comp_toCompletionLoc_eq_three P T s S hden T' s' S' hden'
      T'' s'' S'' hden'' g h k hg hh hk hgc hhc hkc
  apply InducedCategory.hom_ext
  rw [completionLocObjHom_hom, ObjectProperty.FullSubcategory.comp_hom,
    completionLocObjHom_hom, completionLocObjHom_hom]
  let G : TopCommRingCat.of (UniformSpace.Completion S) ⟶
      TopCommRingCat.of (UniformSpace.Completion S') := ⟨g, hg⟩
  let H : TopCommRingCat.of (UniformSpace.Completion S') ⟶
      TopCommRingCat.of (UniformSpace.Completion S'') := ⟨h, hh⟩
  let K : TopCommRingCat.of (UniformSpace.Completion S) ⟶
      TopCommRingCat.of (UniformSpace.Completion S'') := ⟨k, hk⟩
  have hK : K = G ≫ H := by
    apply Subtype.ext
    exact hk_comp
  -- The public object equation is the only way to expose the transports surrounding `G`, `H`,
  -- and `K`; `completionLocObj` itself is deliberately not exposed.
  change eqToHom _ ≫ K ≫ eqToHom _ =
    (eqToHom _ ≫ G ≫ eqToHom _) ≫ eqToHom _ ≫ H ≫ eqToHom _
  rw [hK]
  simp [Category.assoc]

/-! ### Isomorphisms between presentationwise objects -/

/-- Compatible comparison maps in both directions give an isomorphism between the associated
objects of `CompleteSeparatedTopCommRingCat`.

This is the categorical form of `presentationRingEquiv`. As there, the construction is
conditional: equality of rational subsets must separately supply the two comparison maps and
their compatibility with the structure maps from `A`. -/
noncomputable def completionLocObjIso [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
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
      (completionLocObj P T s S hden ≅ completionLocObj P T' s' S' hden') := by
  let _ := locUniformSpace P T s S hden
  let _ := isUniformAddGroup_locUniformSpace P T s S hden
  let _ := isTopologicalRing_locUniformSpace P T s S hden
  let _ := locUniformSpace P T' s' S' hden'
  let _ := isUniformAddGroup_locUniformSpace P T' s' S' hden'
  let _ := isTopologicalRing_locUniformSpace P T' s' S' hden'
  intro g h hg hh hgc hhc
  refine
    { hom := completionLocObjHom P T s S hden T' s' S' hden' g hg
      inv := completionLocObjHom P T' s' S' hden' T s S hden h hh
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · have hcomp : (h.comp g).comp (toCompletionLoc P T s S hden) =
        toCompletionLoc P T s S hden := by
      rw [RingHom.comp_assoc, hgc, hhc]
    calc
      completionLocObjHom P T s S hden T' s' S' hden' g hg ≫
          completionLocObjHom P T' s' S' hden' T s S hden h hh =
        completionLocObjHom P T s S hden T s S hden (h.comp g) (hh.comp hg) :=
          (completionLocObjHom_eq_comp P T s S hden T' s' S' hden' T s S hden
            g h (h.comp g) hg hh (hh.comp hg) hgc hhc hcomp).symm
      _ = 𝟙 (completionLocObj P T s S hden) :=
        completionLocObjHom_eq_id P T s S hden (h.comp g) (hh.comp hg) hcomp
  · have hcomp : (g.comp h).comp (toCompletionLoc P T' s' S' hden') =
        toCompletionLoc P T' s' S' hden' := by
      rw [RingHom.comp_assoc, hhc, hgc]
    calc
      completionLocObjHom P T' s' S' hden' T s S hden h hh ≫
          completionLocObjHom P T s S hden T' s' S' hden' g hg =
        completionLocObjHom P T' s' S' hden' T' s' S' hden'
          (g.comp h) (hg.comp hh) :=
          (completionLocObjHom_eq_comp P T' s' S' hden' T s S hden T' s' S' hden'
            h g (g.comp h) hh hg (hg.comp hh) hhc hgc hcomp).symm
      _ = 𝟙 (completionLocObj P T' s' S' hden') :=
        completionLocObjHom_eq_id P T' s' S' hden' (g.comp h) (hg.comp hh) hcomp

/-- The forward morphism of `completionLocObjIso` is the packaged forward comparison map. -/
@[simp]
theorem completionLocObjIso_hom [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
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
      (completionLocObjIso P T s S hden T' s' S' hden' g h hg hh hgc hhc).hom =
        completionLocObjHom P T s S hden T' s' S' hden' g hg := by
  intro g h hg hh hgc hhc
  rfl

/-- The inverse morphism of `completionLocObjIso` is the packaged backward comparison map. -/
@[simp]
theorem completionLocObjIso_inv [IsTopologicalRing A]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (T' : Finset A) (s' : A)
    (S' : Type u) [CommRing S'] [Algebra A S'] [IsLocalization.Away s' S']
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
      (completionLocObjIso P T s S hden T' s' S' hden' g h hg hh hgc hhc).inv =
        completionLocObjHom P T' s' S' hden' T s S hden h hh := by
  intro g h hg hh hgc hhc
  rfl

end PairOfDefinition

end

end TauCeti.Huber
