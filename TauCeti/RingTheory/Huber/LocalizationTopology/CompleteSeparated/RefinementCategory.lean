/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.Restriction
public import TauCeti.RingTheory.Huber.LocalizationTopology.Presentation
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The refinement category of presentations, and its functor to complete separated rings

The refinement preorder on `Presentation` (`LocalizationTopology/Presentation.lean`) has an
associated category; this file makes the assignment `p ↦ A⟨p.num / p.den⟩` a functor from it
into `CompleteSeparatedTopCommRingCat`, with the restriction morphisms of
`CompleteSeparated/Restriction.lean` as its action on arrows.

This preorder is *intended* to index the adic structure presheaf — `𝒪_X(V)` as a limit of this
functor over the presentations whose rational subset lies in `V` — but no presheaf exists in
this file's imports, and refinement is the cofactor relation on presentation data: sufficient
for containment of the rational subsets, not (yet) proved equivalent to it.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation.completionLocObj` : the object `A⟨T/s⟩` of a
  presentation.
* `TauCeti.Huber.PairOfDefinition.Presentation.restrictionHom` : the restriction morphism of a
  refinement, from an arbitrary choice of cofactor.
* `TauCeti.Huber.PairOfDefinition.presentationFunctor` : the functor into
  `CompleteSeparatedTopCommRingCat`.

## Main results

* `TauCeti.Huber.PairOfDefinition.Presentation.restrictionHom_eq` : cofactor-independence — the
  morphism is computed by *any* cofactor witnessing the refinement.
* `TauCeti.Huber.PairOfDefinition.Presentation.restrictionHom_refl` and
  `…restrictionHom_comp` : the identity and composition laws, stated on `restrictionHom`
  itself so that simp-normalised goals can still reach them.

## Why the cofactor must be quantified away

A category whose arrows carried the cofactor would not be a preorder category, and the intended
index has to be one: a limit over *the presentations inside `V`* is indexed by a condition on
presentations, not by extra data. Quantifying the cofactor away is only legitimate because the
restriction morphism does not depend on it — `restrictionObjHom_congr` — which is what lets the
functor's action be defined by an arbitrary choice and still be functorial.

For the same reason the cofactor accessor and its two spec lemmas are `private` here rather than
public in `LocalizationTopology/Presentation.lean`: they name a `choose` witness with no
mathematical content, so exporting them would let a consumer depend on the choice. The public
route from `p ≤ q` to a cofactor is `Presentation.le_def`, and the public statement about
the morphism is
`Presentation.restrictionHom_eq`, which holds for every cofactor.

## Provenance

Adapted from AINTLIB's `StructurePresheafLimit.lean` (see References): the idea of indexing the
structure presheaf by presentation data rather than by rational subsets, and the refinement
relation between presentations, are that file's. The bundling differs deliberately: AINTLIB
threads `RationalLocData` records through explicit hypotheses, while here `Presentation` packs
the data so that refinement is a `Preorder` and this assignment is a functor — the shape a
categorical limit needs.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1–§8.2.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`.
-/

namespace TauCeti.Huber

open CategoryTheory

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

namespace PairOfDefinition

variable {P : PairOfDefinition A}

/-- The completed rational localization `A⟨T/s⟩` attached to a presentation, as an object. -/
noncomputable abbrev Presentation.completionLocObj (p : Presentation P) :
    CompleteSeparatedTopCommRingCat.{v} :=
  _root_.TauCeti.Huber.PairOfDefinition.completionLocObj P p.num p.den (Localization.Away p.den)
    p.hasDenominatorPower

/-- **The chosen cofactor of a refinement**, an implementation detail of
`Presentation.restrictionHom`. Extraction from `h : p ≤ q` crosses the `≤`-to-existential
boundary through `Presentation.le_def`, here, once. The choice carries no mathematical content
— `Presentation.restrictionHom_eq` computes the morphism from *any* cofactor — so it stays
private and consumers go through that lemma. -/
private noncomputable def Presentation.cofactor {p q : Presentation P} (h : p ≤ q) : A :=
  (Presentation.le_def.mp h).choose

omit [IsTopologicalRing A] in
/-- The denominator of a refinement is the coarser denominator times the chosen cofactor. -/
private theorem Presentation.den_eq_mul_cofactor {p q : Presentation P} (h : p ≤ q) :
    q.den = p.den * Presentation.cofactor h :=
  (Presentation.le_def.mp h).choose_spec.1

omit [IsTopologicalRing A] in
/-- The chosen cofactor carries numerators of the coarser presentation into the finer one. -/
private theorem Presentation.mul_cofactor_mem {p q : Presentation P} (h : p ≤ q) {t : A}
    (ht : t ∈ p.num) : t * Presentation.cofactor h ∈ q.num :=
  (Presentation.le_def.mp h).choose_spec.2 t ht

/-- The restriction morphism attached to a refinement, taking the chosen cofactor. It does not
depend on that choice — `Presentation.restrictionHom_eq` — and it is the preorder-category
counterpart of `restrictionObjHom`, not Mathlib's arrow `LE.le.hom`. -/
noncomputable def Presentation.restrictionHom {p q : Presentation P} (h : p ≤ q) :
    p.completionLocObj ⟶ q.completionLocObj :=
  restrictionObjHom P p.num p.den _ p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower
    (Presentation.cofactor h) (Presentation.den_eq_mul_cofactor h)
    fun _ ↦ Presentation.mul_cofactor_mem h

/-- `Presentation.restrictionHom` is computed by *any* cofactor witnessing the refinement, not
only the chosen one. This is `restrictionObjHom_congr` transported to the preorder. -/
theorem Presentation.restrictionHom_eq {p q : Presentation P} (h : p ≤ q) (r : A)
    (hr : q.den = p.den * r) (hT : ∀ t ∈ p.num, t * r ∈ q.num) :
    Presentation.restrictionHom h =
      restrictionObjHom P p.num p.den _ p.hasDenominatorPower q.num q.den _
        q.hasDenominatorPower r hr hT :=
  restrictionObjHom_congr P p.num p.den _ p.hasDenominatorPower q.num q.den _
    q.hasDenominatorPower (Presentation.cofactor h) r (Presentation.den_eq_mul_cofactor h)
    (fun _ ↦ Presentation.mul_cofactor_mem h) hr hT

/-- The restriction morphism of the trivial refinement is the identity. -/
@[simp]
theorem Presentation.restrictionHom_refl (p : Presentation P) :
    Presentation.restrictionHom (le_refl p) = 𝟙 p.completionLocObj := by
  rw [Presentation.restrictionHom_eq (r := 1) (hr := p.refinedBy_witness_one.1)
    (hT := p.refinedBy_witness_one.2)]
  exact restrictionObjHom_self P p.num p.den _ p.hasDenominatorPower

/-- Restriction morphisms compose along composite refinements. -/
@[reassoc (attr := simp)]
theorem Presentation.restrictionHom_comp {p q w : Presentation P} (h₁ : p ≤ q) (h₂ : q ≤ w) :
    Presentation.restrictionHom h₁ ≫ Presentation.restrictionHom h₂ =
      Presentation.restrictionHom (h₁.trans h₂) := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h₁
  obtain ⟨r₂, hr₂, hT₂⟩ := Presentation.le_def.mp h₂
  rw [Presentation.restrictionHom_eq h₁ r hr hT, Presentation.restrictionHom_eq h₂ r₂ hr₂ hT₂,
    Presentation.restrictionHom_eq (h₁.trans h₂) (r * r₂)
      (Presentation.refinedBy_witness_mul hr hT hr₂ hT₂).1
      (Presentation.refinedBy_witness_mul hr hT hr₂ hT₂).2]
  exact restrictionObjHom_comp_restrictionObjHom P p.num p.den _ p.hasDenominatorPower q.num
    q.den _ q.hasDenominatorPower r hr hT w.num w.den _ w.hasDenominatorPower r₂ hr₂ hT₂

/-- **The functor `p ↦ A⟨p.num / p.den⟩`** from the refinement category into
`CompleteSeparatedTopCommRingCat`, with the restriction morphisms as its action on arrows.
Functoriality is `restrictionHom_refl` and `restrictionHom_comp`.

`@[expose]` is load-bearing, for a narrower reason than exposure usually carries: with the body
sealed, `presentationFunctor_map` below does not typecheck *as a statement*. Its two sides live
in `(presentationFunctor P).obj p ⟶ (presentationFunctor P).obj q` and in
`p.completionLocObj ⟶ q.completionLocObj`, and only unfolding the functor identifies those
types. `presentationFunctor_obj` is statable either
way; it is the `map` equation, and the definitional reindexing a limit over this category
needs, that the exposure provides. -/
@[expose]
noncomputable def presentationFunctor (P : PairOfDefinition A) :
    Presentation P ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj p := p.completionLocObj
  map {_ _} h := Presentation.restrictionHom h.le
  map_id p := Presentation.restrictionHom_refl p
  map_comp {_ _ _} f g := (Presentation.restrictionHom_comp f.le g.le).symm

/-- The functor takes a presentation to its own object. -/
@[simp]
theorem presentationFunctor_obj (P : PairOfDefinition A) (p : Presentation P) :
    (presentationFunctor P).obj p = p.completionLocObj := rfl

/-- The functor takes a refinement to its restriction morphism. -/
@[simp]
theorem presentationFunctor_map (P : PairOfDefinition A) {p q : Presentation P} (h : p ⟶ q) :
    (presentationFunctor P).map h = Presentation.restrictionHom h.le := rfl

end PairOfDefinition

end

end TauCeti.Huber
