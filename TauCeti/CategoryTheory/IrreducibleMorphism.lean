/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Balanced

/-!
# Irreducible morphisms

A morphism `f : X ⟶ Y` is **irreducible** when it is neither a split monomorphism nor a split
epimorphism, and every factorization `f = g ≫ h` has `g` a split mono or `h` a split epi. So `f`
admits no "genuine" intermediate object: any object `Z` it factors through either has `X` as a
retract, split off by the first factor `g`, or has `Y` as a retract, split off by the second
factor `h`.

Irreducible morphisms are the arrows of the Auslander-Reiten quiver of a finite-dimensional
algebra, and the middle term of an almost-split sequence is glued to its ends by them. Nothing in
the definition is special to modules, so this file develops the notion for an arbitrary category
and specializes only where the statement forces it.

## Main results

* `TauCeti.IsIrreducibleMorphism`: the definition, with `TauCeti.isIrreducibleMorphism_iff`
  spelling out its three clauses as the introduction and elimination rule.
* `TauCeti.IsIrreducibleMorphism.not_isIso`: an irreducible morphism is not an isomorphism.
* `TauCeti.IsIrreducibleMorphism.comp_iso` and `TauCeti.IsIrreducibleMorphism.iso_comp`,
  with the `iff` forms `TauCeti.isIrreducibleMorphism_comp_iso_iff` and
  `TauCeti.isIrreducibleMorphism_iso_comp_iff`: irreducibility only depends on the morphism up to
  isomorphisms of its source and target, so it descends to the arrows of a skeleton.
* `TauCeti.not_isIrreducibleMorphism_zero`: **a zero morphism is never irreducible**, and its
  contrapositive `TauCeti.IsIrreducibleMorphism.ne_zero`.
* `TauCeti.IsIrreducibleMorphism.mono_or_epi`: **an irreducible morphism of an abelian category is
  a monomorphism or an epimorphism**, and by
  `TauCeti.IsIrreducibleMorphism.not_mono_and_epi` never both, so
  `TauCeti.IsIrreducibleMorphism.mono_iff_not_epi` is a genuine dichotomy.

Two general facts about split morphisms and composition are proved on the way and stated for
reuse: `TauCeti.isSplitMono_of_isSplitMono_comp` and `TauCeti.isSplitEpi_of_isSplitEpi_comp`.
Mathlib has the composition direction (a composite of split monos is a split mono) but not these
cancellation directions.

## Implementation notes

The definition is a conjunction rather than a structure, matching the signature pinned by the
roadmap; the three components are available as `TauCeti.IsIrreducibleMorphism.not_isSplitMono`,
`TauCeti.IsIrreducibleMorphism.not_isSplitEpi` and `TauCeti.IsIrreducibleMorphism.factors`, so
that no proof has to project through `And` by hand. The body of the definition is not exposed
outside this module, so `⟨_, _, _⟩` is not available to establish it downstream;
`TauCeti.isIrreducibleMorphism_iff` is the introduction rule.

The quantifier in the third component ranges over *all* objects of the ambient category. For the
Auslander-Reiten theory of a finite-dimensional algebra that is the intended reading: the ambient
category there is already the finite-dimensional one (compare the finiteness side conditions that
the roadmap's `IsAlmostSplit` carries, which are needed because the lifting properties of an
almost-split sequence are *not* stable under enlarging the category, whereas the condition here
is a factorization property of a single morphism and so is simply inherited by any full
subcategory containing `X` and `Y`).

The dichotomy `mono_or_epi` is proved by feeding the image factorization `f = e ≫ i` of an abelian
category to the definition: `e` is epi, so if it splits it is an isomorphism and `f` is mono; `i`
is mono, so if it splits it is an isomorphism and `f` is epi.

## References

This implements the `IsIrreducibleMorphism` target of Layer 6 (Auslander-Reiten theory) of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, stated there for
representations of a quiver; the definition below is the same one for a general category, and
instantiating `C` at `TauCeti.QuiverRep k Q` returns the pinned signature.

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, CUP (1995), V.5.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), IV.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Cancelling a split morphism off a composite -/

/-- **A composite that is a split mono has a split mono for its first factor**: a retraction of
`f ≫ g` retracts `f` after `g` is absorbed into it. Mathlib has the composition direction
(`CategoryTheory.IsSplitMono` is closed under `≫`) but not this cancellation. -/
theorem isSplitMono_of_isSplitMono_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSplitMono (f ≫ g)] : IsSplitMono f :=
  IsSplitMono.mk' ⟨g ≫ retraction (f ≫ g), by rw [← Category.assoc]; exact IsSplitMono.id _⟩

/-- **A composite that is a split epi has a split epi for its second factor**: a section of
`f ≫ g` sections `g` after `f` is absorbed into it. -/
theorem isSplitEpi_of_isSplitEpi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSplitEpi (f ≫ g)] : IsSplitEpi g :=
  IsSplitEpi.mk' ⟨section_ (f ≫ g) ≫ f, by rw [Category.assoc]; exact IsSplitEpi.id _⟩

/-- The remaining cancellation, in the case the absorbed factor is invertible: if `f ≫ e.hom`
is a split epi then so is `f`. -/
theorem isSplitEpi_of_isSplitEpi_comp_iso {X Y Y' : C} (f : X ⟶ Y) (e : Y ≅ Y')
    [IsSplitEpi (f ≫ e.hom)] : IsSplitEpi f := by
  have h : (f ≫ e.hom) ≫ e.inv = f := by simp
  rw [← h]
  infer_instance

/-- The remaining cancellation, in the case the absorbed factor is invertible: if `e.hom ≫ f`
is a split mono then so is `f`. -/
theorem isSplitMono_of_isSplitMono_iso_comp {X' X Y : C} (e : X' ≅ X) (f : X ⟶ Y)
    [IsSplitMono (e.hom ≫ f)] : IsSplitMono f := by
  have h : e.inv ≫ e.hom ≫ f = f := by simp
  rw [← h]
  infer_instance

/-! ### Irreducible morphisms -/

/-- **An irreducible morphism**: one that is neither a split monomorphism nor a split
epimorphism, and through which no object factors nontrivially — in every factorization
`f = g ≫ h`, either `g` is a split mono or `h` is a split epi.

The two negative clauses are what makes the notion nonvacuous: without them every isomorphism
would qualify. With them, an irreducible morphism is in particular not an isomorphism
(`TauCeti.IsIrreducibleMorphism.not_isIso`) and not zero
(`TauCeti.IsIrreducibleMorphism.ne_zero`). -/
def IsIrreducibleMorphism {X Y : C} (f : X ⟶ Y) : Prop :=
  ¬ IsSplitMono f ∧ ¬ IsSplitEpi f ∧
    ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y), g ≫ h = f → IsSplitMono g ∨ IsSplitEpi h

variable {X Y : C} {f : X ⟶ Y}

/-- **The three clauses of irreducibility**, spelled out. This is both the introduction rule —
the body of `TauCeti.IsIrreducibleMorphism` is not exposed outside this module, so `⟨_, _, _⟩`
does not establish it there — and the elimination rule in a single statement; the individual
components are also available as `TauCeti.IsIrreducibleMorphism.not_isSplitMono`,
`TauCeti.IsIrreducibleMorphism.not_isSplitEpi` and `TauCeti.IsIrreducibleMorphism.factors`. -/
theorem isIrreducibleMorphism_iff :
    IsIrreducibleMorphism f ↔ ¬ IsSplitMono f ∧ ¬ IsSplitEpi f ∧
      ∀ (Z : C) (g : X ⟶ Z) (h : Z ⟶ Y), g ≫ h = f → IsSplitMono g ∨ IsSplitEpi h :=
  Iff.rfl

/-- An irreducible morphism is not a split monomorphism. -/
theorem IsIrreducibleMorphism.not_isSplitMono (hf : IsIrreducibleMorphism f) :
    ¬ IsSplitMono f := hf.1

/-- An irreducible morphism is not a split epimorphism. -/
theorem IsIrreducibleMorphism.not_isSplitEpi (hf : IsIrreducibleMorphism f) :
    ¬ IsSplitEpi f := hf.2.1

/-- **The factorization property.** In any factorization of an irreducible morphism, the first
factor is a split mono or the second is a split epi. -/
theorem IsIrreducibleMorphism.factors (hf : IsIrreducibleMorphism f) {Z : C} (g : X ⟶ Z)
    (h : Z ⟶ Y) (hgh : g ≫ h = f) : IsSplitMono g ∨ IsSplitEpi h := hf.2.2 Z g h hgh

/-- The form of `TauCeti.IsIrreducibleMorphism.factors` used when the second factor is known not
to split. -/
theorem IsIrreducibleMorphism.isSplitMono_of_not_isSplitEpi (hf : IsIrreducibleMorphism f)
    {Z : C} {g : X ⟶ Z} {h : Z ⟶ Y} (hgh : g ≫ h = f) (hh : ¬ IsSplitEpi h) : IsSplitMono g :=
  (hf.factors g h hgh).resolve_right hh

/-- The form of `TauCeti.IsIrreducibleMorphism.factors` used when the first factor is known not to
split. -/
theorem IsIrreducibleMorphism.isSplitEpi_of_not_isSplitMono (hf : IsIrreducibleMorphism f)
    {Z : C} {g : X ⟶ Z} {h : Z ⟶ Y} (hgh : g ≫ h = f) (hg : ¬ IsSplitMono g) : IsSplitEpi h :=
  (hf.factors g h hgh).resolve_left hg

/-- **An irreducible morphism is not an isomorphism**, an isomorphism being a split mono. -/
theorem IsIrreducibleMorphism.not_isIso (hf : IsIrreducibleMorphism f) : ¬ IsIso f :=
  fun _ => hf.not_isSplitMono inferInstance

/-- An identity is not irreducible. -/
theorem not_isIrreducibleMorphism_id (X : C) : ¬ IsIrreducibleMorphism (𝟙 X) :=
  fun hf => hf.not_isIso inferInstance

/-! ### Invariance under isomorphisms of the source and the target -/

/-- **Postcomposing an irreducible morphism with an isomorphism keeps it irreducible.** -/
theorem IsIrreducibleMorphism.comp_iso (hf : IsIrreducibleMorphism f) {Y' : C} (e : Y ≅ Y') :
    IsIrreducibleMorphism (f ≫ e.hom) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_comp f e.hom),
    fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp_iso f e), fun Z g h hgh => ?_⟩
  have hgh' : g ≫ h ≫ e.inv = f := by rw [← Category.assoc, hgh, Category.assoc, e.hom_inv_id,
    Category.comp_id]
  rcases hf.factors g (h ≫ e.inv) hgh' with hsplit | hsplit
  · exact Or.inl hsplit
  · refine Or.inr ?_
    have hh : h = (h ≫ e.inv) ≫ e.hom := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [hh]
    infer_instance

/-- **Precomposing an irreducible morphism with an isomorphism keeps it irreducible.** -/
theorem IsIrreducibleMorphism.iso_comp (hf : IsIrreducibleMorphism f) {X' : C} (e : X' ≅ X) :
    IsIrreducibleMorphism (e.hom ≫ f) := by
  refine ⟨fun _ => hf.not_isSplitMono (isSplitMono_of_isSplitMono_iso_comp e f),
    fun _ => hf.not_isSplitEpi (isSplitEpi_of_isSplitEpi_comp e.hom f), fun Z g h hgh => ?_⟩
  have hgh' : (e.inv ≫ g) ≫ h = f := by rw [Category.assoc, hgh, ← Category.assoc, e.inv_hom_id,
    Category.id_comp]
  rcases hf.factors (e.inv ≫ g) h hgh' with hsplit | hsplit
  · refine Or.inl ?_
    have hg : g = e.hom ≫ e.inv ≫ g := by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    rw [hg]
    infer_instance
  · exact Or.inr hsplit

/-- Irreducibility is invariant under an isomorphism of the target. -/
theorem isIrreducibleMorphism_comp_iso_iff {Y' : C} (e : Y ≅ Y') :
    IsIrreducibleMorphism (f ≫ e.hom) ↔ IsIrreducibleMorphism f := by
  refine ⟨fun hf => ?_, fun hf => hf.comp_iso e⟩
  have h : (f ≫ e.hom) ≫ e.symm.hom = f := by
    rw [Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact h ▸ hf.comp_iso e.symm

/-- Irreducibility is invariant under an isomorphism of the source. -/
theorem isIrreducibleMorphism_iso_comp_iff {X' : C} (e : X' ≅ X) :
    IsIrreducibleMorphism (e.hom ≫ f) ↔ IsIrreducibleMorphism f := by
  refine ⟨fun hf => ?_, fun hf => hf.iso_comp e⟩
  have h : e.symm.hom ≫ e.hom ≫ f = f := by
    rw [Iso.symm_hom, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact h ▸ hf.iso_comp e.symm

/-! ### Zero morphisms -/

section Zero

variable [HasZeroMorphisms C]

/-- **A zero morphism is never irreducible.** It factors as `X --0--> X --0--> Y`, and neither
factor can split: if the first splits then `𝟙 X = 0`, which makes the zero morphism `X ⟶ Y` a
split mono; and the second factor *is* the morphism itself. Note that no zero object is needed —
the intermediate object is `X`. -/
theorem not_isIrreducibleMorphism_zero (X Y : C) : ¬ IsIrreducibleMorphism (0 : X ⟶ Y) := by
  intro hf
  rcases hf.factors (0 : X ⟶ X) (0 : X ⟶ Y) zero_comp with h | h
  · have hid : (0 : X ⟶ X) ≫ retraction (0 : X ⟶ X) = 𝟙 X := IsSplitMono.id _
    rw [zero_comp] at hid
    exact hf.not_isSplitMono (IsSplitMono.mk' ⟨0, by rw [zero_comp, hid]⟩)
  · exact hf.not_isSplitEpi h

/-- An irreducible morphism is nonzero. -/
theorem IsIrreducibleMorphism.ne_zero (hf : IsIrreducibleMorphism f) : f ≠ 0 :=
  fun h => not_isIrreducibleMorphism_zero X Y (h ▸ hf)

end Zero

/-! ### The monomorphism/epimorphism dichotomy -/

/-- **An irreducible morphism of a balanced category is not both a monomorphism and an
epimorphism**, since it would then be an isomorphism. -/
theorem IsIrreducibleMorphism.not_mono_and_epi [Balanced C] (hf : IsIrreducibleMorphism f) :
    ¬ (Mono f ∧ Epi f) := fun ⟨_, _⟩ => hf.not_isIso (isIso_of_mono_of_epi f)

/-- **An irreducible morphism of an abelian category is a monomorphism or an epimorphism.**

Apply the definition to the image factorization `f = e ≫ i`. If `e`, which is epi, is a split
mono, then it is an isomorphism and `f` is the composite of an isomorphism with the mono `i`. If
`i`, which is mono, is a split epi, then it is an isomorphism and `f` is the composite of the epi
`e` with an isomorphism. -/
theorem IsIrreducibleMorphism.mono_or_epi [Abelian C] (hf : IsIrreducibleMorphism f) :
    Mono f ∨ Epi f := by
  rcases hf.factors (factorThruImage f) (image.ι f) (image.fac f) with h | h
  · refine Or.inl ?_
    have : IsIso (factorThruImage f) := isIso_of_epi_of_isSplitMono _
    rw [← image.fac f]
    infer_instance
  · refine Or.inr ?_
    have : IsIso (image.ι f) := isIso_of_mono_of_isSplitEpi _
    rw [← image.fac f]
    infer_instance

/-- **The dichotomy**: an irreducible morphism of an abelian category is a monomorphism exactly
when it fails to be an epimorphism. -/
theorem IsIrreducibleMorphism.mono_iff_not_epi [Abelian C] (hf : IsIrreducibleMorphism f) :
    Mono f ↔ ¬ Epi f :=
  ⟨fun hm he => hf.not_mono_and_epi ⟨hm, he⟩, fun he => hf.mono_or_epi.resolve_right he⟩

/-- The other half of the dichotomy of `TauCeti.IsIrreducibleMorphism.mono_iff_not_epi`. -/
theorem IsIrreducibleMorphism.epi_iff_not_mono [Abelian C] (hf : IsIrreducibleMorphism f) :
    Epi f ↔ ¬ Mono f :=
  ⟨fun he hm => hf.not_mono_and_epi ⟨hm, he⟩, fun hm => hf.mono_or_epi.resolve_left hm⟩

end TauCeti
