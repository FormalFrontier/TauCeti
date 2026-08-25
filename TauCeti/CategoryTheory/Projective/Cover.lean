/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Essential epimorphisms and the uniqueness of a projective cover

A *projective cover* of an object `M` is an epimorphism `π : P ⟶ M` from a projective object which
is minimal, in the sense of being an **essential epimorphism**: a morphism `g` into `P` is an
epimorphism as soon as `g ≫ π` is one. That epimorphism condition is the definition used here —
`TauCeti.IsEssentialEpi` — and nothing beyond `[Category C]` is assumed for it. It is what makes
"the" projective cover well defined: two projective covers of the same object are isomorphic
over it.

The familiar reading of minimality, that no proper subobject of `P` already maps onto `M`, is
intuition rather than a restatement, and the two are not interchangeable. In a *balanced*
category, where a morphism that is both a monomorphism and an epimorphism is an isomorphism,
essentiality *implies* subobject-minimality: a subobject `m : P' ⟶ P` with `m ≫ π` an epimorphism
is an epimorphism by essentiality, hence an isomorphism. The converse needs more than
balancedness — an epimorphism–monomorphism factorization, to reduce an arbitrary `g : X ⟶ P` to
its image before applying minimality to that subobject — which module and representation
categories do have, so there the two conditions agree. In an arbitrary category they need not,
and it is the epimorphism condition, not the subobject one, that the results below use.

Mathlib has projective objects (`CategoryTheory.Projective`) and projective *presentations*
(`CategoryTheory.ProjectivePresentation`, an epimorphism from a projective with no minimality
demanded), but neither essential epimorphisms nor projective covers. The module-level notion is
`TauCeti.IsProjectiveCover` in `TauCeti.Algebra.Module.ProjectiveCover`, phrased through the
superfluousness of the kernel; `TauCeti.isProjectiveCover_iff_forall_surjective` shows that over an
additive group it is exactly the condition used here, so this file is the categorical reading of
the same notion, available in categories with no ambient kernel or subobject theory.

The uniqueness argument is short and needs no additivity, exactness, or subobjects — only the
lifting property of projectives and the fact that a split epimorphism whose section is an
epimorphism is an isomorphism (`CategoryTheory.IsIso.of_epi_section'`). Given two covers
`π : P ⟶ M` and `π' : P' ⟶ M`, lift `π` through `π'` to `h : P ⟶ P'`. Essentiality of `π'` makes
`h` an epimorphism, so projectivity of `P'` splits it: there is `σ : P' ⟶ P` with `σ ≫ h = 𝟙`.
That section satisfies `σ ≫ π = π'`, so essentiality of `π` makes `σ` an epimorphism too, and a
split epimorphism whose section is an epimorphism is an isomorphism.

## Main definitions

* `TauCeti.IsEssentialEpi`: `π` is an epimorphism, and every morphism into its source whose
  composite with `π` is an epimorphism is already one. An essential epimorphism from a projective
  object is a projective cover.

## Main results

* `TauCeti.IsEssentialEpi.isIso_of_comp_eq`: **rigidity** — any morphism between the sources of
  two projective covers of `M` that commutes with them is an isomorphism. Only the *target* of
  that morphism has to be projective.
* `TauCeti.IsEssentialEpi.exists_iso`: **uniqueness** — two projective covers of `M` are
  isomorphic by an isomorphism commuting with the covering morphisms.
* `TauCeti.IsEssentialEpi.exists_comp_eq_and_isSplitEpi`: **minimality** — every epimorphism onto
  `M` from a projective object factors through a projective cover by a *split* epimorphism, so the
  cover is a retract of every projective presentation of `M`.
* `TauCeti.IsEssentialEpi.isIso_of_isSplitEpi`: an essential epimorphism that splits is an
  isomorphism; hence `TauCeti.IsEssentialEpi.isIso_of_projective_target`, a projective object is
  its own projective cover.
* `TauCeti.IsEssentialEpi.comp` and `TauCeti.isEssentialEpi_of_isIso`: essential epimorphisms are
  closed under composition and contain the isomorphisms.

## Implementation notes

Nothing here uses a preadditive structure — every declaration assumes only `[Category C]`, with
projectivity entering as a hypothesis on individual objects — so the file is placed under
`TauCeti.CategoryTheory.Projective` rather than beside its import
`Mathlib.CategoryTheory.Preadditive.Projective.Basic`.

`IsEssentialEpi` carries `Epi π` as a field rather than as an instance argument, so that the
predicate is a single self-contained hypothesis that can be produced and consumed as a term. Its
second field takes the epimorphism hypothesis on the composite as an explicit argument for the
same reason.

## References

This supplies the "unique up to isomorphism" clause of the "projective covers and injective
envelopes" bullet of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, in the categorical form the
representation category needs.

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §17.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An **essential epimorphism** is an epimorphism `π : P ⟶ M` such that a morphism `g` into `P` is
an epimorphism as soon as `g ≫ π` is one. In a balanced category it implies that nothing smaller
than `P` already covers `M`; the converse implication needs in addition an epimorphism–monomorphism
factorization, as a module or representation category has. No subobject theory is assumed here.

An essential epimorphism from a projective object is a **projective cover**. Over a module
category this is exactly `TauCeti.IsProjectiveCover`, by
`TauCeti.isProjectiveCover_iff_forall_surjective`. -/
structure IsEssentialEpi {P M : C} (π : P ⟶ M) : Prop where
  /-- An essential epimorphism is in particular an epimorphism. -/
  epi : Epi π
  /-- A morphism into the source is an epimorphism as soon as its composite with `π` is one. -/
  epi_of_epi_comp {X : C} (g : X ⟶ P) : Epi (g ≫ π) → Epi g

/-- An isomorphism is an essential epimorphism: composing with it changes nothing. -/
theorem isEssentialEpi_of_isIso {P M : C} (f : P ⟶ M) [IsIso f] : IsEssentialEpi f where
  epi := inferInstance
  epi_of_epi_comp g hg := (epi_comp_iff_of_isIso g f).1 hg

namespace IsEssentialEpi

/-- Essential epimorphisms are closed under composition: if `π` and `τ` are both essential then a
morphism whose composite with `π ≫ τ` is an epimorphism is caught first by `τ`, then by `π`. -/
theorem comp {P M N : C} {π : P ⟶ M} {τ : M ⟶ N} (hπ : IsEssentialEpi π)
    (hτ : IsEssentialEpi τ) : IsEssentialEpi (π ≫ τ) where
  epi := by
    have := hπ.epi
    have := hτ.epi
    infer_instance
  epi_of_epi_comp g hg := by
    refine hπ.epi_of_epi_comp g (hτ.epi_of_epi_comp (g ≫ π) ?_)
    rwa [Category.assoc]

/-- **Rigidity of a projective cover.** If `π : P ⟶ M` and `π' : P' ⟶ M` are essential
epimorphisms with `P'` projective, then any `h : P ⟶ P'` over `M` is an isomorphism. Note that
only the *target* `P'` is required to be projective; taking `π' = π` this says that an endomorphism
of the source of a projective cover commuting with the cover is automatically an isomorphism. -/
theorem isIso_of_comp_eq {P P' M : C} [Projective P'] {π : P ⟶ M} {π' : P' ⟶ M}
    (hπ : IsEssentialEpi π) (hπ' : IsEssentialEpi π') {h : P ⟶ P'} (hh : h ≫ π' = π) :
    IsIso h := by
  have hepi : Epi h := hπ'.epi_of_epi_comp h (by rw [hh]; exact hπ.epi)
  -- Projectivity of `P'` splits the epimorphism `h`.
  obtain ⟨σ, hσh⟩ : ∃ σ : P' ⟶ P, σ ≫ h = 𝟙 P' :=
    ⟨Projective.factorThru (𝟙 P') h, Projective.factorThru_comp _ _⟩
  -- The section is itself a morphism over `M`, so essentiality of `π` makes it an epimorphism.
  have hσπ : σ ≫ π = π' := by rw [← hh, ← Category.assoc, hσh, Category.id_comp]
  have hepiσ : Epi σ := hπ.epi_of_epi_comp σ (by rw [hσπ]; exact hπ'.epi)
  exact IsIso.of_epi_section' ⟨σ, hσh⟩

/-- **The projective cover is unique.** Two essential epimorphisms onto `M` from projective
objects are related by an isomorphism of their sources commuting with them, so "the" projective
cover of `M` is well defined up to isomorphism over `M`. -/
theorem exists_iso {P P' M : C} [Projective P] [Projective P'] {π : P ⟶ M} {π' : P' ⟶ M}
    (hπ : IsEssentialEpi π) (hπ' : IsEssentialEpi π') : ∃ e : P ≅ P', e.hom ≫ π' = π := by
  have hepi := hπ'.epi
  have hcomp : Projective.factorThru π π' ≫ π' = π := Projective.factorThru_comp _ _
  have hiso : IsIso (Projective.factorThru π π') := hπ.isIso_of_comp_eq hπ' hcomp
  exact ⟨asIso (Projective.factorThru π π'), hcomp⟩

/-- **The projective cover is minimal.** Every epimorphism onto `M` from a projective object
factors through a projective cover of `M` by a *split* epimorphism, so the cover is a retract of
every projective presentation of `M`. (In an additive category a retract is a direct summand, but
nothing here needs additivity.) -/
theorem exists_comp_eq_and_isSplitEpi {P M : C} [Projective P] {π : P ⟶ M}
    (hπ : IsEssentialEpi π) {X : C} [Projective X] {f : X ⟶ M} (hf : Epi f) :
    ∃ g : X ⟶ P, g ≫ π = f ∧ IsSplitEpi g := by
  have hepi := hπ.epi
  refine ⟨Projective.factorThru f π, Projective.factorThru_comp _ _, ?_⟩
  have hg : Epi (Projective.factorThru f π) :=
    hπ.epi_of_epi_comp _ (by rw [Projective.factorThru_comp]; exact hf)
  exact IsSplitEpi.mk' ⟨Projective.factorThru (𝟙 P) (Projective.factorThru f π),
    Projective.factorThru_comp _ _⟩

/-- **An essential epimorphism that splits is an isomorphism.** Its composite with its section is
the identity, so essentiality makes that section an epimorphism, and a split epimorphism whose
section is an epimorphism is an isomorphism. -/
theorem isIso_of_isSplitEpi {P M : C} {π : P ⟶ M} (hπ : IsEssentialEpi π) [IsSplitEpi π] :
    IsIso π := by
  have hs : section_ π ≫ π = 𝟙 M := IsSplitEpi.id π
  have hepi : Epi (section_ π) := hπ.epi_of_epi_comp _ (by rw [hs]; infer_instance)
  exact IsIso.of_epi_section π

/-- **A projective object is its own projective cover.** An essential epimorphism onto a
projective object splits, hence is an isomorphism. -/
theorem isIso_of_projective_target {P M : C} [Projective M] {π : P ⟶ M}
    (hπ : IsEssentialEpi π) : IsIso π := by
  have hepi := hπ.epi
  have hsplit : IsSplitEpi π :=
    IsSplitEpi.mk' ⟨Projective.factorThru (𝟙 M) π, Projective.factorThru_comp _ _⟩
  exact hπ.isIso_of_isSplitEpi

end IsEssentialEpi

end TauCeti
