/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Module.ProjectiveCover.Existence
public import TauCeti.CategoryTheory.Projective.Cover

/-!
# Projective covers in `ModuleCat`

`TauCeti.IsProjectiveCover` is the module-level predicate — a surjection from a projective module
with superfluous kernel — and `TauCeti.IsEssentialEpi` is its categorical counterpart, an
epimorphism `π` such that every morphism `g` into its source with `g ≫ π` an epimorphism is itself
one. This file is the bridge between the two over `ModuleCat`: a linear map that is a projective
cover is an essential epimorphism of `ModuleCat` from a projective object, and conversely
(`TauCeti.isProjectiveCover_iff_projective_and_isEssentialEpi`), so the existence theorem of
`TauCeti/Algebra/Module/ProjectiveCover/Existence.lean` reads as a statement about objects of
`ModuleCat`.

The two translations used are Mathlib's: an epimorphism of `ModuleCat` is a surjection
(`ModuleCat.epi_iff_surjective`), and a projective object of `ModuleCat` is a projective module
(`IsProjective.iff_projective`). The module-level content of essentiality is
`TauCeti.isProjectiveCover_iff_forall_surjective`.

The covering module produced here is a submodule of a free module on the underlying set of the
module covered, so it lives in the same universe as that module; this is why the statements below
fix a single universe for the ring and the category.

## Main results

* `TauCeti.IsProjectiveCover.isEssentialEpi`: a module-level projective cover is an essential
  epimorphism of `ModuleCat`.
* `TauCeti.isProjectiveCover_iff_projective_and_isEssentialEpi`: the two readings agree — a
  morphism of `ModuleCat` is a projective cover of modules exactly when its source is a projective
  object and it is an essential epimorphism.
* `TauCeti.exists_essentialEpi_projective`: **every object of `ModuleCat R` over a semiprimary ring
  receives an essential epimorphism from a projective object.**
* `TauCeti.exists_projectiveCover`: the same for a module over a finite-dimensional algebra, with
  the two clauses of essentiality written out.

## References

See I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, Section I.5.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

section Bridge

variable {R : Type u} [Ring R] {P M : ModuleCat.{v} R}

/-- **A projective cover of modules is an essential epimorphism.** The two conditions agree over
`ModuleCat`: surjectivity is `Epi` and the minimality of a superfluous kernel is exactly the
essentiality clause, by `TauCeti.isProjectiveCover_iff_forall_surjective`. -/
theorem IsProjectiveCover.isEssentialEpi {π : P ⟶ M} (h : IsProjectiveCover π.hom) :
    IsEssentialEpi π where
  epi := (ModuleCat.epi_iff_surjective π).mpr h.surjective
  epi_of_epi_comp g hg := by
    have : Module.Projective R P := h.projective
    rw [ModuleCat.epi_iff_surjective] at hg ⊢
    refine (isProjectiveCover_iff_forall_surjective h.surjective).mp h g.hom ?_
    simpa [ModuleCat.hom_comp] using hg

/-- A projective cover of modules has a projective source, read in `ModuleCat`. -/
theorem IsProjectiveCover.projective_obj {π : P ⟶ M} (h : IsProjectiveCover π.hom) :
    Projective P :=
  have : Module.Projective R P := h.projective
  inferInstance

/-- **The two readings of a projective cover agree.** A morphism of `ModuleCat` is a projective
cover of modules exactly when its source is a projective object and it is an essential
epimorphism. The backward direction recovers the module-level API — surjectivity and a superfluous
kernel — from the categorical data: a map into the source is tested through its range, a submodule
of the source and so again an object of `ModuleCat`. -/
theorem isProjectiveCover_iff_projective_and_isEssentialEpi [Small.{v} R] {π : P ⟶ M} :
    IsProjectiveCover π.hom ↔ Projective P ∧ IsEssentialEpi π := by
  refine ⟨fun h => ⟨h.projective_obj, h.isEssentialEpi⟩, fun ⟨hP, hπ⟩ => ?_⟩
  have hmod : Module.Projective R P := (IsProjective.iff_projective (R := R) ↥P).mpr hP
  have hsurj : Function.Surjective π.hom := (ModuleCat.epi_iff_surjective π).mp hπ.epi
  refine (isProjectiveCover_iff_forall_surjective hsurj).mpr fun {P'} _ _ h hcomp => ?_
  -- The range of `h` is a submodule of `P`, so essentiality applies to its inclusion.
  have hrange : Function.Surjective (π.hom ∘ₗ (LinearMap.range h).subtype) := fun y => by
    obtain ⟨x, hx⟩ := hcomp y
    exact ⟨⟨h x, LinearMap.mem_range_self h x⟩, hx⟩
  have hepi : Epi (ModuleCat.ofHom (LinearMap.range h).subtype ≫ π) := by
    rw [ModuleCat.epi_iff_surjective]
    simpa [ModuleCat.hom_comp] using hrange
  have hsub : Function.Surjective (LinearMap.range h).subtype :=
    (ModuleCat.epi_iff_surjective _).mp (hπ.epi_of_epi_comp _ hepi)
  rw [← LinearMap.range_eq_top]
  exact (Submodule.range_subtype _).symm.trans (LinearMap.range_eq_top.mpr hsub)

end Bridge

section Existence

/-- **Every object of `ModuleCat R` over a semiprimary ring has a projective cover**: it receives
an essential epimorphism from a projective object. Unfolding `TauCeti.IsEssentialEpi`, this says
that `π` is an epimorphism and that every `i : X ⟶ P` with `i ≫ π` an epimorphism is one. -/
theorem exists_essentialEpi_projective (R : Type u) [Ring R] [IsSemiprimaryRing R]
    (M : ModuleCat.{u} R) :
    ∃ (P : ModuleCat.{u} R) (π : P ⟶ M), Projective P ∧ IsEssentialEpi π := by
  obtain ⟨P, hP⟩ := exists_isProjectiveCover R (↥M)
  -- The cover of the underlying module, read as a morphism of `ModuleCat` onto `M`.
  have hcov : IsProjectiveCover
      ((ModuleCat.ofHom (Finsupp.linearCombination R id ∘ₗ P.subtype) :
        ModuleCat.of R ↥P ⟶ M)).hom := by
    rwa [ModuleCat.hom_ofHom]
  exact ⟨_, _, hcov.projective_obj, hcov.isEssentialEpi⟩

/-- **Every object of `ModuleCat A` over a finite-dimensional algebra `A` has a projective
cover.** A finite-dimensional algebra is an Artinian ring, hence semiprimary, so this is
`TauCeti.exists_essentialEpi_projective` read through that instance; no finiteness is required of
the module. Essentiality is spelled out here as its two clauses, so that the statement is usable
without unfolding `TauCeti.IsEssentialEpi`. -/
theorem exists_projectiveCover {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A]
    [FiniteDimensional k A] (M : ModuleCat.{u} A) :
    ∃ (P : ModuleCat.{u} A) (π : P ⟶ M), Projective P ∧ Epi π ∧
      ∀ (X : ModuleCat.{u} A) (i : X ⟶ P), Epi (i ≫ π) → Epi i := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨P, π, hP, hπ⟩ := exists_essentialEpi_projective A M
  exact ⟨P, π, hP, hπ.epi, fun _ i => hπ.epi_of_epi_comp i⟩

end Existence

end TauCeti
