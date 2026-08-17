/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Simple objects of `Rep k G` and `FDRep k G`

Two notions of "irreducible representation" coexist. `Representation.IsIrreducible ρ` says that the
lattice of subrepresentations of `ρ` has exactly two elements, and it is the notion in which the
representation-theoretic arguments of this repository are phrased.
`CategoryTheory.Simple X` says that every monomorphism into the object `X` is either zero or an
isomorphism, and it is the notion in which the categorical machinery is phrased -- Schur's lemma
`FDRep.finrank_hom_simple_simple`, the characters of simple objects, semisimple categories. Neither
Mathlib nor this repository related the two, and several files here say so and stop at the
`Representation` level. This file supplies the dictionary.

Over `Rep k G` the dictionary is bookkeeping. `Rep k G` is equivalent to the category of
`k[G]`-modules (`Rep.equivalenceModuleMonoidAlgebra`), an equivalence transports simplicity in both
directions, and a module is a simple object exactly when it is a simple module
(`simple_iff_isSimpleModule`).

`FDRep k G` is not known to be equivalent to a module category, so it needs an argument in each
direction. One is formal: the forgetful functor to `Rep k G` is faithful, preserves zero morphisms
and monomorphisms, and reflects isomorphisms, and such a functor reflects simplicity
(`CategoryTheory.Functor.simple_of_simple_obj`). The other uses finite-dimensionality, and is where
the restriction to `FDRep` earns its keep: a subrepresentation of a finite-dimensional
representation is again finite-dimensional, so it is again an object of `FDRep k G`, and its
inclusion is a monomorphism which is nonzero exactly when the subrepresentation is nonzero and an
isomorphism exactly when the subrepresentation is everything. Simplicity of the object therefore
says precisely that the lattice of subrepresentations is `{⊥, ⊤}` with `⊥ ≠ ⊤`.

Both equivalences are also supplied as instances in each direction, so a statement proved in one
language applies in the other without a rewrite. The type of isomorphism classes of simple objects
that a categorical classification statement is valued in is `TauCeti.SimpleFDRepClasses`, in
`TauCeti.RepresentationTheory.Simple.FDRepClasses`; it is Mathlib's `CategoryTheory.Skeleton` of
the full subcategory of simple objects.

## Main results

* `TauCeti.Rep.simple_iff_isIrreducible`: an object of `Rep k G` is simple exactly when the
  representation it carries is irreducible.
* `TauCeti.FDRep.simple_iff_isIrreducible`: the same for `FDRep k G`.
-/

public section

open CategoryTheory

open scoped MonoidAlgebra

universe u v w

/-- **An object of `Rep k G` is simple exactly when the representation it carries is
irreducible.** Both sides say that the `k[G]`-module the object carries is simple: the left-hand
side across `Rep.equivalenceModuleMonoidAlgebra`, the right-hand side across
`Representation.irreducible_iff_isSimpleModule_asModule`. -/
theorem Rep.simple_iff_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) : Simple A ↔ Representation.IsIrreducible A.ρ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    ← simple_iff_isSimpleModule (R := k[G]) (M := A.ρ.asModule)]
  exact (simple_obj_iff (Rep.toModuleMonoidAlgebra (k := k) (G := G)) A).symm

instance Rep.simple_of_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) [Representation.IsIrreducible A.ρ] : Simple A :=
  (Rep.simple_iff_isIrreducible A).mpr ‹_›

instance Rep.isIrreducible_of_simple {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) [Simple A] : Representation.IsIrreducible A.ρ :=
  (Rep.simple_iff_isIrreducible A).mp ‹_›

section FDRep

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

section Inclusion

variable {V : Type u} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  (W : Subrepresentation ρ)

/-- The inclusion of a subrepresentation is a monomorphism of `Rep k G`, being injective. -/
private theorem mono_repOfHom_subtype : Mono (Rep.ofHom W.subtype) :=
  (Rep.mono_iff_injective _).mpr fun _ _ hab => Subtype.ext (by simpa using hab)

/-- The inclusion of a subrepresentation is the zero morphism of `Rep k G` exactly when the
subrepresentation is zero. -/
private theorem repOfHom_subtype_eq_zero_iff : Rep.ofHom W.subtype = 0 ↔ W = ⊥ := by
  constructor
  · intro h
    have hzero : W.subtype = 0 := by simpa using congrArg Rep.Hom.hom h
    refine Subrepresentation.toSubmodule_injective ?_
    rw [Subrepresentation.toSubmodule_bot, Submodule.eq_bot_iff]
    intro x hx
    simpa using DFunLike.congr_fun hzero (⟨x, hx⟩ : W.toSubmodule)
  · rintro rfl
    have hzero : (⊥ : Subrepresentation ρ).subtype = 0 := by
      ext x
      simp only [Subrepresentation.toLinearMap_subtype, Submodule.subtype_apply,
        Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
      exact (Submodule.mem_bot k).mp x.2
    rw [hzero, Rep.ofHom_zero]

/-- The inclusion of a subrepresentation is an epimorphism of `Rep k G` exactly when the
subrepresentation is everything. -/
private theorem epi_repOfHom_subtype_iff : Epi (Rep.ofHom W.subtype) ↔ W = ⊤ := by
  rw [Rep.epi_iff_surjective]
  constructor
  · intro hsurj
    have hrange : W.subtype.toLinearMap.range = ⊤ :=
      LinearMap.range_eq_top.mpr (by simpa using hsurj)
    rw [Subrepresentation.toLinearMap_subtype, Submodule.range_subtype] at hrange
    exact Subrepresentation.toSubmodule_injective
      (hrange.trans Subrepresentation.toSubmodule_top.symm)
  · rintro rfl
    intro y
    have hy : y ∈ (⊤ : Subrepresentation ρ).toSubmodule := by
      rw [Subrepresentation.toSubmodule_top]; exact Submodule.mem_top
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [Rep.hom_ofHom, Subrepresentation.coe_subtype]

end Inclusion

/-- The inclusion of a subrepresentation of a finite-dimensional representation, as a morphism of
`FDRep k G`: the monomorphism whose behaviour witnesses simplicity of the object. Its image in
`Rep k G` is `Rep.ofHom W.subtype`, which is where its properties are read off. -/
private noncomputable def subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    FDRep.of W.toRepresentation ⟶ X :=
  (forget₂ (FDRep k G) (Rep k G)).preimage (Rep.ofHom W.subtype)

private theorem map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    (forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W) = Rep.ofHom W.subtype :=
  (forget₂ (FDRep k G) (Rep k G)).map_preimage _

private theorem mono_map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    Mono ((forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W)) := by
  rw [map_subInclusion]
  exact mono_repOfHom_subtype W

private instance (X : FDRep k G) (W : Subrepresentation X.ρ) : Mono (subInclusion X W) :=
  (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (mono_map_subInclusion X W)

/-- The inclusion of a subrepresentation is the zero morphism exactly when the subrepresentation is
zero. -/
private theorem subInclusion_eq_zero_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    subInclusion X W = 0 ↔ W = ⊥ := by
  rw [← (forget₂ (FDRep k G) (Rep k G)).map_eq_zero_iff, map_subInclusion]
  exact repOfHom_subtype_eq_zero_iff W

/-- The inclusion of a subrepresentation is an isomorphism exactly when the subrepresentation is
everything. -/
private theorem isIso_subInclusion_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    IsIso (subInclusion X W) ↔ W = ⊤ := by
  constructor
  · intro h
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W)) := inferInstance
    rw [map_subInclusion] at hepi
    have hepi' : Epi (Rep.ofHom W.subtype) := hepi
    exact (epi_repOfHom_subtype_iff W).mp hepi'
  · rintro rfl
    have hmono := mono_map_subInclusion X (⊤ : Subrepresentation X.ρ)
    have hepi : Epi ((forget₂ (FDRep k G) (Rep k G)).map
        (subInclusion X (⊤ : Subrepresentation X.ρ))) := by
      rw [map_subInclusion]
      exact (epi_repOfHom_subtype_iff _).mpr rfl
    have : IsIso ((forget₂ (FDRep k G) (Rep k G)).map
        (subInclusion X (⊤ : Subrepresentation X.ρ))) := isIso_of_mono_of_epi _
    exact isIso_of_reflects_iso _ (forget₂ (FDRep k G) (Rep k G))

/-- **An object of `FDRep k G` is simple exactly when the representation it carries is
irreducible.** -/
theorem FDRep.simple_iff_isIrreducible (X : FDRep k G) :
    Simple X ↔ Representation.IsIrreducible X.ρ := by
  constructor
  · intro _
    -- A subrepresentation is everything exactly when it is nonzero: this is simplicity of `X`,
    -- read through the inclusion of the subrepresentation.
    have key : ∀ W : Subrepresentation X.ρ, W = ⊤ ↔ ¬W = ⊥ := fun W => by
      rw [← isIso_subInclusion_iff, ← subInclusion_eq_zero_iff]
      exact Simple.mono_isIso_iff_nonzero _
    have hbot : (⊥ : Subrepresentation X.ρ) ≠ ⊤ := fun h => (key ⊥).mp h rfl
    have : Nontrivial (Subrepresentation X.ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
    exact ⟨fun W => (em (W = ⊥)).imp id (key W).mpr⟩
  · intro _
    have : Simple ((forget₂ (FDRep k G) (Rep k G)).obj X) :=
      (Rep.simple_iff_isIrreducible _).mpr ‹_›
    exact Functor.simple_of_simple_obj (forget₂ (FDRep k G) (Rep k G)) X

instance FDRep.simple_of_isIrreducible (X : FDRep k G)
    [Representation.IsIrreducible X.ρ] : Simple X :=
  (FDRep.simple_iff_isIrreducible X).mpr ‹_›

instance FDRep.isIrreducible_of_simple (X : FDRep k G) [Simple X] :
    Representation.IsIrreducible X.ρ :=
  (FDRep.simple_iff_isIrreducible X).mp ‹_›

end FDRep
