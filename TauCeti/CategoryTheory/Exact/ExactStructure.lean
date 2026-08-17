/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.KernelCokernelPair
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Exact structures

An exact structure on an additive category is an isomorphism-closed class of kernel--cokernel
pairs satisfying Quillen's axioms. This file packages those axioms in their self-dual
E0/E1/E2 form. In particular, the E2 axioms return actual pushout and pullback squares; they do
not assume that the ambient category has arbitrary pushouts or pullbacks.

The distinguished short complexes are called *conflations*. Their first maps are
*inflations*, and their second maps are *deflations*. The structures here contain only this
intrinsic data and the six Quillen axioms. The split and canonical abelian exact structures are
constructed separately.

## Main definitions

* `TauCeti.ConflationClass` is an isomorphism-closed class of kernel--cokernel pairs.
* `TauCeti.ConflationClass.inflations` and `TauCeti.ConflationClass.deflations` are the
  `CategoryTheory.MorphismProperty` of morphisms occurring as the first, resp. second, map of a
  conflation. `TauCeti.ConflationClass.IsInflation` and `TauCeti.ConflationClass.IsDeflation`
  are the corresponding predicates on a single morphism.
* `TauCeti.ExactStructure` equips a conflation class with E0/E0op, E1/E1op, and E2/E2op.

## Implementation notes

The conflations are a `CategoryTheory.ObjectProperty (CategoryTheory.ShortComplex C)` closed
under isomorphisms in Mathlib's sense, and the inflations and the deflations are each a
`CategoryTheory.MorphismProperty`, so that the generic API applies: isomorphism-closure of the
conflations makes the inflations and the deflations
`CategoryTheory.MorphismProperty.RespectsIso`, and E0/E0op and E1/E1op are recorded as
`CategoryTheory.MorphismProperty.ContainsIdentities` and
`CategoryTheory.MorphismProperty.IsStableUnderComposition` instances. E2/E2op are recorded by
the corresponding property-specific `HasPushouts`/`HasPullbacks` and
`IsStableUnderCobaseChange`/`IsStableUnderBaseChange` classes. These assert existence only for
pushouts of inflations and pullbacks of deflations, without requiring arbitrary pushouts or
pullbacks in the ambient category.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Definition 2.1 and Remarks 2.2--2.8 give the axioms used
  here.
* `TauCetiRoadmap/GrothendieckEulerForms/Suggested.lean`, the human-authored roadmap
  formalization, fixes the design followed here: the `ConflationClass`/`ExactStructure`
  split, the E0/E0op, E1/E1op, E2/E2op fields, and the derived inflation and deflation
  predicates are its. This file replaces its bespoke `PushoutWitness` and `PullbackWitness`
  by Mathlib's property-specific pushout and pullback classes, and its pair of composable
  morphisms by a `CategoryTheory.ShortComplex`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An isomorphism-closed class of kernel--cokernel pairs in a preadditive category.

This is the relation underlying an exact structure, before imposing the Quillen axioms. -/
structure ConflationClass (C : Type u) [Category.{v} C] [Preadditive C] where
  /-- The distinguished short complexes. -/
  Conflation : ObjectProperty (ShortComplex C)
  /-- Every conflation is a kernel--cokernel pair. -/
  isKernelCokernelPair : ∀ S, Conflation S → IsKernelCokernelPair S
  /-- The class of conflations is closed under isomorphisms of short complexes. -/
  isClosedUnderIsomorphisms : Conflation.IsClosedUnderIsomorphisms

attribute [instance] ConflationClass.isClosedUnderIsomorphisms

namespace ConflationClass

/-- Two conflation classes are equal when they distinguish the same short complexes. -/
@[ext]
theorem ext (E F : ConflationClass C) (h : ∀ S, E.Conflation S ↔ F.Conflation S) : E = F := by
  cases E
  cases F
  simp only [mk.injEq]
  funext S
  exact propext (h S)

/-- The inflations: the morphisms occurring as the first map of a conflation. -/
def inflations (E : ConflationClass C) : MorphismProperty C :=
  fun _ Y i => ∃ (Z : C) (p : Y ⟶ Z) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero)

/-- The deflations: the morphisms occurring as the second map of a conflation. -/
def deflations (E : ConflationClass C) : MorphismProperty C :=
  fun Y _ p => ∃ (X : C) (i : X ⟶ Y) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero)

/-- A morphism is an inflation when it is the first map of a conflation. -/
abbrev IsInflation (E : ConflationClass C) {X Y : C} (i : X ⟶ Y) : Prop := E.inflations i

/-- A morphism is a deflation when it is the second map of a conflation. -/
abbrev IsDeflation (E : ConflationClass C) {Y Z : C} (p : Y ⟶ Z) : Prop := E.deflations p

/-- A morphism is an inflation exactly when it is the first map of a conflation. -/
theorem isInflation_iff (E : ConflationClass C) {X Y : C} (i : X ⟶ Y) :
    E.IsInflation i ↔
      ∃ (Z : C) (p : Y ⟶ Z) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero) :=
  Iff.rfl

/-- A morphism is a deflation exactly when it is the second map of a conflation. -/
theorem isDeflation_iff (E : ConflationClass C) {Y Z : C} (p : Y ⟶ Z) :
    E.IsDeflation p ↔
      ∃ (X : C) (i : X ⟶ Y) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero) :=
  Iff.rfl

/-- A conflation's first map is an inflation. -/
theorem isInflation_f (E : ConflationClass C) {S : ShortComplex C} (hS : E.Conflation S) :
    E.IsInflation S.f := by
  exact ⟨S.X₃, S.g, S.zero, hS⟩

/-- A conflation's second map is a deflation. -/
theorem isDeflation_g (E : ConflationClass C) {S : ShortComplex C} (hS : E.Conflation S) :
    E.IsDeflation S.g := by
  exact ⟨S.X₁, S.f, S.zero, hS⟩

/-- Every inflation is a monomorphism. -/
theorem IsInflation.mono {E : ConflationClass C} {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) : Mono i := by
  obtain ⟨Z, p, zero, hS⟩ := hi
  exact (E.isKernelCokernelPair (ShortComplex.mk i p zero) hS).mono_f

/-- Every deflation is an epimorphism. -/
theorem IsDeflation.epi {E : ConflationClass C} {Y Z : C} {p : Y ⟶ Z}
    (hp : E.IsDeflation p) : Epi p := by
  obtain ⟨X, i, zero, hS⟩ := hp
  exact (E.isKernelCokernelPair (ShortComplex.mk i p zero) hS).epi_g

/-- An isomorphism of short complexes transports the property of being a conflation. -/
theorem conflation_of_iso (E : ConflationClass C) {S T : ShortComplex C} (e : S ≅ T)
    (hS : E.Conflation S) : E.Conflation T :=
  E.Conflation.prop_of_iso e hS

/-- Isomorphic short complexes are conflations together. -/
theorem conflation_iff_of_iso (E : ConflationClass C) {S T : ShortComplex C} (e : S ≅ T) :
    E.Conflation S ↔ E.Conflation T :=
  E.Conflation.prop_iff_of_iso e

/-- A kernel–cokernel pair whose first map is an inflation is a conflation: the conflation
witnessing the inflation has the same cokernel, so the two short complexes are isomorphic. -/
theorem conflation_of_isKernelCokernelPair_of_isInflation (E : ConflationClass C)
    {S : ShortComplex C}
    (hS : IsKernelCokernelPair S) (hf : E.IsInflation S.f) : E.Conflation S := by
  obtain ⟨Z, q, hq, hT⟩ := (E.isInflation_iff _).mp hf
  let T := ShortComplex.mk S.f q hq
  have hT' : E.Conflation T := by simpa [T] using hT
  have hpairT : IsKernelCokernelPair T := E.isKernelCokernelPair T hT'
  let e : Z ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso hpairT.gIsCokernel hS.gIsCokernel
  have he : q ≫ e.hom = S.g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hpairT.gIsCokernel hS.gIsCokernel
      WalkingParallelPair.one
  exact E.conflation_of_iso (S := T) (T := S)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by simp [T]) (by simpa [T] using he.symm)) hT'

/-- A kernel–cokernel pair whose second map is a deflation is a conflation: the conflation
witnessing the deflation has the same kernel, so the two short complexes are isomorphic. -/
theorem conflation_of_isKernelCokernelPair_of_isDeflation (E : ConflationClass C)
    {S : ShortComplex C}
    (hS : IsKernelCokernelPair S) (hg : E.IsDeflation S.g) : E.Conflation S := by
  obtain ⟨X, i, hi, hT⟩ := (E.isDeflation_iff _).mp hg
  let T := ShortComplex.mk i S.g hi
  have hT' : E.Conflation T := by simpa [T] using hT
  have hpairT : IsKernelCokernelPair T := E.isKernelCokernelPair T hT'
  let e : X ≅ S.X₁ :=
    IsLimit.conePointUniqueUpToIso hpairT.fIsKernel hS.fIsKernel
  have he : e.hom ≫ S.f = i :=
    IsLimit.conePointUniqueUpToIso_hom_comp hpairT.fIsKernel hS.fIsKernel
      WalkingParallelPair.zero
  exact E.conflation_of_iso (S := T) (T := S)
    (ShortComplex.isoMk e (Iso.refl _) (Iso.refl _)
      (by simpa [T] using he) (by simp [T])) hT'

/-- Being an inflation is invariant under composing with isomorphisms on either side: the
witnessing conflation transports along the isomorphism. -/
instance (E : ConflationClass C) : E.inflations.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e i ⟨W, p, zero, hS⟩
    refine ⟨W, p, by simp [zero], E.conflation_of_iso (S := ShortComplex.mk i p zero)
      (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)) hS⟩
  · rintro X Y Z e i ⟨W, p, zero, hS⟩
    refine ⟨W, e.inv ≫ p, by simp [zero], E.conflation_of_iso (S := ShortComplex.mk i p zero)
      (ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) (by simp) (by simp)) hS⟩

/-- Being a deflation is invariant under composing with isomorphisms on either side: the
witnessing conflation transports along the isomorphism. -/
instance (E : ConflationClass C) : E.deflations.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e p ⟨W, i, zero, hS⟩
    refine ⟨W, i ≫ e.inv, by simp [zero], E.conflation_of_iso (S := ShortComplex.mk i p zero)
      (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)) hS⟩
  · rintro X Y Z e p ⟨W, i, zero, hS⟩
    refine ⟨W, i, by simp [reassoc_of% zero], E.conflation_of_iso (S := ShortComplex.mk i p zero)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp)) hS⟩

end ConflationClass

/-- A Quillen exact structure on an additive category, in the self-dual E0/E1/E2
presentation.

The E2 fields provide genuine universal squares through Mathlib's pushout and pullback APIs. No
ambient pushouts or pullbacks are assumed. -/
structure ExactStructure (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] extends ConflationClass C where
  /-- E0: identity morphisms are inflations. -/
  isInflation_id : ∀ X : C, toConflationClass.IsInflation (𝟙 X)
  /-- E0op: identity morphisms are deflations. -/
  isDeflation_id : ∀ X : C, toConflationClass.IsDeflation (𝟙 X)
  /-- E1: a composite of inflations is an inflation. -/
  isInflation_comp : ∀ {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z),
    toConflationClass.IsInflation i → toConflationClass.IsInflation j →
      toConflationClass.IsInflation (i ≫ j)
  /-- E1op: a composite of deflations is a deflation. -/
  isDeflation_comp : ∀ {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z),
    toConflationClass.IsDeflation p → toConflationClass.IsDeflation q →
      toConflationClass.IsDeflation (p ≫ q)
  /-- E2 existence: pushouts of inflations along arbitrary morphisms exist. -/
  hasPushouts_inflations : toConflationClass.inflations.HasPushouts
  /-- E2 stability: every cobase change of an inflation is an inflation. -/
  isStableUnderCobaseChange_inflations :
    toConflationClass.inflations.IsStableUnderCobaseChange
  /-- E2op existence: pullbacks of deflations along arbitrary morphisms exist. -/
  hasPullbacks_deflations : toConflationClass.deflations.HasPullbacks
  /-- E2op stability: every base change of a deflation is a deflation. -/
  isStableUnderBaseChange_deflations : toConflationClass.deflations.IsStableUnderBaseChange

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- Two exact structures are equal when they have the same conflations. -/
@[ext]
theorem ext (E F : ExactStructure C) (h : ∀ S, E.Conflation S ↔ F.Conflation S) : E = F := by
  cases E
  cases F
  simp only [mk.injEq]
  apply ConflationClass.ext
  exact h

/-- The predicate that a morphism is the first map of a distinguished conflation. -/
abbrev IsInflation (E : ExactStructure C) {X Y : C} (i : X ⟶ Y) : Prop :=
  E.toConflationClass.IsInflation i

/-- The predicate that a morphism is the second map of a distinguished conflation. -/
abbrev IsDeflation (E : ExactStructure C) {Y Z : C} (p : Y ⟶ Z) : Prop :=
  E.toConflationClass.IsDeflation p

/-- E0, as the statement that the inflations contain the identities. -/
instance (E : ExactStructure C) : E.inflations.ContainsIdentities where
  id_mem := E.isInflation_id

/-- E0op, as the statement that the deflations contain the identities. -/
instance (E : ExactStructure C) : E.deflations.ContainsIdentities where
  id_mem := E.isDeflation_id

/-- E1, as the statement that the inflations are stable under composition. -/
instance (E : ExactStructure C) : E.inflations.IsStableUnderComposition where
  comp_mem := E.isInflation_comp

/-- E1op, as the statement that the deflations are stable under composition. -/
instance (E : ExactStructure C) : E.deflations.IsStableUnderComposition where
  comp_mem := E.isDeflation_comp

/-- E2 existence, as property-specific availability of pushouts. -/
instance (E : ExactStructure C) : E.inflations.HasPushouts := E.hasPushouts_inflations

/-- E2 stability, as stability of inflations under cobase change. -/
instance (E : ExactStructure C) : E.inflations.IsStableUnderCobaseChange :=
  E.isStableUnderCobaseChange_inflations

/-- E2op existence, as property-specific availability of pullbacks. -/
instance (E : ExactStructure C) : E.deflations.HasPullbacks := E.hasPullbacks_deflations

/-- E2op stability, as stability of deflations under base change. -/
instance (E : ExactStructure C) : E.deflations.IsStableUnderBaseChange :=
  E.isStableUnderBaseChange_deflations

end ExactStructure

end TauCeti
