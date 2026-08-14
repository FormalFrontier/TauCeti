/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.KernelCokernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

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
* `TauCeti.ConflationClass.IsInflation` and `TauCeti.ConflationClass.IsDeflation` say that a
  morphism occurs as the first or second map of a conflation.
* `TauCeti.ExactStructure` equips a conflation class with E0/E0op, E1/E1op, and E2/E2op.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Definition 2.1 and Remarks 2.2--2.8 give the axioms used
  here.
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
  Conflation : ShortComplex C → Prop
  /-- Every conflation is a kernel--cokernel pair. -/
  isKernelCokernelPair : ∀ S, Conflation S → IsKernelCokernelPair S
  /-- The class of conflations is closed under isomorphisms of short complexes. -/
  conflation_iff_of_iso : ∀ {S T : ShortComplex C}, (S ≅ T) → (Conflation S ↔ Conflation T)

namespace ConflationClass

/-- Two conflation classes are equal when they distinguish the same short complexes. -/
@[ext]
theorem ext (E F : ConflationClass C) (h : ∀ S, E.Conflation S ↔ F.Conflation S) : E = F := by
  cases E
  cases F
  simp only [mk.injEq]
  funext S
  exact propext (h S)

/-- A morphism is an inflation when it is the first map of a conflation. -/
def IsInflation (E : ConflationClass C) {X Y : C} (i : X ⟶ Y) : Prop :=
  ∃ (Z : C) (p : Y ⟶ Z) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero)

/-- A morphism is a deflation when it is the second map of a conflation. -/
def IsDeflation (E : ConflationClass C) {Y Z : C} (p : Y ⟶ Z) : Prop :=
  ∃ (X : C) (i : X ⟶ Y) (zero : i ≫ p = 0), E.Conflation (ShortComplex.mk i p zero)

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
  (E.conflation_iff_of_iso e).mp hS

end ConflationClass

/-- A Quillen exact structure on an additive category, in the self-dual E0/E1/E2
presentation.

The E2 fields provide genuine universal squares. No ambient pushouts or pullbacks are assumed. -/
structure ExactStructure (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] extends ConflationClass C where
  /-- E0: identity morphisms are inflations. -/
  id_isInflation : ∀ X : C, toConflationClass.IsInflation (𝟙 X)
  /-- E0op: identity morphisms are deflations. -/
  id_isDeflation : ∀ X : C, toConflationClass.IsDeflation (𝟙 X)
  /-- E1: a composite of inflations is an inflation. -/
  comp_isInflation : ∀ {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z),
    toConflationClass.IsInflation i → toConflationClass.IsInflation j →
      toConflationClass.IsInflation (i ≫ j)
  /-- E1op: a composite of deflations is a deflation. -/
  comp_isDeflation : ∀ {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z),
    toConflationClass.IsDeflation p → toConflationClass.IsDeflation q →
      toConflationClass.IsDeflation (p ≫ q)
  /-- E2: the pushout of an inflation along any morphism exists, and its other leg is an
  inflation. -/
  pushout_isInflation : ∀ {X Y : C} (i : X ⟶ Y), toConflationClass.IsInflation i →
    ∀ {X' : C} (f : X ⟶ X'), ∃ (Y' : C) (g : Y ⟶ Y') (i' : X' ⟶ Y'),
      IsPushout i f g i' ∧ toConflationClass.IsInflation i'
  /-- E2op: the pullback of a deflation along any morphism exists, and its other leg is a
  deflation. -/
  pullback_isDeflation : ∀ {X Y : C} (p : X ⟶ Y), toConflationClass.IsDeflation p →
    ∀ {Y' : C} (f : Y' ⟶ Y), ∃ (X' : C) (p' : X' ⟶ Y') (g : X' ⟶ X),
      IsPullback p' g f p ∧ toConflationClass.IsDeflation p'

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

/-- A conflation's first map is an inflation. -/
theorem isInflation_f (E : ExactStructure C) {S : ShortComplex C} (hS : E.Conflation S) :
    E.IsInflation S.f :=
  E.toConflationClass.isInflation_f hS

/-- A conflation's second map is a deflation. -/
theorem isDeflation_g (E : ExactStructure C) {S : ShortComplex C} (hS : E.Conflation S) :
    E.IsDeflation S.g :=
  E.toConflationClass.isDeflation_g hS

/-- Every inflation in an exact structure is a monomorphism. -/
theorem IsInflation.mono {E : ExactStructure C} {X Y : C} {i : X ⟶ Y}
    (hi : E.IsInflation i) : Mono i :=
  ConflationClass.IsInflation.mono hi

/-- Every deflation in an exact structure is an epimorphism. -/
theorem IsDeflation.epi {E : ExactStructure C} {Y Z : C} {p : Y ⟶ Z}
    (hp : E.IsDeflation p) : Epi p :=
  ConflationClass.IsDeflation.epi hp

/-- An isomorphism of short complexes transports distinguished conflations. -/
theorem conflation_of_iso (E : ExactStructure C) {S T : ShortComplex C} (e : S ≅ T)
    (hS : E.Conflation S) : E.Conflation T :=
  E.toConflationClass.conflation_of_iso e hS

end ExactStructure

end TauCeti
