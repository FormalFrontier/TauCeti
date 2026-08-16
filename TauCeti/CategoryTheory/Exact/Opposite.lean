/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.ExactStructure

/-!
# Opposite exact structures

Every exact structure on an additive category induces an exact structure on the opposite
category. Its conflations are the opposites of the original conflations, so its inflations are
the opposites of the original deflations and its deflations are the opposites of the original
inflations.

This file develops the self-duality of the intrinsic Quillen axioms. Identity and composition
exchange their inflation and deflation forms, while pullbacks of deflations become pushouts of
inflations and conversely.

## Main definitions

* `TauCeti.ConflationClass.op`: the opposite of a conflation class.
* `TauCeti.ExactStructure.op`: the opposite of an exact structure.

## Main results

* `TauCeti.ConflationClass.op_inflations` and
  `TauCeti.ConflationClass.op_deflations` identify the two morphism properties under duality.
* `TauCeti.ExactStructure.op_conflation_op_iff` identifies the opposite conflations coming from
  an original short complex.
* `TauCeti.ExactStructure.op_isInflation_iff` and
  `TauCeti.ExactStructure.op_isDeflation_iff` exchange inflations and deflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Remarks 2.2--2.8 explain the self-duality of the exact
  category axioms.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ConflationClass

/-- The opposite of a conflation class. A short complex in `Cᵒᵖ` is distinguished exactly
when its un-opposite is distinguished in `C`. -/
def op (E : ConflationClass C) : ConflationClass Cᵒᵖ where
  Conflation S := E.Conflation S.unop
  isKernelCokernelPair S hS := isKernelCokernelPair_unop_iff.mp (E.isKernelCokernelPair S.unop hS)
  isClosedUnderIsomorphisms := ⟨by
    intro S T e hS
    let e' : S.unop ≅ T.unop := ((ShortComplex.unopFunctor C).mapIso e).unop.symm
    exact E.conflation_of_iso e' hS⟩

/-- A short complex is a conflation of the opposite class exactly when its un-opposite is a
conflation of the original class. -/
@[simp]
theorem op_conflation (E : ConflationClass C) (S : ShortComplex Cᵒᵖ) :
    E.op.Conflation S ↔ E.Conflation S.unop :=
  Iff.rfl

/-- Opposite conflations are precisely the opposites of the original conflations. -/
@[simp]
theorem op_conflation_op_iff (E : ConflationClass C) (S : ShortComplex C) :
    E.op.Conflation S.op ↔ E.Conflation S :=
  E.conflation_iff_of_iso S.opUnop

/-- The inflations of the opposite conflation class are the opposites of its deflations. -/
theorem op_inflations (E : ConflationClass C) : E.op.inflations = E.deflations.op := by
  ext X Y f
  constructor
  · intro hf
    obtain ⟨Z, p, zero, hS⟩ := (isInflation_iff E.op f).mp hf
    apply (isDeflation_iff E f.unop).mpr
    exact ⟨Z.unop, p.unop, by simpa using congrArg Quiver.Hom.unop zero,
      (op_conflation E _).mp hS⟩
  · intro hf
    obtain ⟨Z, p, zero, hS⟩ := (isDeflation_iff E f.unop).mp hf
    apply (isInflation_iff E.op f).mpr
    refine ⟨Opposite.op Z, p.op, by simpa using congrArg Quiver.Hom.op zero, ?_⟩
    exact (op_conflation E _).mpr
      (E.conflation_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
          (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])) hS)

/-- The deflations of the opposite conflation class are the opposites of its inflations. -/
theorem op_deflations (E : ConflationClass C) : E.op.deflations = E.inflations.op := by
  ext X Y f
  constructor
  · intro hf
    obtain ⟨Z, i, zero, hS⟩ := (isDeflation_iff E.op f).mp hf
    apply (isInflation_iff E f.unop).mpr
    exact ⟨Z.unop, i.unop, by simpa using congrArg Quiver.Hom.unop zero,
      (op_conflation E _).mp hS⟩
  · intro hf
    obtain ⟨Z, i, zero, hS⟩ := (isInflation_iff E f.unop).mp hf
    apply (isDeflation_iff E.op f).mpr
    refine ⟨Opposite.op Z, i.op, by simpa using congrArg Quiver.Hom.op zero, ?_⟩
    exact (op_conflation E _).mpr
      (E.conflation_of_iso
        (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
          (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])) hS)

/-- A morphism is an inflation in the opposite conflation class exactly when its un-opposite is
a deflation in the original class. -/
@[simp]
theorem op_isInflation_iff (E : ConflationClass C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.IsInflation f ↔ E.IsDeflation f.unop := by
  exact iff_of_eq (congrArg (fun P : MorphismProperty Cᵒᵖ => P f) E.op_inflations)

/-- A morphism is a deflation in the opposite conflation class exactly when its un-opposite is
an inflation in the original class. -/
@[simp]
theorem op_isDeflation_iff (E : ConflationClass C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.IsDeflation f ↔ E.IsInflation f.unop := by
  exact iff_of_eq (congrArg (fun P : MorphismProperty Cᵒᵖ => P f) E.op_deflations)

end ConflationClass

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-- The opposite exact structure. Its conflations are the short complexes whose un-opposites
are conflations of the original exact structure. -/
noncomputable def op (E : ExactStructure C) : ExactStructure Cᵒᵖ where
  toConflationClass := E.toConflationClass.op
  isInflation_id X := by
    rw [ConflationClass.op_isInflation_iff]
    simpa using E.isDeflation_id X.unop
  isDeflation_id X := by
    rw [ConflationClass.op_isDeflation_iff]
    simpa using E.isInflation_id X.unop
  isInflation_comp f g hf hg := by
    rw [ConflationClass.op_isInflation_iff] at hf hg ⊢
    simpa using E.isDeflation_comp g.unop f.unop hg hf
  isDeflation_comp f g hf hg := by
    rw [ConflationClass.op_isDeflation_iff] at hf hg ⊢
    simpa using E.isInflation_comp g.unop f.unop hg hf
  hasPushouts_inflations := by
    rw [ConflationClass.op_inflations]
    constructor
    intro X Y S f g hf
    simp only [MorphismProperty.op] at hf
    have := MorphismProperty.HasPullbacks.hasPullback g.unop hf
    simpa using (inferInstance : HasPushout f.unop.op g.unop.op)
  isStableUnderCobaseChange_inflations := by
    rw [ConflationClass.op_inflations]
    infer_instance
  hasPullbacks_deflations := by
    rw [ConflationClass.op_deflations]
    constructor
    intro X Y S f g hf
    simp only [MorphismProperty.op] at hf
    have := MorphismProperty.HasPushouts.hasPushout g.unop hf
    simpa using (inferInstance : HasPullback f.unop.op g.unop.op)
  isStableUnderBaseChange_deflations := by
    rw [ConflationClass.op_deflations]
    infer_instance

/-- A short complex is a conflation of the opposite exact structure exactly when its
un-opposite is a conflation of the original exact structure. -/
@[simp]
theorem op_conflation (E : ExactStructure C) (S : ShortComplex Cᵒᵖ) :
    E.op.Conflation S ↔ E.Conflation S.unop :=
  Iff.rfl

/-- The opposite of a conflation is a conflation in the opposite exact structure, and every
such opposite conflation arises this way. -/
@[simp]
theorem op_conflation_op_iff (E : ExactStructure C) (S : ShortComplex C) :
    E.op.Conflation S.op ↔ E.Conflation S :=
  E.toConflationClass.op_conflation_op_iff S

/-- The inflations of the opposite exact structure are the opposites of the original
deflations. -/
theorem op_inflations (E : ExactStructure C) : E.op.inflations = E.deflations.op :=
  E.toConflationClass.op_inflations

/-- The deflations of the opposite exact structure are the opposites of the original
inflations. -/
theorem op_deflations (E : ExactStructure C) : E.op.deflations = E.inflations.op :=
  E.toConflationClass.op_deflations

/-- A morphism is an inflation of the opposite exact structure exactly when its un-opposite is
a deflation of the original exact structure. -/
@[simp]
theorem op_isInflation_iff (E : ExactStructure C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.IsInflation f ↔ E.IsDeflation f.unop :=
  E.toConflationClass.op_isInflation_iff f

/-- A morphism is a deflation of the opposite exact structure exactly when its un-opposite is
an inflation of the original exact structure. -/
@[simp]
theorem op_isDeflation_iff (E : ExactStructure C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.IsDeflation f ↔ E.IsInflation f.unop :=
  E.toConflationClass.op_isDeflation_iff f

end ExactStructure

end TauCeti
