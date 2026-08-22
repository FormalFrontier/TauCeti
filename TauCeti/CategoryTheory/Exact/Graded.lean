/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Equivalence

/-!
# Graded exact categories

A *graded exact category* is a Quillen exact category equipped with a chosen internal grading
shift `{1}`: an autoequivalence of the underlying additive category which is an isomorphism of
exact categories, that is, whose functor and whose inverse are both conflation-exact.  The shift
is data, not a property, exactly as a pinning is: it is what gives the Grothendieck group of the
category its `ℤ`-action `[M] ↦ [M{1}]`.

Requiring the inverse to be conflation-exact is not automatic from requiring it of the functor.
An autoequivalence can enlarge the class of conflations strictly, in which case its inverse does
not induce the canonical inverse map on `K₀`.  The theorem
`TauCeti.ExactStructure.isConflationExact_inverse_iff_reflectsConflations`, proved alongside the
transport of exact structures, identifies the extra hypothesis with reflection of conflations,
which is the form in which it is usually checked.

## Main definitions

* `TauCeti.GradedExactStructure`: an exact structure together with a conflation-exact
  autoequivalence, the grading shift.
* `TauCeti.GradedExactStructure.split` and `TauCeti.GradedExactStructure.abelian`: the split
  exact structure and the canonical exact structure of an abelian category are graded by an
  arbitrary additive autoequivalence, no compatibility being needed in either case.
* `TauCeti.GradedConflationExact`: a graded conflation-exact functor, namely a conflation-exact
  functor together with a chosen commutation isomorphism with the two grading shifts.
* `TauCeti.GradedExactEquiv`: a graded exact equivalence, namely an equivalence whose functor and
  whose inverse are conflation-exact, carrying such a commutation isomorphism.

## Main results

* `TauCeti.GradedExactStructure.conflation_shift_iff`: a short complex is a conflation exactly
  when its shift is.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Section 2, for the exact structures which the grading shift
  is required here to preserve and to reflect.
* `TauCetiRoadmap/GrothendieckEulerForms/README.md`, Layer 2, which fixes the normalization
  `[M{1}] = q[M]` used downstream and requires the shift to be part of the data of a graded
  exact category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A **graded exact structure** on an additive category: a Quillen exact structure together with
a chosen autoequivalence `{1}`, the *grading shift*, whose functor and whose inverse both preserve
the distinguished conflations.

The shift is data.  Conflation-exactness of both directions supplies mutually inverse maps on
Grothendieck groups induced by the shift and its inverse; see
`TauCeti.ExactStructure.isConflationExact_inverse_iff_reflectsConflations` for the reformulation
of the second hypothesis as reflection of conflations. -/
structure GradedExactStructure (C : Type u₁) [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] extends ExactStructure C where
  /-- The grading shift `{1}`, an autoequivalence of the underlying additive category. -/
  shift : C ≌ C
  /-- The grading shift is an additive functor. -/
  [shift_additive : shift.functor.Additive]
  /-- The grading shift preserves the distinguished conflations. -/
  shift_exact : toExactStructure.IsConflationExact toExactStructure shift.functor
  /-- The inverse grading shift preserves the distinguished conflations. -/
  shift_inverse_exact : toExactStructure.IsConflationExact toExactStructure shift.inverse

attribute [instance] GradedExactStructure.shift_additive

namespace GradedExactStructure

section Basic

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : GradedExactStructure C)

/-- The grading shift of a graded exact structure reflects conflations. -/
theorem shift_reflectsConflations :
    E.toExactStructure.ReflectsConflations E.toExactStructure E.shift.functor :=
  ExactStructure.reflectsConflations_of_isConflationExact_inverse E.shift E.shift_inverse_exact

/-- The inverse grading shift of a graded exact structure reflects conflations. -/
theorem shift_inverse_reflectsConflations :
    E.toExactStructure.ReflectsConflations E.toExactStructure E.shift.inverse := by
  have : E.shift.symm.functor.Additive := inferInstanceAs E.shift.inverse.Additive
  exact ExactStructure.reflectsConflations_of_isConflationExact_inverse E.shift.symm E.shift_exact

/-- **A short complex is a conflation exactly when its shift is.**  This is the precise sense in
which the grading shift is an isomorphism of exact categories. -/
@[simp]
theorem conflation_shift_iff (S : ShortComplex C) :
    E.toExactStructure.Conflation (S.map E.shift.functor) ↔ E.toExactStructure.Conflation S :=
  ExactStructure.conflation_map_iff E.shift_exact E.shift_reflectsConflations S

/-- A short complex is a conflation exactly when its inverse shift is. -/
@[simp]
theorem conflation_shift_inverse_iff (S : ShortComplex C) :
    E.toExactStructure.Conflation (S.map E.shift.inverse) ↔ E.toExactStructure.Conflation S :=
  ExactStructure.conflation_map_iff E.shift_inverse_exact E.shift_inverse_reflectsConflations S

end Basic

section Construct

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- Build a graded exact structure from a shift which both preserves and reflects conflations.
This is the form in which the hypothesis is usually available. -/
def ofReflects (E : ExactStructure C) (e : C ≌ C) [e.functor.Additive]
    (he : E.IsConflationExact E e.functor) (hr : E.ReflectsConflations E e.functor) :
    GradedExactStructure C where
  toExactStructure := E
  shift := e
  shift_exact := he
  shift_inverse_exact := ExactStructure.isConflationExact_inverse_of_reflectsConflations e hr

@[simp]
theorem ofReflects_toExactStructure (E : ExactStructure C) (e : C ≌ C) [e.functor.Additive]
    (he : E.IsConflationExact E e.functor) (hr : E.ReflectsConflations E e.functor) :
    (ofReflects E e he hr).toExactStructure = E :=
  -- `(rfl)` rather than `rfl`: a bare `rfl` proof would demand that `ofReflects` be `@[expose]`,
  -- and the projection lemmas are the supported interface instead.
  (rfl)

@[simp]
theorem ofReflects_shift (E : ExactStructure C) (e : C ≌ C) [e.functor.Additive]
    (he : E.IsConflationExact E e.functor) (hr : E.ReflectsConflations E e.functor) :
    (ofReflects E e he hr).shift = e :=
  (rfl)

variable (C) in
/-- The split exact structure, graded by an arbitrary additive autoequivalence: every additive
functor preserves split conflations, so no compatibility between the shift and the exact
structure has to be checked. -/
noncomputable def split (e : C ≌ C) [e.functor.Additive] : GradedExactStructure C where
  toExactStructure := ExactStructure.split C
  shift := e
  shift_exact := ExactStructure.isConflationExact_split e.functor
  shift_inverse_exact := ExactStructure.isConflationExact_split e.inverse

@[simp]
theorem split_toExactStructure (e : C ≌ C) [e.functor.Additive] :
    (split C e).toExactStructure = ExactStructure.split C :=
  (rfl)

@[simp]
theorem split_shift (e : C ≌ C) [e.functor.Additive] : (split C e).shift = e :=
  (rfl)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

variable (A) in
/-- The canonical exact structure of an abelian category, graded by an arbitrary additive
autoequivalence: an equivalence preserves all finite limits and colimits, so again no
compatibility has to be checked. -/
noncomputable def abelian (e : A ≌ A) [e.functor.Additive] : GradedExactStructure A where
  toExactStructure := ExactStructure.abelian A
  shift := e
  shift_exact := ExactStructure.isConflationExact_abelian e.functor
  shift_inverse_exact := ExactStructure.isConflationExact_abelian e.inverse

@[simp]
theorem abelian_toExactStructure (e : A ≌ A) [e.functor.Additive] :
    (abelian A e).toExactStructure = ExactStructure.abelian A :=
  (rfl)

@[simp]
theorem abelian_shift (e : A ≌ A) [e.functor.Additive] : (abelian A e).shift = e :=
  (rfl)

end Construct

end GradedExactStructure

/-- A **graded conflation-exact functor** between graded exact categories: a conflation-exact
functor together with a chosen isomorphism commuting it with the two grading shifts.

The commutation isomorphism is data rather than a property, since the induced `ℤ`-equivariance of
the map on Grothendieck groups is proved from it. -/
structure GradedConflationExact {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
    (E : GradedExactStructure C) (E' : GradedExactStructure D) (F : C ⥤ D) [F.Additive] where
  /-- The underlying functor is conflation-exact. -/
  isConflationExact : E.toExactStructure.IsConflationExact E'.toExactStructure F
  /-- The chosen isomorphism commuting the functor with the two grading shifts. -/
  commShift : E.shift.functor ⋙ F ≅ F ⋙ E'.shift.functor

namespace GradedConflationExact

variable {C : Type u₁} {D : Type u₂} {K : Type u₃}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable [Category.{v₃} K] [Preadditive K] [HasZeroObject K] [HasBinaryBiproducts K]
variable {E : GradedExactStructure C} {E' : GradedExactStructure D} {E'' : GradedExactStructure K}

/-- The identity functor is graded conflation-exact. -/
protected def id (E : GradedExactStructure C) : GradedConflationExact E E (𝟭 C) where
  isConflationExact := ExactStructure.IsConflationExact.id
  commShift := (Functor.rightUnitor _) ≪≫ (Functor.leftUnitor _).symm

/-- The shift-commutation isomorphism of the identity graded conflation-exact functor. -/
@[simp]
theorem id_commShift (E : GradedExactStructure C) :
    (GradedConflationExact.id E).commShift =
      (Functor.rightUnitor _) ≪≫ (Functor.leftUnitor _).symm :=
  (rfl)

/-- A composite of graded conflation-exact functors is graded conflation-exact, for the composed
commutation isomorphism. -/
protected def comp {F : C ⥤ D} {H : D ⥤ K} [F.Additive] [H.Additive]
    (h : GradedConflationExact E E' F) (h' : GradedConflationExact E' E'' H) :
    GradedConflationExact E E'' (F ⋙ H) where
  isConflationExact := h.isConflationExact.comp h'.isConflationExact
  commShift :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h.commShift H ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F h'.commShift ≪≫
      (Functor.associator _ _ _).symm

/-- The shift-commutation isomorphism of a composite graded conflation-exact functor. -/
@[simp]
theorem comp_commShift {F : C ⥤ D} {H : D ⥤ K} [F.Additive] [H.Additive]
    (h : GradedConflationExact E E' F) (h' : GradedConflationExact E' E'' H) :
    (h.comp h').commShift =
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h.commShift H ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F h'.commShift ≪≫
        (Functor.associator _ _ _).symm :=
  (rfl)

end GradedConflationExact

/-- A **graded exact equivalence** between graded exact categories: an equivalence of the
underlying additive categories whose functor and whose inverse are both conflation-exact,
together with a chosen isomorphism commuting the functor with the two grading shifts.

Conflation-exactness of the inverse is again an extra hypothesis, for the reason recorded on
`TauCeti.GradedExactStructure`: it supplies the inverse map on Grothendieck groups induced by the
inverse functor. -/
structure GradedExactEquiv {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
    (E : GradedExactStructure C) (E' : GradedExactStructure D) where
  /-- The underlying equivalence of the additive categories. -/
  equiv : C ≌ D
  /-- The underlying equivalence is additive. -/
  [functor_additive : equiv.functor.Additive]
  /-- The equivalence is conflation-exact. -/
  isConflationExact : E.toExactStructure.IsConflationExact E'.toExactStructure equiv.functor
  /-- The inverse equivalence is conflation-exact. -/
  inverse_isConflationExact :
    E'.toExactStructure.IsConflationExact E.toExactStructure equiv.inverse
  /-- The chosen isomorphism commuting the equivalence with the two grading shifts. -/
  commShift : E.shift.functor ⋙ equiv.functor ≅ equiv.functor ⋙ E'.shift.functor

attribute [instance] GradedExactEquiv.functor_additive

namespace GradedExactEquiv

variable {C : Type u₁} {D : Type u₂} {K : Type u₃}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable [Category.{v₃} K] [Preadditive K] [HasZeroObject K] [HasBinaryBiproducts K]
variable {E : GradedExactStructure C} {E' : GradedExactStructure D} {E'' : GradedExactStructure K}

/-- The graded conflation-exact functor underlying a graded exact equivalence. -/
def toGradedConflationExact (h : GradedExactEquiv E E') :
    GradedConflationExact E E' h.equiv.functor where
  isConflationExact := h.isConflationExact
  commShift := h.commShift

/-- Passing to the underlying graded conflation-exact functor preserves the commutation
isomorphism. -/
@[simp]
theorem toGradedConflationExact_commShift (h : GradedExactEquiv E E') :
    h.toGradedConflationExact.commShift = h.commShift :=
  (rfl)

/-- The identity equivalence is a graded exact equivalence. -/
protected def refl (E : GradedExactStructure C) : GradedExactEquiv E E :=
  haveI : (CategoryTheory.Equivalence.refl (C := C)).functor.Additive :=
    inferInstanceAs (𝟭 C).Additive
  { equiv := CategoryTheory.Equivalence.refl
    isConflationExact := ExactStructure.IsConflationExact.id
    inverse_isConflationExact := ExactStructure.IsConflationExact.id
    commShift := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm }

/-- The equivalence underlying the identity graded exact equivalence. -/
@[simp]
theorem refl_equiv (E : GradedExactStructure C) :
    (GradedExactEquiv.refl E).equiv = CategoryTheory.Equivalence.refl :=
  (rfl)

/-- The shift-commutation isomorphism of the identity graded exact equivalence. -/
@[simp]
theorem refl_commShift (E : GradedExactStructure C) :
    HEq (GradedExactEquiv.refl E).commShift
      (Functor.rightUnitor E.shift.functor ≪≫ (Functor.leftUnitor E.shift.functor).symm) :=
  (HEq.rfl)

/-- The inverse of a graded exact equivalence is a graded exact equivalence. -/
protected def symm (h : GradedExactEquiv E E') : GradedExactEquiv E' E :=
  haveI : h.equiv.symm.functor.Additive := inferInstanceAs h.equiv.inverse.Additive
  { equiv := h.equiv.symm
    isConflationExact := h.inverse_isConflationExact
    inverse_isConflationExact := h.isConflationExact
    commShift :=
      (Functor.leftUnitor (E'.shift.functor ⋙ h.equiv.inverse)).symm ≪≫
        Functor.isoWhiskerRight h.equiv.counitIso.symm
          (E'.shift.functor ⋙ h.equiv.inverse) ≪≫
        Functor.associator h.equiv.inverse h.equiv.functor
          (E'.shift.functor ⋙ h.equiv.inverse) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.associator h.equiv.functor E'.shift.functor h.equiv.inverse).symm ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.isoWhiskerRight h.commShift.symm h.equiv.inverse) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.associator E.shift.functor h.equiv.functor h.equiv.inverse) ≪≫
        (Functor.associator h.equiv.inverse E.shift.functor
          (h.equiv.functor ⋙ h.equiv.inverse)).symm ≪≫
        Functor.isoWhiskerLeft (h.equiv.inverse ⋙ E.shift.functor) h.equiv.unitIso.symm ≪≫
        Functor.associator h.equiv.inverse E.shift.functor (𝟭 C) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse (Functor.rightUnitor E.shift.functor) }

/-- The equivalence underlying the inverse of a graded exact equivalence. -/
@[simp]
theorem symm_equiv (h : GradedExactEquiv E E') : h.symm.equiv = h.equiv.symm :=
  (rfl)

/-- The shift-commutation isomorphism of the inverse of a graded exact equivalence. -/
@[simp]
theorem symm_commShift (h : GradedExactEquiv E E') :
    HEq h.symm.commShift
      ((Functor.leftUnitor (E'.shift.functor ⋙ h.equiv.inverse)).symm ≪≫
        Functor.isoWhiskerRight h.equiv.counitIso.symm
          (E'.shift.functor ⋙ h.equiv.inverse) ≪≫
        Functor.associator h.equiv.inverse h.equiv.functor
          (E'.shift.functor ⋙ h.equiv.inverse) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.associator h.equiv.functor E'.shift.functor h.equiv.inverse).symm ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.isoWhiskerRight h.commShift.symm h.equiv.inverse) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse
          (Functor.associator E.shift.functor h.equiv.functor h.equiv.inverse) ≪≫
        (Functor.associator h.equiv.inverse E.shift.functor
          (h.equiv.functor ⋙ h.equiv.inverse)).symm ≪≫
        Functor.isoWhiskerLeft (h.equiv.inverse ⋙ E.shift.functor) h.equiv.unitIso.symm ≪≫
        Functor.associator h.equiv.inverse E.shift.functor (𝟭 C) ≪≫
        Functor.isoWhiskerLeft h.equiv.inverse (Functor.rightUnitor E.shift.functor)) :=
  (HEq.rfl)

/-- A composite of graded exact equivalences is a graded exact equivalence, for the composed
commutation isomorphism. -/
protected def trans (h : GradedExactEquiv E E') (h' : GradedExactEquiv E' E'') :
    GradedExactEquiv E E'' :=
  haveI : (h.equiv.trans h'.equiv).functor.Additive :=
    inferInstanceAs (h.equiv.functor ⋙ h'.equiv.functor).Additive
  { equiv := h.equiv.trans h'.equiv
    isConflationExact := h.isConflationExact.comp h'.isConflationExact
    inverse_isConflationExact := h'.inverse_isConflationExact.comp h.inverse_isConflationExact
    commShift := (h.toGradedConflationExact.comp h'.toGradedConflationExact).commShift }

/-- The equivalence underlying a composite of graded exact equivalences. -/
@[simp]
theorem trans_equiv (h : GradedExactEquiv E E') (h' : GradedExactEquiv E' E'') :
    (h.trans h').equiv = h.equiv.trans h'.equiv :=
  (rfl)

/-- The shift-commutation isomorphism of a composite graded exact equivalence. -/
@[simp]
theorem trans_commShift (h : GradedExactEquiv E E') (h' : GradedExactEquiv E' E'') :
    HEq (h.trans h').commShift
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight h.commShift h'.equiv.functor ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft h.equiv.functor h'.commShift ≪≫
        (Functor.associator _ _ _).symm) :=
  (HEq.rfl)

end GradedExactEquiv

end TauCeti
