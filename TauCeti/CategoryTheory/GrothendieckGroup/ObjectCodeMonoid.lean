/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Presentation
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# The monoid of isomorphism classes under the binary biproduct

For an essentially small category `C` with zero morphisms, a zero object and binary biproducts,
the small type `TauCeti.ObjectCode C` of codes for the isomorphism classes of objects carries an
additive commutative monoid structure: the sum of two classes is the class of the biproduct of
chosen representatives, and the neutral element is the class of the zero object.

The chosen representatives supplied by `TauCeti.objectCodeOut` are what makes the addition
definable at all, but they never escape: `TauCeti.objectCode_biprod` computes the sum on the codes
of actual objects, and the monoid laws are transported from `biprod.associator`,
`biprod.braiding` and the two zero-summand isomorphisms of Mathlib.

## Main definitions

* the `AddCommMonoid (TauCeti.ObjectCode C)` instance.

## Main results

* `TauCeti.objectCode_biprod` and `TauCeti.objectCode_zero`: the code of a binary biproduct is the
  sum of the codes, and the code of the zero object is the neutral element.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 5,
  where the monoid of isomorphism classes of objects under the biproduct is the starting point of
  the group-completion description of split `K₀`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

/-- Isomorphism classes of objects are added by taking the binary biproduct of chosen
representatives. The choice never escapes: `TauCeti.objectCode_biprod` computes the sum on the
codes of actual objects. -/
noncomputable instance : Add (ObjectCode C) :=
  ⟨fun c d => objectCode (objectCodeOut c ⊞ objectCodeOut d)⟩

/-- The class of the zero object is the neutral isomorphism class. -/
noncomputable instance : Zero (ObjectCode C) := ⟨objectCode (0 : C)⟩

omit [HasZeroObject C] in
/-- The defining equation of the addition of isomorphism classes, in terms of the chosen
representatives. -/
lemma ObjectCode.add_def (c d : ObjectCode C) :
    c + d = objectCode (objectCodeOut c ⊞ objectCodeOut d) := (rfl)

omit [HasZeroObject C] in
/-- The code of a binary biproduct is the sum of the object codes. -/
@[simp]
lemma objectCode_biprod (X Y : C) : objectCode (X ⊞ Y) = objectCode X + objectCode Y := by
  rw [ObjectCode.add_def]
  exact (objectCode_congr (biprod.mapIso (objectCodeOutIso X) (objectCodeOutIso Y))).symm

omit [HasZeroMorphisms C] [HasBinaryBiproducts C] in
/-- The code of the zero object is the neutral isomorphism class. -/
@[simp]
lemma objectCode_zero : objectCode (0 : C) = (0 : ObjectCode C) := (rfl)

/-- The isomorphism classes of an essentially small category with zero morphisms, a zero object
and binary biproducts form an additive commutative monoid under the binary biproduct. -/
noncomputable instance : AddCommMonoid (ObjectCode C) where
  nsmul := nsmulRec
  add_assoc a b c := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    obtain ⟨B, rfl⟩ := objectCode_surjective b
    obtain ⟨D, rfl⟩ := objectCode_surjective c
    rw [← objectCode_biprod, ← objectCode_biprod, ← objectCode_biprod, ← objectCode_biprod]
    exact objectCode_congr (biprod.associator A B D)
  add_comm a b := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    obtain ⟨B, rfl⟩ := objectCode_surjective b
    rw [← objectCode_biprod, ← objectCode_biprod]
    exact objectCode_congr (biprod.braiding A B)
  add_zero a := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    rw [← objectCode_zero, ← objectCode_biprod]
    exact objectCode_congr (isoBiprodZero (isZero_zero C)).symm
  zero_add a := by
    obtain ⟨A, rfl⟩ := objectCode_surjective a
    rw [← objectCode_zero, ← objectCode_biprod]
    exact objectCode_congr (isoZeroBiprod (isZero_zero C)).symm

end TauCeti
