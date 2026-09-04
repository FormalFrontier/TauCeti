/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.Ring

/-!
# Additivity of the integer powers of an autoequivalence

Mathlib defines the integer powers `e ^ j` of an autoequivalence `e : C ≌ C` by recursion and
records `e ^ 0`, `e ^ 1` and `e ^ (-1)`, but leaves the comparison of `e ^ (a + b)` with the
composite `e ^ a ⋙ e ^ b` as an explicit TODO.  This file supplies that comparison as an
isomorphism of the underlying functors, together with the successor and predecessor forms which
consume it.

Only the underlying functors are compared.  `e ^ (a + b)` and `(e ^ a).trans (e ^ b)` are not
equal as equivalences — the recursion inserts unitors — so the isomorphism below, and not an
equation, is what downstream constructions use.

## Main definitions

* `TauCeti.equivPowSuccIso`: `e ^ (j + 1) ≅ e ⋙ e ^ j`, by case analysis on `j`.
* `TauCeti.equivPowPredIso`: `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.
* `TauCeti.equivPowAddIso`: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
* `TauCeti.equivPowSuccRightIso`: `e ^ (j + 1) ≅ e ^ j ⋙ e`, the opposite-handed successor
  isomorphism, which the additivity isomorphism supplies but the recursion does not.
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- Equal integer exponents give the same power functor. -/
def equivPowCongrIso (e : C ≌ C) {a b : ℤ} (h : a = b) :
    (e ^ a).functor ≅ (e ^ b).functor :=
  eqToIso (by rw [h])

/-- **The successor isomorphism `e ^ (j + 1) ≅ e ⋙ e ^ j`.**  Mathlib's power is built by
prepending a copy of `e`, so this is the identity except at the two exponents where the recursion
bottoms out. -/
def equivPowSuccIso (e : C ≌ C) : ∀ j : ℤ,
    (e ^ (j + 1)).functor ≅ e.functor ⋙ (e ^ j).functor
  | (0 : ℕ) => (Functor.rightUnitor e.functor).symm
  | ((_ + 1 : ℕ) : ℤ) => Iso.refl _
  | Int.negSucc 0 => e.unitIso
  | Int.negSucc (m + 1) =>
      (Functor.leftUnitor (e.symm.powNat (m + 1)).functor).symm ≪≫
        Functor.isoWhiskerRight e.unitIso _ ≪≫
          Functor.associator e.functor e.inverse (e.symm.powNat (m + 1)).functor

/-- Composing on the left with the inverse equivalence cancels a leading copy of the functor. -/
private def leftCancelInverseIso (e : C ≌ C) (G : C ⥤ C) :
    e.inverse ⋙ e.functor ⋙ G ≅ G :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso G ≪≫
    Functor.leftUnitor G

/-- **The predecessor isomorphism `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.** -/
def equivPowPredIso (e : C ≌ C) (j : ℤ) :
    e.inverse ⋙ (e ^ j).functor ≅ (e ^ (j - 1)).functor :=
  Functor.isoWhiskerLeft e.inverse
      (equivPowCongrIso e (by ring : j = j - 1 + 1) ≪≫ equivPowSuccIso e (j - 1)) ≪≫
    leftCancelInverseIso e _

/-- The inductive step of `TauCeti.equivPowAddIso` which raises the first exponent by one. -/
private def addIsoOfSucc (e : C ≌ C) (b a a' : ℤ) (h : a' = a + 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  equivPowCongrIso e (by rw [h]; ring : a' + b = a + b + 1) ≪≫
    equivPowSuccIso e (a + b) ≪≫ Functor.isoWhiskerLeft e.functor ih ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((equivPowSuccIso e a).symm ≪≫ equivPowCongrIso e (by rw [h] : a + 1 = a')) _

/-- The inductive step of `TauCeti.equivPowAddIso` which lowers the first exponent by one. -/
private def addIsoOfPred (e : C ≌ C) (b a a' : ℤ) (h : a' = a - 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  (leftCancelInverseIso e _).symm ≪≫
    Functor.isoWhiskerLeft e.inverse
        ((equivPowSuccIso e (a' + b)).symm ≪≫
          equivPowCongrIso e (by rw [h]; ring : a' + b + 1 = a + b) ≪≫ ih) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (equivPowPredIso e a ≪≫ equivPowCongrIso e (by rw [h] : a - 1 = a')) _

/-- Additivity of the integer powers at a nonnegative first exponent. -/
private def equivPowAddNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ ((n : ℤ) + b)).functor ≅ (e ^ (n : ℤ)).functor ⋙ (e ^ b).functor
  | 0 =>
      equivPowCongrIso e (by push_cast; ring : ((0 : ℕ) : ℤ) + b = b) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      addIsoOfSucc e b (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (equivPowAddNatIso e b n)

/-- Additivity of the integer powers at a nonpositive first exponent. -/
private def equivPowSubNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ (-(n : ℤ) + b)).functor ≅ (e ^ (-(n : ℤ))).functor ⋙ (e ^ b).functor
  | 0 =>
      equivPowCongrIso e (by push_cast; ring : -((0 : ℕ) : ℤ) + b = b) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      addIsoOfPred e b (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (equivPowSubNatIso e b n)

/-- **Additivity of the integer powers of an autoequivalence**: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`. -/
def equivPowAddIso (e : C ≌ C) : ∀ a b : ℤ,
    (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor
  | Int.ofNat n, b => equivPowAddNatIso e b n
  | Int.negSucc n, b => equivPowSubNatIso e b (n + 1)

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def equivPowSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  equivPowAddIso e j 1

end TauCeti
