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

* `CategoryTheory.Equivalence.powSuccIso`: `e ^ (j + 1) ≅ e ⋙ e ^ j`, by case analysis on `j`.
* `CategoryTheory.Equivalence.powPredIso`: `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.
* `CategoryTheory.Equivalence.powAddIso`: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`.
* `CategoryTheory.Equivalence.powSuccRightIso`: `e ^ (j + 1) ≅ e ^ j ⋙ e`, the opposite-handed
  successor isomorphism, which the additivity isomorphism supplies but the recursion does not.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C]

/-- Equal integer exponents give the same power functor. -/
def _root_.CategoryTheory.Equivalence.powCongrIso (e : C ≌ C) {a b : ℤ} (h : a = b) :
    (e ^ a).functor ≅ (e ^ b).functor :=
  eqToIso (by rw [h])

/-- **The successor isomorphism `e ^ (j + 1) ≅ e ⋙ e ^ j`.**  Mathlib's power is built by
prepending a copy of `e`, so this is the identity except at the two exponents where the recursion
bottoms out. -/
def _root_.CategoryTheory.Equivalence.powSuccIso (e : C ≌ C) : ∀ j : ℤ,
    (e ^ (j + 1)).functor ≅ e.functor ⋙ (e ^ j).functor
  | (0 : ℕ) => (Functor.rightUnitor e.functor).symm
  | ((_ + 1 : ℕ) : ℤ) => Iso.refl _
  | Int.negSucc 0 => e.unitIso
  | Int.negSucc (m + 1) =>
      (Functor.leftUnitor (e.symm.powNat (m + 1)).functor).symm ≪≫
        Functor.isoWhiskerRight e.unitIso _ ≪≫
          Functor.associator e.functor e.inverse (e.symm.powNat (m + 1)).functor

/-- **The predecessor isomorphism `e⁻¹ ⋙ e ^ j ≅ e ^ (j - 1)`.** -/
def _root_.CategoryTheory.Equivalence.powPredIso (e : C ≌ C) (j : ℤ) :
    e.inverse ⋙ (e ^ j).functor ≅ (e ^ (j - 1)).functor :=
  Functor.isoWhiskerLeft e.inverse
      (e.powCongrIso (by ring : j = j - 1 + 1) ≪≫ e.powSuccIso (j - 1)) ≪≫
    e.invFunIdAssoc _

/-- The inductive step of `CategoryTheory.Equivalence.powAddIso` which raises the first exponent
by one. -/
private def _root_.CategoryTheory.Equivalence.powAddIsoOfSucc (e : C ≌ C) (b a a' : ℤ)
    (h : a' = a + 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  e.powCongrIso (by rw [h]; ring : a' + b = a + b + 1) ≪≫
    e.powSuccIso (a + b) ≪≫ Functor.isoWhiskerLeft e.functor ih ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((e.powSuccIso a).symm ≪≫ e.powCongrIso (by rw [h] : a + 1 = a')) _

/-- The inductive step of `CategoryTheory.Equivalence.powAddIso` which lowers the first exponent
by one. -/
private def _root_.CategoryTheory.Equivalence.powAddIsoOfPred (e : C ≌ C) (b a a' : ℤ)
    (h : a' = a - 1)
    (ih : (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor) :
    (e ^ (a' + b)).functor ≅ (e ^ a').functor ⋙ (e ^ b).functor :=
  (e.invFunIdAssoc _).symm ≪≫
    Functor.isoWhiskerLeft e.inverse
        ((e.powSuccIso (a' + b)).symm ≪≫
          e.powCongrIso (by rw [h]; ring : a' + b + 1 = a + b) ≪≫ ih) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (e.powPredIso a ≪≫ e.powCongrIso (by rw [h] : a - 1 = a')) _

/-- Additivity of the integer powers at a nonnegative first exponent. -/
private def _root_.CategoryTheory.Equivalence.powAddNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ ((n : ℤ) + b)).functor ≅ (e ^ (n : ℤ)).functor ⋙ (e ^ b).functor
  | 0 =>
      e.powCongrIso (by push_cast; ring : ((0 : ℕ) : ℤ) + b = b) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      e.powAddIsoOfSucc b (n : ℤ) (((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (CategoryTheory.Equivalence.powAddNatIso e b n)

/-- Additivity of the integer powers at a nonpositive first exponent. -/
private def _root_.CategoryTheory.Equivalence.powSubNatIso (e : C ≌ C) (b : ℤ) : ∀ n : ℕ,
    (e ^ (-(n : ℤ) + b)).functor ≅ (e ^ (-(n : ℤ))).functor ⋙ (e ^ b).functor
  | 0 =>
      e.powCongrIso (by push_cast; ring : -((0 : ℕ) : ℤ) + b = b) ≪≫
        (Functor.leftUnitor _).symm
  | n + 1 =>
      e.powAddIsoOfPred b (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by push_cast; ring)
        (CategoryTheory.Equivalence.powSubNatIso e b n)

/-- **Additivity of the integer powers of an autoequivalence**: `e ^ (a + b) ≅ e ^ a ⋙ e ^ b`. -/
def _root_.CategoryTheory.Equivalence.powAddIso (e : C ≌ C) : ∀ a b : ℤ,
    (e ^ (a + b)).functor ≅ (e ^ a).functor ⋙ (e ^ b).functor
  | Int.ofNat n, b => e.powAddNatIso b n
  | Int.negSucc n, b => e.powSubNatIso b (n + 1)

/-- **The opposite-handed successor isomorphism `e ^ (j + 1) ≅ e ^ j ⋙ e`.** -/
def _root_.CategoryTheory.Equivalence.powSuccRightIso (e : C ≌ C) (j : ℤ) :
    (e ^ (j + 1)).functor ≅ (e ^ j).functor ⋙ e.functor :=
  e.powAddIso j 1

end TauCeti
