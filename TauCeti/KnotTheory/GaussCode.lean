/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases

/-!
# Based oriented Gauss codes

A based oriented Gauss code records the combinatorial data seen while traversing an oriented knot
diagram from a chosen base point.  There are `2 * n` visits to `n` crossings; the partner
permutation pairs the two visits at each crossing, and the Boolean `over` field records which visit
passes over the other.  The `same_iff` axiom is the local four-valent condition in a compact form:
two visits have the same crossing label exactly when they are equal or partnered.  Crossing signs
are stored separately, so mirroring a code changes signs without changing its traversal data.

This is deliberately the based combinatorial presentation, rather than a claim that every abstract
code is already realised by a planar drawing.  Planar realisation, Reidemeister moves, and the
geometric-to-diagram correspondence are later parts of Layer 4 of the geometric-topology roadmap.
The code nevertheless has the structural operations needed by those developments: relabelling
crossings, mirroring, the writhe, and the crossing-free witness.

The conventions follow Lickorish, *An Introduction to Knot Theory*, Chapter 1: `true` means the
first visit is over, and a positive crossing contributes `+1` to the writhe.
-/

public section

namespace TauCeti

/-! ### Crossing signs -/

/-- The sign of an oriented crossing in a knot diagram. -/
inductive CrossingSign where
  | positive
  | negative
  deriving DecidableEq, Repr

namespace CrossingSign

/-- Reverse the sign, as under reflection of a diagram. -/
def neg : CrossingSign → CrossingSign
  | positive => negative
  | negative => positive

@[simp] theorem neg_positive : neg positive = negative := by simp [neg]

@[simp] theorem neg_negative : neg negative = positive := by simp [neg]

@[simp] theorem neg_neg (s : CrossingSign) : neg (neg s) = s := by
  cases s <;> rfl

/-- The integer contribution of a crossing to the writhe. -/
def toInt : CrossingSign → ℤ
  | positive => 1
  | negative => -1

@[simp] theorem toInt_positive : toInt positive = 1 := by simp [toInt]

@[simp] theorem toInt_negative : toInt negative = -1 := by simp [toInt]

@[simp] theorem toInt_neg (s : CrossingSign) : toInt (neg s) = -toInt s := by
  cases s <;> rfl

end CrossingSign

/-! ### Codes -/

/-- A based oriented Gauss code with `n` crossings.

The permutation `partner` is fixed-point-free and involutive.  `same_iff` says that its two-point
orbits are exactly the visits carrying a given crossing label; `visit_surjective` rules out unused
crossing labels.  Thus every crossing occurs exactly twice, once over and once under. -/
structure OrientedGaussCode (n : ℕ) where
  /-- Crossing label seen at each visit along the oriented traversal. -/
  visit : Fin (2 * n) → Fin n
  /-- Whether the strand is over (`true`) or under (`false`) at a visit. -/
  over : Fin (2 * n) → Bool
  /-- The oriented sign attached to each crossing. -/
  sign : Fin n → CrossingSign
  /-- The other visit at the same crossing. -/
  partner : Equiv.Perm (Fin (2 * n))
  /-- The partner operation is an involution. -/
  partner_involutive : ∀ i, partner (partner i) = i
  /-- No visit is partnered with itself. -/
  partner_ne : ∀ i, partner i ≠ i
  /-- The partner orbit is exactly the fibre of a crossing label. -/
  same_iff : ∀ i j, visit i = visit j ↔ j = i ∨ j = partner i
  /-- Every crossing label occurs in the traversal. -/
  visit_surjective : Function.Surjective visit
  /-- The two visits at a crossing have opposite over/under status. -/
  over_partner : ∀ i, over (partner i) = !over i

namespace OrientedGaussCode

variable {n : ℕ}

@[ext]
theorem ext {D E : OrientedGaussCode n}
    (hvisit : D.visit = E.visit) (hover : D.over = E.over) (hsign : D.sign = E.sign)
    (hpartner : D.partner = E.partner) : D = E := by
  cases D
  cases E
  simp only at hvisit hover hsign hpartner
  cases hvisit
  cases hover
  cases hsign
  cases hpartner
  rfl

/-- The partner of a visit is the unique distinct visit carrying the same crossing label. -/
theorem partner_eq_of_visit_eq {D : OrientedGaussCode n} {i j : Fin (2 * n)}
    (h : D.visit i = D.visit j) : j = i ∨ j = D.partner i :=
  (D.same_iff i j).mp h

@[simp]
theorem partner_partner (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.partner (D.partner i) = i := D.partner_involutive i

@[simp]
theorem visit_partner (D : OrientedGaussCode n) (i : Fin (2 * n)) :
    D.visit (D.partner i) = D.visit i := by
  exact (D.same_iff i (D.partner i)).mpr (Or.inr rfl) |>.symm

theorem exists_visit_of_crossing (D : OrientedGaussCode n) (c : Fin n) :
    ∃ i : Fin (2 * n), D.visit i = c :=
  D.visit_surjective c

/-- The two visits at every crossing have opposite over/under data. -/
theorem over_partner_ne {D : OrientedGaussCode n} (i : Fin (2 * n)) :
    D.over (D.partner i) ≠ D.over i := by
  rw [D.over_partner]
  cases h : D.over i <;> simp

/-- The writhe is the sum of the signs of all crossings. -/
def writhe (D : OrientedGaussCode n) : ℤ :=
  ∑ c : Fin n, CrossingSign.toInt (D.sign c)

/-- Reflecting a diagram reverses every crossing sign and leaves its traversal unchanged. -/
def mirror (D : OrientedGaussCode n) : OrientedGaussCode n where
  visit := D.visit
  over := D.over
  sign := fun c => CrossingSign.neg (D.sign c)
  partner := D.partner
  partner_involutive := D.partner_involutive
  partner_ne := D.partner_ne
  same_iff := D.same_iff
  visit_surjective := D.visit_surjective
  over_partner := D.over_partner

@[simp] theorem mirror_visit (D : OrientedGaussCode n) : D.mirror.visit = D.visit := by
  simp [mirror]

@[simp] theorem mirror_over (D : OrientedGaussCode n) : D.mirror.over = D.over := by
  simp [mirror]

@[simp] theorem mirror_sign (D : OrientedGaussCode n) (c : Fin n) :
    D.mirror.sign c = CrossingSign.neg (D.sign c) := by simp [mirror]

@[simp] theorem mirror_mirror (D : OrientedGaussCode n) : D.mirror.mirror = D := by
  apply ext <;> simp [mirror]

@[simp] theorem writhe_mirror (D : OrientedGaussCode n) : D.mirror.writhe = -D.writhe := by
  simp only [writhe, mirror_sign, CrossingSign.toInt_neg, Finset.sum_neg_distrib]

/-- Relabel crossings by an equivalence, without changing the traversal or pairing. -/
def relabel (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) : OrientedGaussCode n where
  visit := e ∘ D.visit
  over := D.over
  sign := D.sign ∘ e.symm
  partner := D.partner
  partner_involutive := D.partner_involutive
  partner_ne := D.partner_ne
  same_iff := by
    intro i j
    simpa [Function.comp_def] using D.same_iff i j
  visit_surjective := by
    intro c
    obtain ⟨i, hi⟩ := D.visit_surjective (e.symm c)
    exact ⟨i, by simp [hi]⟩
  over_partner := D.over_partner

@[simp] theorem relabel_visit (D : OrientedGaussCode n) (e : Fin n ≃ Fin n)
    (i : Fin (2 * n)) : (D.relabel e).visit i = e (D.visit i) := by
  simp [relabel]

@[simp] theorem relabel_sign (D : OrientedGaussCode n) (e : Fin n ≃ Fin n) (c : Fin n) :
    (D.relabel e).sign c = D.sign (e.symm c) := by simp [relabel]

@[simp] theorem relabel_id (D : OrientedGaussCode n) : D.relabel (Equiv.refl (Fin n)) = D := by
  apply ext <;> simp [relabel, Function.comp_def]

/-- The crossing-free based oriented Gauss code, representing the unknot diagram. -/
def empty : OrientedGaussCode 0 where
  visit := Fin.elim0
  over := Fin.elim0
  sign := Fin.elim0
  partner := Equiv.refl (Fin 0)
  partner_involutive := fun i => Fin.elim0 i
  partner_ne := fun i => Fin.elim0 i
  same_iff := fun i => Fin.elim0 i
  visit_surjective := fun x => Fin.elim0 x
  over_partner := fun i => Fin.elim0 i

/-- The one-crossing positive kink.  This is the smallest nontrivial Gauss code. -/
def oneCrossingPositive : OrientedGaussCode 1 where
  visit := fun _ => 0
  over := fun i => if i = 0 then true else false
  sign := fun _ => CrossingSign.positive
  partner := Equiv.swap 0 1
  partner_involutive := by
    intro i
    fin_cases i <;> rfl
  partner_ne := by
    intro i
    fin_cases i <;> decide
  same_iff := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  visit_surjective := by
    intro c
    fin_cases c
    exact ⟨0, rfl⟩
  over_partner := by
    intro i
    fin_cases i <;> simp

@[simp] theorem oneCrossingPositive_writhe :
    writhe oneCrossingPositive = 1 := by
  simp [writhe, oneCrossingPositive]

@[simp] theorem writhe_empty :
    writhe (empty : OrientedGaussCode 0) = 0 := by
  simp [writhe]

end OrientedGaussCode

end TauCeti
