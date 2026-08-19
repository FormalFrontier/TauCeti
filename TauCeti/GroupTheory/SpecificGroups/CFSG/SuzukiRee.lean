/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# Numbered data for the Suzuki--Ree isogenies

The exceptional isogenies used to construct the Suzuki and Ree groups exchange long and short
simple roots. Their action on a simple root subgroup also raises its parameter to an exponent:
the exponent is `1` on a long simple root and the defining characteristic on a short simple root.
This file attaches both the length-exchanging permutation and the exponent convention to
`TauCeti.SuzukiReeIndex`.

The assignment is a genuine choice. Reversing the two exponents would still make the square of the
exceptional isogeny a prime-field Frobenius, so the square relation alone does not determine which
isogeny the later construction uses. Defining the exponent through
`TauCeti.DynkinType.IsLongSimpleRoot` ties it to the Bourbaki numbering and root-length convention
already fixed by the root-systems development, without introducing a second table for `B₂`, `G₂`,
and `F₄`.

The permutation selector has only the four half-Frobenius branches: Suzuki and Ree `G₂` use the
rank-two node swap, while Ree `F₄` and Tits use diagram reversal. Milestone L2 must reduce every
branch to the corresponding pinned permutation when selecting the upstream special isogeny, so the
four branch equations are simp lemmas rather than the selector body being exposed.

## Main definitions and results

* `TauCeti.SuzukiReeIndex.lengthPerm` selects the length-exchanging permutation used by the
  exceptional isogeny.
* `TauCeti.SuzukiReeIndex.lengthPerm_suzuki`, `TauCeti.SuzukiReeIndex.lengthPerm_reeG2`,
  `TauCeti.SuzukiReeIndex.lengthPerm_reeF4`, and `TauCeti.SuzukiReeIndex.lengthPerm_tits` are the
  branch equations naming the selected permutation on each half-Frobenius family.
* `TauCeti.SuzukiReeIndex.isLongSimpleRoot_lengthPerm` proves that this permutation exchanges long
  and short simple roots.
* `TauCeti.SuzukiReeIndex.exponent` is `1` on long simple roots and the characteristic on short
  simple roots.
* `TauCeti.SuzukiReeIndex.exponent_of_isLongSimpleRoot` and
  `TauCeti.SuzukiReeIndex.exponent_of_not_isLongSimpleRoot` are the two computation rules used by
  the exceptional-isogeny equations.
* `TauCeti.SuzukiReeIndex.exponent_eq_one_iff` and
  `TauCeti.SuzukiReeIndex.exponent_eq_characteristic_iff` characterize the two values without
  unfolding the definition.

This is the Suzuki--Ree numbered-data part of milestone I0 in
`TauCetiRoadmap/CFSGStatement/README.md`. The exponent convention follows Carter, *Simple Groups of
Lie Type*. The permutations and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters
4--6*, plates II, VIII, and IX, as fixed by the CFSG and root-systems roadmaps.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

-- Transporting the root-length predicate together with its index type avoids dependent rewriting
-- through `DynkinType.rank`, which is precisely the dependency that `finCongr` packages.
private theorem isLongSimpleRoot_reindexPerm {t u : DynkinType} (h : t = u)
    (p : Equiv.Perm (Fin u.rank))
    (hp : ∀ j, u.IsLongSimpleRoot (p j) ↔ ¬u.IsLongSimpleRoot j) (i : Fin t.rank) :
    t.IsLongSimpleRoot
        ((finCongr (congrArg DynkinType.rank h)).symm.permCongr p i) ↔
      ¬t.IsLongSimpleRoot i := by
  subst u
  simpa [finCongr_refl, Equiv.permCongr_def] using hp i

/-- The length-exchanging permutation used by the exceptional isogeny attached to a Suzuki--Ree
index: the node swap for `B₂` and `G₂`, and reversal for `F₄`.

The four branch equations `lengthPerm_suzuki`, `lengthPerm_reeG2`, `lengthPerm_reeF4`, and
`lengthPerm_tits` name the selected permutation on each family, so no consumer needs this body. -/
def lengthPerm (e : SuzukiReeIndex) : Equiv.Perm (Fin e.1.rank) :=
  match e with
  | ⟨⟨.A _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedA _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.B _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.C _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.D _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedD _ _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E7 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.E8 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.F4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.G2 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.twistedE6 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.trialityD4 _, _⟩, h⟩ => by simp at h
  | ⟨⟨.suzuki m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_suzuki, DynkinType.rank_B])).symm.permCongr lengthPermRankTwo
  | ⟨⟨.reeG2 m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeG2, DynkinType.rank_G2])).symm.permCongr lengthPermRankTwo
  | ⟨⟨.reeF4 m, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeF4, DynkinType.rank_F4])).symm.permCongr lengthPermF4
  | ⟨⟨.tits, hvalid⟩, _⟩ =>
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_tits, DynkinType.rank_F4])).symm.permCongr lengthPermF4

/-- A Suzuki index selects the rank-two node swap, transported along the `B₂` numbering. -/
@[simp] theorem lengthPerm_suzuki (m : ℕ) (hvalid : (LieTypeIndex.suzuki m).Valid) :
    lengthPerm ⟨⟨.suzuki m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_suzuki, DynkinType.rank_B])).symm.permCongr
        lengthPermRankTwo := by
  simp only [lengthPerm]

/-- A Ree `G₂` index selects the rank-two node swap, transported along the `G₂` numbering. -/
@[simp] theorem lengthPerm_reeG2 (m : ℕ) (hvalid : (LieTypeIndex.reeG2 m).Valid) :
    lengthPerm ⟨⟨.reeG2 m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeG2, DynkinType.rank_G2])).symm.permCongr
        lengthPermRankTwo := by
  simp only [lengthPerm]

/-- A Ree `F₄` index selects the `F₄` diagram reversal. -/
@[simp] theorem lengthPerm_reeF4 (m : ℕ) (hvalid : (LieTypeIndex.reeF4 m).Valid) :
    lengthPerm ⟨⟨.reeF4 m, hvalid⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_reeF4, DynkinType.rank_F4])).symm.permCongr lengthPermF4 := by
  simp only [lengthPerm]

/-- The Tits index selects the `F₄` diagram reversal. -/
@[simp] theorem lengthPerm_tits :
    lengthPerm ⟨⟨.tits, by simp⟩, by simp⟩ =
      (finCongr (by
        simp only [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType,
          LieTypeIndex.dynkinType_tits, DynkinType.rank_F4])).symm.permCongr lengthPermF4 := by
  simp only [lengthPerm]

/-- The length permutation selected by a Suzuki--Ree index exchanges long and short simple roots
in the Bourbaki numbering of its underlying untwisted Dynkin diagram. -/
@[simp]
theorem isLongSimpleRoot_lengthPerm (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.1.dynkinType.IsLongSimpleRoot (e.lengthPerm i) ↔
      ¬e.1.dynkinType.IsLongSimpleRoot i := by
  simp only [ValidLieTypeIndex.dynkinType, ValidLieTypeIndex.rank] at i ⊢
  obtain ⟨⟨d, hvalid⟩, hhalf⟩ := e
  cases d <;> try simp at hhalf
  case suzuki =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_suzuki _)
      lengthPermRankTwo isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_B2 i using 1
    all_goals simp only [lengthPerm_suzuki]
    rfl
  case reeG2 =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_reeG2 _)
      lengthPermRankTwo isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_G2 i using 1
    all_goals simp only [lengthPerm_reeG2]
    rfl
  case reeF4 =>
    convert isLongSimpleRoot_reindexPerm (LieTypeIndex.dynkinType_reeF4 _)
      lengthPermF4 isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 i using 1
    all_goals simp only [lengthPerm_reeF4]
    rfl
  case tits =>
    convert isLongSimpleRoot_reindexPerm LieTypeIndex.dynkinType_tits lengthPermF4
      isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 i using 1
    all_goals simp only [lengthPerm_tits]
    rfl

/-- The exponent attached to a numbered simple root subgroup by the exceptional isogeny: `1` on a
long simple root and the defining characteristic on a short simple root.

The long-root predicate is the root-systems development's Bourbaki-numbered predicate, rather than
a second family-by-family table. -/
def exponent (e : SuzukiReeIndex) (i : Fin e.1.rank) : ℕ :=
  if e.1.dynkinType.IsLongSimpleRoot i then 1 else e.1.characteristic

/-- The exceptional isogeny uses exponent `1` on long simple root subgroups. -/
@[simp]
theorem exponent_of_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = 1 := by
  simp [exponent, hi]

/-- The exceptional isogeny uses the defining characteristic as its exponent on short simple root
subgroups. -/
@[simp]
theorem exponent_of_not_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : ¬e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = e.1.characteristic := by
  simp [exponent, hi]

/-- A root-subgroup exponent is `1` exactly on a long simple root. -/
@[simp]
theorem exponent_eq_one_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ↔ e.1.dynkinType.IsLongSimpleRoot i := by
  simp [exponent, e.1.characteristic_prime.ne_one]

/-- A root-subgroup exponent is the defining characteristic exactly on a short simple root. -/
@[simp]
theorem exponent_eq_characteristic_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = e.1.characteristic ↔ ¬e.1.dynkinType.IsLongSimpleRoot i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, hi, not_true_eq_false, iff_false]
    exact e.1.characteristic_prime.ne_one.symm
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, hi, not_false_eq_true]

/-- Every root-subgroup exponent is positive. -/
theorem exponent_pos (e : SuzukiReeIndex) (i : Fin e.1.rank) : 0 < e.exponent i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, Nat.zero_lt_one]
  · rw [exponent_of_not_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.pos

/-- Every root-subgroup exponent is at most the defining characteristic. -/
theorem exponent_le_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i ≤ e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · rw [exponent_of_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.one_lt.le
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, le_refl]

/-- The two possible values of a root-subgroup exponent. -/
theorem exponent_eq_one_or_eq_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ∨ e.exponent i = e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · exact Or.inl (exponent_of_isLongSimpleRoot e i hi)
  · exact Or.inr (exponent_of_not_isLongSimpleRoot e i hi)

end SuzukiReeIndex

end TauCeti
