/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data for finite cyclic groups

For `n ≠ 0`, this file gives the cyclic group `Multiplicative (ZMod n)` the executable
conjugacy-class numbering used by the Dixon--Schneider algorithm.  It uses the standard enumeration
`0, 1, ..., n - 1`, transported from the additive group `ZMod n`; since the group is commutative,
each conjugacy class is a singleton.

The order produced by `TauCeti.ClassData.ofList` is the order of the retained representatives in
the input enumeration.  For `n = 2` the resulting representatives are `0, 1`, which in
multiplicative notation are the identity and the nontrivial element.

## Main definitions

* `TauCeti.cyclicClassData`: executable class data obtained from that enumeration.

## Main results

* `TauCeti.numClasses_cyclicClassData`: a cyclic group of order `n` has `n` numbered classes.
* `TauCeti.classFinset_cyclicClassData`: every numbered cyclic class is a singleton.
* `TauCeti.structureConstant_cyclicClassData`: the structure constants are cyclic convolution.

## References

This supplies the executable class data for the cyclic `C₂` example in Layer 6, “Rational tables
(first executable milestone),” of the [character theory roadmap][roadmap].

The definition follows the executable pattern of `TauCeti.dihedralClassData`.

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md
-/

public section

namespace TauCeti

private theorem cyclicElements_pairwise_not_isConj (n : ℕ) :
    (cyclicElements n).Pairwise fun x y => ¬ IsConj x y := by
  rw [cyclicElements, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij hconj
  rw [isConj_iff_eq] at hconj
  have hval := congrArg ZMod.val (congrArg Multiplicative.toAdd hconj)
  rw [List.getElem_range hi, List.getElem_range hj] at hval
  simp only [List.length_range] at hi hj
  simp only [toAdd_ofAdd] at hval
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hval
  exact (Nat.ne_of_lt hij) hval

/-- Executable conjugacy-class data for the finite cyclic group
`Multiplicative (ZMod n)`.  The body is exposed so concrete cyclic groups can evaluate their class
sizes and structure constants in downstream modules. -/
@[expose] def cyclicClassData (n : ℕ) [NeZero n] :
    ClassData (Multiplicative (ZMod n)) :=
  ClassData.ofList (cyclicElements n) fun g =>
    ⟨g, mem_cyclicElements n g, IsConj.refl g⟩

/-- The chosen representatives for cyclic class data are the standard enumeration. -/
@[simp]
theorem reps_cyclicClassData (n : ℕ) [NeZero n] :
    (cyclicClassData n).reps = cyclicElements n := by
  rw [cyclicClassData, ClassData.reps_ofList]
  exact (cyclicElements_pairwise_not_isConj n).pwFilter

/-- A cyclic group of order `n` has `n` conjugacy classes. -/
@[simp]
theorem numClasses_cyclicClassData (n : ℕ) [NeZero n] :
    (cyclicClassData n).numClasses = n := by
  simp [ClassData.numClasses, cyclicElements]

/-- The representative numbered `i` is the residue class of `i`. -/
@[simp]
theorem rep_cyclicClassData (n : ℕ) [NeZero n]
    (i : Fin (cyclicClassData n).numClasses) :
    (cyclicClassData n).rep i = Multiplicative.ofAdd (i.val : ZMod n) := by
  simp [ClassData.rep, cyclicElements]

/-- Every numbered conjugacy class of a cyclic group is the singleton of its representative. -/
@[simp]
theorem classFinset_cyclicClassData (n : ℕ) [NeZero n]
    (i : Fin (cyclicClassData n).numClasses) :
    (cyclicClassData n).classFinset i = {(cyclicClassData n).rep i} := by
  ext g
  rw [ClassData.mem_classFinset_iff_isConj, Finset.mem_singleton, isConj_iff_eq]
  exact eq_comm

/-- Every numbered conjugacy class of a finite cyclic group has cardinality one. -/
theorem card_classFinset_cyclicClassData (n : ℕ) [NeZero n]
    (i : Fin (cyclicClassData n).numClasses) :
    ((cyclicClassData n).classFinset i).card = 1 := by
  rw [classFinset_cyclicClassData, Finset.card_singleton]

/-- The ordered list of class sizes of a finite cyclic group consists entirely of ones. -/
theorem card_classes_cyclicClassData (n : ℕ) [NeZero n] :
    (cyclicClassData n).classes.map Finset.card = List.replicate n 1 := by
  rw [ClassData.classes, List.map_map]
  calc
    _ = (List.finRange (cyclicClassData n).numClasses).map (Function.const _ 1) := by
      apply List.map_congr_left
      intro i _
      exact card_classFinset_cyclicClassData n i
    _ = List.replicate n 1 := by
      rw [List.map_const, List.length_finRange, numClasses_cyclicClassData]

/-- The cyclic class-sum structure constant is one exactly when the indices add to the output
index, and zero otherwise. -/
@[simp]
theorem structureConstant_cyclicClassData (n : ℕ) [NeZero n]
    (i j k : Fin (cyclicClassData n).numClasses) :
    (cyclicClassData n).structureConstant i j k =
      if (i : ZMod n) + j = k then 1 else 0 := by
  rw [ClassData.structureConstant, classFinset_cyclicClassData]
  simp only [Finset.filter_singleton]
  rw [rep_cyclicClassData, rep_cyclicClassData]
  have hindex :
      (cyclicClassData n).index
          ((Multiplicative.ofAdd (i : ZMod n))⁻¹ *
            Multiplicative.ofAdd (k : ZMod n)) = j ↔
        (i : ZMod n) + j = k := by
    rw [(cyclicClassData n).index_eq_iff, isConj_iff_eq, rep_cyclicClassData]
    constructor
    · intro h
      have h' := congrArg Multiplicative.toAdd h
      simp only [toAdd_ofAdd, toAdd_inv, toAdd_mul] at h'
      calc
        (i : ZMod n) + j = (i : ZMod n) + (-i + k) := congrArg _ h'
        _ = k := add_neg_cancel_left _ _
    · intro h
      apply Multiplicative.toAdd.injective
      simp only [toAdd_ofAdd, toAdd_inv, toAdd_mul]
      calc
        (j : ZMod n) = -i + (i + j) := by simp
        _ = -i + k := congrArg _ h
  by_cases h : (cyclicClassData n).index
      ((Multiplicative.ofAdd (i : ZMod n))⁻¹ *
        Multiplicative.ofAdd (k : ZMod n)) = j
  · simp only [h, ↓reduceIte, Finset.card_singleton, hindex.mp h]
  · simp only [h, ↓reduceIte, Finset.card_empty, mt hindex.mpr h]

end TauCeti
