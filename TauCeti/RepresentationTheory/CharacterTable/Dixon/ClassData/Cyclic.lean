/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data for finite cyclic groups

This file gives the cyclic group `Multiplicative (ZMod n)` the executable conjugacy-class
numbering used by the Dixon--Schneider algorithm.  The enumeration is the standard list
`0, 1, ..., n - 1`, transported from the additive group `ZMod n`; since the group is commutative,
each conjugacy class is a singleton.

The order produced by `TauCeti.ClassData.ofList` is the order of the retained representatives in
the input enumeration.  For `n = 2` the resulting representatives are `0, 1`, which in
multiplicative notation are the identity and the nontrivial element.  The concrete class sizes and
structure constants below are kernel-checked inputs to the rational Dixon computation for `C₂`.

## Main definitions

* `TauCeti.cyclicElements`: a computable enumeration of `Multiplicative (ZMod n)`.
* `TauCeti.cyclicClassData`: executable class data obtained from that enumeration.

## Main results

* `TauCeti.numClasses_cyclicClassData`: a cyclic group of order `n` has `n` numbered classes.
* `TauCeti.classFinset_cyclicClassData`: every numbered cyclic class is a singleton.
* `TauCeti.card_classFinset_cyclicClassData_two`: both classes are singletons.
* `TauCeti.structureConstantTable_cyclicClassData_two`: the complete multiplication table of the
  two class sums.

## References

This supplies the executable class data for the cyclic `C₂` example in Layer 6, “Rational tables
(first executable milestone),” of the [character theory roadmap][roadmap].

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md
-/

public section

namespace TauCeti

/-- The standard computable enumeration of the finite cyclic group
`Multiplicative (ZMod n)`. -/
@[expose] def cyclicElements (n : ℕ) : List (Multiplicative (ZMod n)) :=
  List.map (fun i : ℕ => Multiplicative.ofAdd (i : ZMod n)) (List.range n)

/-- Every element of `Multiplicative (ZMod n)` occurs in `TauCeti.cyclicElements n` when `n` is
nonzero. -/
theorem mem_cyclicElements (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ cyclicElements n := by
  rw [cyclicElements]
  have hg : Multiplicative.ofAdd (g.toAdd.val : ZMod n) = g :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)
  rw [← hg]
  exact List.mem_map_of_mem
    (f := fun i : ℕ => Multiplicative.ofAdd (i : ZMod n))
    (List.mem_range.mpr (ZMod.val_lt g.toAdd))

private theorem cyclicElements_pairwise_not_isConj (n : ℕ) [NeZero n] :
    (cyclicElements n).Pairwise fun x y => ¬ IsConj x y := by
  rw [cyclicElements, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij hconj
  rw [isConj_iff_eq] at hconj
  have hval := congrArg ZMod.val (congrArg Multiplicative.toAdd hconj)
  rw [List.getElem_range hi, List.getElem_range hj] at hval
  simp only [List.length_range] at hi hj
  change (i : ZMod n).val = (j : ZMod n).val at hval
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

/-- Every conjugacy class of a cyclic group has cardinality one. -/
@[simp]
theorem card_classFinset_cyclicClassData (n : ℕ) [NeZero n]
    (i : Fin (cyclicClassData n).numClasses) :
    ((cyclicClassData n).classFinset i).card = 1 := by
  rw [classFinset_cyclicClassData, Finset.card_singleton]

/-- **Both conjugacy classes of the cyclic group of order two are singletons.** The numbered
representatives are the identity followed by the nontrivial element. -/
theorem card_classFinset_cyclicClassData_two :
    (cyclicClassData 2).classes.map Finset.card = [1, 1] := by
  decide

/-- **The class-sum structure constants of the cyclic group of order two.** In the numbering
above, the identity class is first and the nontrivial class squares to it. -/
theorem structureConstantTable_cyclicClassData_two :
    (cyclicClassData 2).structureConstantTable =
      [[[1, 0], [0, 1]],
       [[0, 1], [1, 0]]] := by
  decide

end TauCeti
