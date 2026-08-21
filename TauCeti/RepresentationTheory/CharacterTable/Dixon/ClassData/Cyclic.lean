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

* `TauCeti.numClasses_cyclicClassData_two`: `C₂` has two numbered conjugacy classes.
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
  change g ∈ List.map (fun i : ℕ => Multiplicative.ofAdd (i : ZMod n)) (List.range n)
  have hg : Multiplicative.ofAdd (g.toAdd.val : ZMod n) = g :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)
  rw [← hg]
  exact List.mem_map_of_mem
    (f := fun i : ℕ => Multiplicative.ofAdd (i : ZMod n))
    (List.mem_range.mpr (ZMod.val_lt g.toAdd))

/-- Executable conjugacy-class data for the finite cyclic group
`Multiplicative (ZMod n)`.  The body is exposed so concrete cyclic groups can evaluate their class
sizes and structure constants in downstream modules. -/
@[expose] def cyclicClassData (n : ℕ) [NeZero n] :
    ClassData (Multiplicative (ZMod n)) :=
  ClassData.ofList (cyclicElements n) fun g =>
    ⟨g, mem_cyclicElements n g, IsConj.refl g⟩

/-- **The cyclic group of order two has two conjugacy classes**, computed by the kernel. -/
@[simp]
theorem numClasses_cyclicClassData_two : (cyclicClassData 2).numClasses = 2 := by
  decide

/-- **Both conjugacy classes of the cyclic group of order two are singletons.** The numbered
representatives are the identity followed by the nontrivial element. -/
theorem card_classFinset_cyclicClassData_two :
    (cyclicClassData 2).classes.map Finset.card = [1, 1] := by
  decide

/-- Each numbered conjugacy class of the cyclic group of order two has cardinality one. -/
@[simp]
theorem card_classFinset_cyclicClassData_two_apply
    (i : Fin (cyclicClassData 2).numClasses) :
    ((cyclicClassData 2).classFinset i).card = 1 := by
  fin_cases i <;> decide

/-- **The class-sum structure constants of the cyclic group of order two.** In the numbering
above, the identity class is first and the nontrivial class squares to it. -/
theorem structureConstantTable_cyclicClassData_two :
    (cyclicClassData 2).structureConstantTable =
      [[[1, 0], [0, 1]],
       [[0, 1], [1, 0]]] := by
  decide

end TauCeti
