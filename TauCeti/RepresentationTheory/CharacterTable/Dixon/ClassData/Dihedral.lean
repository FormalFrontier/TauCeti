/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Class data for the dihedral groups

`TauCeti.ClassData` needs a concrete enumeration of the group to start from, since `Finset.toList`
is noncomputable. This file supplies one for `DihedralGroup n` and works the dihedral group of
order `8` as a closed instance of the executable class-data API: its number of classes, its class
sizes, and its full array of structure constants are all evaluated by the kernel with `decide`.
Stating the acceptance test as `decide`-checked theorems rather than as `#eval`s is what makes CI
check the values instead of merely printing them.

## Main definitions

* `TauCeti.dihedralElements`: an enumeration of `DihedralGroup n`.
* `TauCeti.dihedralClassData`: the class data it produces.

## Main results

* `TauCeti.numClasses_dihedralClassData_four`,
  `TauCeti.card_classFinset_dihedralClassData_four` and
  `TauCeti.structureConstantTable_dihedralClassData_four`: the class count, the class sizes, and
  the structure constants of the dihedral group of order `8`, evaluated by the kernel.

## References

This is the `#eval`-test on `DihedralGroup 4` asked for by Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

namespace TauCeti

/-- The `2 * n` elements of `DihedralGroup n`, listed: each rotation followed by the corresponding
reflection. A concrete enumeration is what `TauCeti.ClassData.ofList` needs, and `Finset.toList`
cannot supply. -/
def dihedralElements (n : ℕ) [NeZero n] : List (DihedralGroup n) :=
  (List.range n).flatMap fun i : ℕ => [DihedralGroup.r (i : ZMod n), DihedralGroup.sr (i : ZMod n)]

/-- The enumeration `TauCeti.dihedralElements` exhausts the dihedral group. -/
theorem mem_dihedralElements {n : ℕ} [NeZero n] (g : DihedralGroup n) : g ∈ dihedralElements n := by
  have hmem : ∀ i : ZMod n, i.val ∈ List.range n := fun i => List.mem_range.mpr (ZMod.val_lt i)
  cases g with
  | r i =>
    refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
    rw [ZMod.natCast_rightInverse i]
    simp
  | sr i =>
    refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
    rw [ZMod.natCast_rightInverse i]
    simp

/-- Class data for the dihedral group of order `2 * n`, computed from the enumeration
`TauCeti.dihedralElements`. -/
def dihedralClassData (n : ℕ) [NeZero n] : ClassData (DihedralGroup n) :=
  ClassData.ofList (dihedralElements n) mem_dihedralElements

/-- **The dihedral group of order `8` has five conjugacy classes**, computed by the kernel from
`TauCeti.dihedralClassData`. -/
theorem numClasses_dihedralClassData_four : (dihedralClassData 4).numClasses = 5 := by decide

/-- **The five conjugacy classes of the dihedral group of order `8` have sizes `1, 1, 2, 2, 2`.**
The order is the one `TauCeti.ClassData.ofList` produces from `TauCeti.dihedralElements`, with
representatives `1`, `r²`, `sr²`, `r³`, `sr³`: the identity, the central rotation, one pair of
reflections, the pair of rotations of order `4`, and the other pair of reflections. -/
theorem card_classFinset_dihedralClassData_four :
    (List.finRange (dihedralClassData 4).numClasses).map
      (fun i => ((dihedralClassData 4).classFinset i).card) = [1, 1, 2, 2, 2] := by
  decide

/-- **The structure constants of the dihedral group of order `8`**, computed by the kernel; this
nested list is the entire input the Dixon--Schneider algorithm reads for that group. In the
numbering of `TauCeti.card_classFinset_dihedralClassData_four`, each of the three classes of size
`2` squares to `2K₀ + 2K₁`, and multiplying the class `K₃` of rotations of order `4` by either
class of reflections exchanges the two. -/
theorem structureConstantTable_dihedralClassData_four :
    (dihedralClassData 4).structureConstantTable =
      [[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
       [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
       [[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 2, 0, 0, 0], [0, 0, 0, 0, 2], [0, 0, 0, 2, 0]],
       [[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2], [2, 2, 0, 0, 0], [0, 0, 2, 0, 0]],
       [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 2, 0], [0, 0, 2, 0, 0], [2, 2, 0, 0, 0]]] := by
  decide

end TauCeti
