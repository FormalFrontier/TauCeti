/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data for the dihedral groups

`TauCeti.ClassData` needs a concrete enumeration of the group to start from, since `Finset.toList`
is noncomputable; `TauCeti.dihedralElements` is that enumeration for `DihedralGroup n`. This file
feeds it to `TauCeti.ClassData.ofList` and works the dihedral group of order `8` as a closed
instance of the executable class-data API: its number of classes, its class sizes, and its full
array of structure constants are all evaluated by the kernel with `decide`. Stating the acceptance
test as `decide`-checked theorems rather than as `#eval`s is what makes CI check the values instead
of merely printing them.

## Main definitions

* `TauCeti.dihedralClassData`: the class data of `DihedralGroup n`.

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

/-- Class data for the dihedral group of order `2 * n`, computed from the enumeration
`TauCeti.dihedralElements`. The body is exposed so that a module downstream of this one can still
`decide` statements about the class data of a concrete dihedral group. -/
@[expose] def dihedralClassData (n : ℕ) [NeZero n] : ClassData (DihedralGroup n) :=
  ClassData.ofList (dihedralElements n) fun g =>
    ⟨g, mem_dihedralElements g, IsConj.refl g⟩

/-- **The dihedral group of order `8` has five conjugacy classes**, computed by the kernel from
`TauCeti.dihedralClassData`. -/
theorem numClasses_dihedralClassData_four : (dihedralClassData 4).numClasses = 5 := by decide

/-- **The five conjugacy classes of the dihedral group of order `8` have sizes `1, 1, 2, 2, 2`.**
The order is the one `TauCeti.ClassData.ofList` produces from `TauCeti.dihedralElements`, with
representatives `1`, `r²`, `sr²`, `r³`, `sr³`: the identity, the central rotation, one pair of
reflections, the pair of rotations of order `4`, and the other pair of reflections. -/
theorem card_classFinset_dihedralClassData_four :
    (dihedralClassData 4).classes.map Finset.card = [1, 1, 2, 2, 2] := by
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
