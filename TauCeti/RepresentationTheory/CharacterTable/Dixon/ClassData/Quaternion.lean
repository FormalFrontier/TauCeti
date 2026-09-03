/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data for the quaternion group of order eight

This file feeds the computable enumeration `TauCeti.quaternionElements` to
`TauCeti.ClassData.ofList` and evaluates the conjugacy classes and class-algebra structure constants
of `QuaternionGroup 2`.  The five classes have representatives `1`, `-1`, and one member of each
of the three pairs of quaternion units.  Their structure constants agree with those of
`DihedralGroup 4`, as expected from the equality of the two groups' character tables.

## Main definitions

* `TauCeti.quaternionClassData`: computable class data for `QuaternionGroup n`.

## Main results

* `TauCeti.numClasses_quaternionClassData_two`: there are five conjugacy classes.
* `TauCeti.card_classFinset_quaternionClassData_two`: their sizes are `1, 1, 2, 2, 2`.
* `TauCeti.structureConstantTable_quaternionClassData_two`: the complete class multiplication
  table, evaluated by the kernel.

## References

This is the `Q₈ = QuaternionGroup 2` input for the rational-table milestone in Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

namespace TauCeti

/-- Class data for `QuaternionGroup n`, computed from `TauCeti.quaternionElements`. -/
@[expose] def quaternionClassData (n : ℕ) [NeZero n] : ClassData (QuaternionGroup n) :=
  ClassData.ofList (quaternionElements n) fun g =>
    ⟨g, mem_quaternionElements g, IsConj.refl g⟩

/-- **The quaternion group of order eight has five conjugacy classes.** -/
theorem numClasses_quaternionClassData_two : (quaternionClassData 2).numClasses = 5 := by
  decide

/-- **The conjugacy classes of the quaternion group of order eight have sizes
`1, 1, 2, 2, 2`.**  The numbering produced by `TauCeti.ClassData.ofList` has representatives
`a 0`, `a 2`, `xa 2`, `a 3`, and `xa 3`: the identity, the central element of order two, and
one member of each pair of elements of order four. -/
theorem card_classFinset_quaternionClassData_two :
    (quaternionClassData 2).classes.map Finset.card = [1, 1, 2, 2, 2] := by
  decide

/-- **The structure constants of the quaternion group of order eight.**  Each noncentral class
square is `2K₀ + 2K₁`, and the product of two distinct noncentral classes is twice the third.
This is the entire group-specific input to the Dixon--Schneider computation. -/
theorem structureConstantTable_quaternionClassData_two :
    (quaternionClassData 2).structureConstantTable =
      [[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
       [[0, 1, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
       [[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [2, 2, 0, 0, 0], [0, 0, 0, 0, 2], [0, 0, 0, 2, 0]],
       [[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2], [2, 2, 0, 0, 0], [0, 0, 2, 0, 0]],
       [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 2, 0], [0, 0, 2, 0, 0], [2, 2, 0, 0, 0]]] := by
  decide

end TauCeti
