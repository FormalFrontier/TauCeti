/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The basic upper-triangular subgroup API and diagonal kernel identification.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel.Basic
-- Nilpotence of the upper-unitriangular subgroup supplies the solvable kernel below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent

/-!
# Solvability of upper-triangular general linear groups

The diagonal quotient of the upper-triangular group is abelian, while its kernel is the
nilpotent upper-unitriangular group. Hence every upper-triangular general linear group over a
commutative ring is solvable.

This advances the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap. The result supplies the abstract-group input for the corresponding Borel subgroup scheme
once that scheme has been constructed in general rank.

## Main declaration

* `TauCeti.UpperTriangularGroup.instIsSolvable`: upper-triangular general linear groups are
  solvable.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti.UpperTriangularGroup

open Matrix

universe u

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type u) [CommRing R]

/-- The upper-triangular subgroup of `GL_m(R)` is solvable over every commutative ring. -/
instance instIsSolvable : Group.IsSolvable (upperTriangularGroup m R) := by
  apply Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (upperUnitriangularGroup_le_upperTriangularGroup (m := m) (R := R)))
    (diag (m := m) (R := R))
  rw [Subgroup.inclusion_range, ker_diag]

end TauCeti.UpperTriangularGroup
