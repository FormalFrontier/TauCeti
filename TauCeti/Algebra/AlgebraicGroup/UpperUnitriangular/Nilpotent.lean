/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.FunctorOfPoints
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent

/-!
# Nilpotence of upper-unitriangular group points

The convolution points of the coordinate Hopf algebra of `U_n` are naturally equivalent to the
ordinary upper-unitriangular matrix group. The matrix group is nilpotent over every commutative
ring, so this equivalence makes every value of the represented group functor nilpotent, and hence
solvable.

## Main declarations

* `TauCeti.UpperUnitriangular.isNilpotent_points`: every group of algebra-valued points of `U_n`
  is nilpotent.
* `TauCeti.UpperUnitriangular.isSolvable_points`: every such point group is solvable.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

This is the upper-unitriangular case of the solvability target in Layer 5 of the ReductiveGroups
roadmap. Once the upper-unitriangular embedding characterization is complete, subgroup closure
transfers this result to every smooth connected unipotent affine group.
-/

public section

namespace TauCeti.UpperUnitriangular

universe u v w

variable (R : Type u) [CommRing R] (m : Type v) [Fintype m] [LinearOrder m]
variable (A : Type w) [CommRing A] [Algebra R A]

/-- The group of `A`-valued points of `U_n` is nilpotent. -/
theorem isNilpotent_points :
    Group.IsNilpotent
      (WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) := by
  exact Group.nilpotent_of_mulEquiv (pointsMulEquiv R m).symm

/-- The group of `A`-valued points of `U_n` is solvable. -/
theorem isSolvable_points :
    Group.IsSolvable
      (WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) := by
  let _ := isNilpotent_points R m A
  infer_instance

end TauCeti.UpperUnitriangular
