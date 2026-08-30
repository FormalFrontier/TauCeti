/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# Geometric solvability of upper-triangular general linear groups

Over a field, the geometric points of the upper-triangular subgroup scheme are solvable: its
points are identified with the abstract upper-triangular matrix group, whose diagonal quotient is
abelian and whose upper-unitriangular kernel is nilpotent.

## Main declarations

* `isSolvable_points`: every algebra-valued point group is solvable.
* `geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra`: the upper-triangular
  affine group has solvable geometric points.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Sections 2.4 and 6.3.

This advances Layer 5, "Lie--Kolchin; solvable groups", of the ReductiveGroups roadmap.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear.UpperTriangular

universe u

/-- Every algebra-valued point group of the upper-triangular affine group is solvable. -/
theorem isSolvable_points (R : Type u) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (n : ℕ) : Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A)) := by
  let e := pointsMulEquiv (R := R) (n := n) (A := A)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- The upper-triangular affine group has a solvable group of geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact isSolvable_points k (AlgebraicClosure k) n

end TauCeti.GeneralLinear.UpperTriangular
