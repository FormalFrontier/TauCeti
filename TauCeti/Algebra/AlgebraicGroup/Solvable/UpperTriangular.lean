/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# Geometric solvability of upper-triangular general linear groups

Over a field, the geometric points of the upper-triangular subgroup scheme are solvable: its
points are identified with the abstract upper-triangular matrix group, whose diagonal quotient is
abelian and whose upper-unitriangular kernel is nilpotent.

## Main declaration

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

/-- The upper-triangular affine group has a solvable group of geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  let e := pointsMulEquiv (R := k) (n := n) (A := AlgebraicClosure k)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end TauCeti.GeneralLinear.UpperTriangular
