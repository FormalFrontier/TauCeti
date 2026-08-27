/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel

/-!
# Geometric solvability of the upper-triangular Borel of `GL₂`

The coordinate Hopf algebra of the upper-triangular Borel subgroup of `GL₂` has a solvable group
of geometric points. The existing point equivalence identifies that group with `GL2Borel` over an
algebraic closure. This group is solvable as the `Fin 2` case of
`TauCeti.UpperTriangularGroup.instIsSolvable`: it has an abelian diagonal quotient and a nilpotent
upper-unitriangular kernel.

## Main declaration

* `geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra`:
  the `GL₂` Borel has solvable geometric points.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is the standard Borel example for the "Lie--Kolchin; solvable groups" milestone in Layer 5
of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti.GeneralLinear.Borel

universe u

open TauCeti.GeneralLinear

/-- The upper-triangular Borel subgroup of `GL₂` has a solvable group of geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  exact UpperTriangular.geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k 2

end TauCeti.GeneralLinear.Borel
