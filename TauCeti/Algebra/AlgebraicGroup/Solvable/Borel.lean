/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Geometric solvability of the upper-triangular Borel of `GL₂`

The coordinate Hopf algebra of the upper-triangular Borel subgroup of `GL₂` has a solvable group
of geometric points. The existing point equivalence identifies that group with `GL2Borel` over an
algebraic closure, while the latter is solvable because its diagonal quotient and unipotent kernel
are abelian.

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

open WithConv

namespace TauCeti.GeneralLinear.Borel

universe u

/-- The upper-triangular Borel subgroup of `GL₂` has a solvable group of geometric points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallySolvablePointsCommHopfAlgProperty k (coordinateHopfAlgebra k) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff]
  let e := pointsMulEquiv (R := k) (A := AlgebraicClosure k)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end TauCeti.GeneralLinear.Borel
