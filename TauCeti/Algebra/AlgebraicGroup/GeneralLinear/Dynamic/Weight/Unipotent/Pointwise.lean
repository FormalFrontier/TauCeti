/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Basic

/-!
# Unipotence of represented weight-cocharacter subgroups

Let `w : Fin N → ℤ` and let `λ_w` be the corresponding diagonal cocharacter of `GL_N`.
The dynamic subgroup `U(λ_w)(A)` consists of the matrices which are block triangular for the
weight filtration and induce the identity on its associated graded. The coordinate Hopf algebra
`GeneralLinear.weightUnipotentCoordinateHopfAlgebra k w` represents this subgroup.

This file proves that every point of that coordinate Hopf algebra over a same-universe perfect
extension field is unipotent in the representation-theoretic sense. The defining Hopf ideal cuts
out the dynamic unipotent subgroup, so the general quotient-point theorem applies.

Smoothness and geometric connectedness of the represented subgroup require an explicit
description of its coordinate ring and are not asserted here.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra`: every
  perfect-extension-valued point of a represented weight-unipotent subgroup is unipotent.
* `geometricallyUnipotentPointsCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra`: the
  represented subgroup has geometrically unipotent points.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic parabolic and Levi route in Layer 7, "Structure theory", of the
ReductiveGroups roadmap by proving the unipotence property of the represented unipotent factor.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- Every point of the weight-unipotent coordinate Hopf algebra over a perfect extension field is
unipotent in every finite-dimensional representation. -/
theorem isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra
    (w : Fin N → ℤ) (L : Type u) [Field L] [Algebra k L] [PerfectField L]
    (g : HopfAlgebra.points (R := k)
      (H := weightUnipotentCoordinateHopfAlgebra k w) (CommAlgCat.of k L)) :
    HopfAlgebra.IsUnipotentPoint g := by
  apply Cocharacter.isUnipotentPoint_quotient_of_le_unipotent
    (coordinateHopfAlgebra k N) (weightUnipotentDefiningHopfIdeal k w)
    (weightCocharacter (R := k) w) L _ g
  intro p hp
  exact (mem_weightUnipotentDefiningPointsSubgroup_iff k w p).mp hp

/-- The represented weight-unipotent subgroup has geometrically unipotent points. -/
theorem geometricallyUnipotentPointsCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra
    (w : Fin N → ℤ) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (weightUnipotentCoordinateHopfAlgebra k w) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff k]
  intro g
  exact isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra
    (k := k) w (AlgebraicClosure k) g

end TauCeti.GeneralLinear.Dynamic
