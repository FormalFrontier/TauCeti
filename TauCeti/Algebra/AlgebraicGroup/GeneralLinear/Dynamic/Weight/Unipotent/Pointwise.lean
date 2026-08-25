/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Unipotent.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.ClosedSubgroup

/-!
# Unipotence of represented weight-cocharacter subgroups

Let `w : Fin N → ℤ` and let `λ_w` be the corresponding diagonal cocharacter of `GL_N`.
The dynamic subgroup `U(λ_w)(A)` consists of the matrices which are block triangular for the
weight filtration and induce the identity on its associated graded. The coordinate Hopf algebra
`GeneralLinear.weightUnipotentCoordinateHopfAlgebra k w` represents this subgroup.

This file proves that every point of that coordinate Hopf algebra over a same-universe perfect
extension field is unipotent in the representation-theoretic sense. The argument uses the
representing isomorphism to place the point in the dynamic subgroup of `GL_N`, applies the general
dynamic-unipotence theorem there, and then reflects unipotence across the surjective quotient
coordinate morphism.

Smoothness and geometric connectedness of the represented subgroup require an explicit
description of its coordinate ring and are not asserted here.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra`: every
  perfect-extension-valued point of a represented weight-unipotent subgroup is unipotent.
* `TauCeti.GeneralLinear.Dynamic.geometricallyUnipotentPoints_weightUnipotentCoordinateHopfAlgebra`:
  the represented subgroup has geometrically unipotent points.

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
unipotent in every finite-dimensional representation.

The representing isomorphism identifies its image in `GL_N` with a point of the dynamic
unipotent subgroup. Unipotence is then reflected from that ambient point because the defining
coordinate morphism is surjective. -/
theorem isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra
    (w : Fin N → ℤ) (L : Type u) [Field L] [Algebra k L] [PerfectField L]
    (g : HopfAlgebra.points (R := k)
      (H := weightUnipotentCoordinateHopfAlgebra k w) (CommAlgCat.of k L)) :
    HopfAlgebra.IsUnipotentPoint g := by
  let p : Cocharacter.unipotent (CommAlgCat.of k L)
      (weightCocharacter (R := k) w) :=
    eqToHom (Cocharacter.unipotentFunctor_obj
      (weightCocharacter (R := k) w) (CommAlgCat.of k L))
      ((weightUnipotentPointsIso k w).hom.app (CommAlgCat.of k L) g)
  have hp : (p : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k N)
      (CommAlgCat.of k L)) =
      CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra k N)
        (weightUnipotentDefiningHopfIdeal k w) (CommAlgCat.of k L) g :=
    coe_weightUnipotentPointsIso_hom_app_apply k w g
  have hambient : HopfAlgebra.IsUnipotentPoint
      (CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra k N)
        (weightUnipotentDefiningHopfIdeal k w) (CommAlgCat.of k L) g) := by
    rw [← hp]
    exact Cocharacter.isUnipotentPoint_of_mem_unipotent
      (weightCocharacter (R := k) w) p.2
  refine (HopfAlgebra.isUnipotentPoint_mapDomain_iff_of_surjective
    (k := k) (H := coordinateHopfAlgebra k N)
    (K := weightUnipotentCoordinateHopfAlgebra k w) (L := L)
    (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra k N)
      (weightUnipotentDefiningHopfIdeal k w)).hom
    (Ideal.Quotient.mkₐ_surjective k
      (weightUnipotentDefiningHopfIdeal k w).toIdeal) g).mp ?_
  rw [← CommHopfAlgCat.quotientPointsHom_apply]
  exact hambient

/-- The represented weight-unipotent subgroup has geometrically unipotent points. -/
theorem geometricallyUnipotentPoints_weightUnipotentCoordinateHopfAlgebra
    (w : Fin N → ℤ) :
    geometricallyUnipotentPointsCommHopfAlgProperty k
      (weightUnipotentCoordinateHopfAlgebra k w) := by
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff k]
  intro g
  exact isUnipotentPoint_weightUnipotentCoordinateHopfAlgebra
    (k := k) w (AlgebraicClosure k) g

end TauCeti.GeneralLinear.Dynamic
