/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Solvability and the derived closed subgroup

Let `H` be a commutative Hopf algebra. Its derived closed subgroup has coordinate algebra
`H / CommHopfAlgCat.derivedDefiningIdeal H`. This file proves, over any commutative base and at
every commutative value algebra, that the point group of `H` is solvable exactly when the point
group of this derived subgroup is solvable. The geometric-points statement over a field is then an
immediate specialization.

One implication is closure of solvability under closed subgroups. Conversely, the derived closed
subgroup contains every pointwise commutator, so the corresponding point-group quotient is
commutative. Solvability of the derived subgroup and of this commutative quotient then gives
solvability of the ambient point group by extension closure. No equality between the abstract
pointwise commutator subgroup and the points of the derived group is needed.

## Main declaration

* `TauCeti.CommHopfAlgCat.isSolvable_points_iff_derived`: over any commutative base and value
  algebra, the point group is solvable exactly when the derived closed subgroup's point group is.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff_derived`: geometric-point
  solvability is equivalent to geometric-point solvability of the derived closed subgroup.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This advances Layer 5, "Lie--Kolchin; solvable groups", of the ReductiveGroups roadmap. It is the
derived-subgroup recursion bridge connecting the existing scheme-theoretic derived subgroup to the
existing geometric-points solvability predicate. The strict-dimension step and the representation
induction remain separate.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The group of points of an affine group is solvable if and only if the group of points of its
derived closed subgroup is solvable.

The forward implication uses the injection from quotient-coordinate points into ambient points.
For the reverse implication, their image is a normal solvable subgroup containing the abstract
commutator subgroup. The ambient point group is therefore an extension of a commutative group by
a solvable group. This statement holds over an arbitrary commutative base ring and at every
commutative value algebra. -/
theorem isSolvable_points_iff_derived (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) ↔
      Group.IsSolvable
        (HopfAlgebra.points (R := R)
          (H := quotient H (derivedDefiningIdeal H)) A) := by
  let G := HopfAlgebra.points (R := R) (H := H) A
  let I := derivedDefiningIdeal (R := R) H
  let D := quotientPointsSubgroup H I A
  constructor
  · intro hG
    let _ : Group.IsSolvable G := hG
    exact Group.isSolvable_of_isSolvable_injective
      (f := (quotientPointsHom H I A).hom)
      (quotientPointsHom_injective H I A)
  · intro hderived
    let q := (quotientPointsHom H I A).hom
    let _ : Group.IsSolvable
        (HopfAlgebra.points (R := R) (H := quotient H I) A) := hderived
    have hD : Group.IsSolvable D :=
      Group.isSolvable_of_surjective q.rangeRestrict_surjective
    let _ : Group.IsSolvable D := hD
    let _ : D.Normal := quotientPointsSubgroup_normal H I
      (isNormal_derivedDefiningIdeal H) A
    have hcommutator : commutator G ≤ D :=
      commutator_le_quotientPointsSubgroup_of_le_derivedDefiningIdeal H I le_rfl A
    have hcommutative : IsMulCommutative (G ⧸ D) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcommutator
    have hquotient : Group.IsSolvable (G ⧸ D) :=
      Group.isSolvable_of_comm (isMulCommutative_iff.mp hcommutative)
    exact (Group.isSolvable_iff_subgroup_quotient D).mpr ⟨hD, hquotient⟩

end CommHopfAlgCat

/-- An affine group has solvable geometric points if and only if its derived closed subgroup does.

The forward implication uses that the derived closed subgroup embeds in the ambient group on
points. For the reverse implication, its image is a normal solvable subgroup containing the
abstract commutator subgroup, so the quotient is commutative and hence solvable. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_iff_derived
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H)) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff,
    geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact CommHopfAlgCat.isSolvable_points_iff_derived H
    (CommAlgCat.of k (AlgebraicClosure k))

end TauCeti
