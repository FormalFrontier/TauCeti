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
group of any closed subgroup containing the derived subgroup is solvable. The derived-subgroup
and geometric-points statements are immediate specializations.

One implication is closure of solvability under closed subgroups. Conversely, the derived closed
subgroup contains every pointwise commutator, so the corresponding point-group quotient is
commutative. Solvability of the derived subgroup and of this commutative quotient then gives
solvability of the ambient point group by extension closure. No equality between the abstract
pointwise commutator subgroup and the points of the derived group is needed.

## Main declarations

* `TauCeti.CommHopfAlgCat.isSolvable_points_iff_of_le_derivedDefiningIdeal`: over any
  commutative base and value algebra, the point group is solvable exactly when any closed subgroup
  containing the derived subgroup has a solvable point group.
* `TauCeti.CommHopfAlgCat.isSolvable_points_iff_derived`: the derived-subgroup specialization.
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

/-- The point group of a closed subgroup of an affine group is solvable whenever the ambient
point group is solvable. This holds over an arbitrary commutative base ring and at every
commutative value algebra. -/
theorem isSolvable_points_quotient (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (A : CommAlgCat.{w} R) :
    Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) →
      Group.IsSolvable
        (HopfAlgebra.points (R := R) (H := quotient H I) A) := by
  intro hH
  let _ : Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) := hH
  exact Group.isSolvable_of_isSolvable_injective
    (f := (quotientPointsHom H I A).hom)
    (quotientPointsHom_injective H I A)

/-- If a closed subgroup contains the derived subgroup and its point group is solvable, then the
ambient point group is solvable. This holds over an arbitrary commutative base ring and at every
commutative value algebra. -/
theorem isSolvable_points_of_le_derivedDefiningIdeal
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
    (hID : I ≤ derivedDefiningIdeal (R := R) H) (A : CommAlgCat.{w} R) :
    Group.IsSolvable (HopfAlgebra.points (R := R) (H := quotient H I) A) →
      Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) := by
  let G := HopfAlgebra.points (R := R) (H := H) A
  let D := quotientPointsSubgroup H I A
  intro hsubgroup
  let q := (quotientPointsHom H I A).hom
  let _ : Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := quotient H I) A) := hsubgroup
  have hD : Group.IsSolvable D :=
    Group.isSolvable_of_surjective q.rangeRestrict_surjective
  let _ : D.Normal := quotientPointsSubgroup_normal H I
    (isNormal_of_le_derivedDefiningIdeal H I hID) A
  have hcommutative : IsMulCommutative (G ⧸ D) :=
    isMulCommutative_pointQuotient_of_le_derivedDefiningIdeal H I hID A
  have hquotient : Group.IsSolvable (G ⧸ D) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hcommutative)
  exact (Group.isSolvable_iff_subgroup_quotient D).mpr ⟨hD, hquotient⟩

/-- The point group of an affine group is solvable if and only if the point group of any closed
subgroup containing its derived subgroup is solvable. This holds over an arbitrary commutative
base ring and at every commutative value algebra. -/
theorem isSolvable_points_iff_of_le_derivedDefiningIdeal
    (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H)
    (hID : I ≤ derivedDefiningIdeal (R := R) H) (A : CommAlgCat.{w} R) :
    Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) ↔
      Group.IsSolvable
        (HopfAlgebra.points (R := R) (H := quotient H I) A) :=
  ⟨isSolvable_points_quotient H I A,
    isSolvable_points_of_le_derivedDefiningIdeal H I hID A⟩

/-- The group of points of an affine group is solvable if and only if the group of points of its
derived closed subgroup is solvable, over any commutative base and value algebra. -/
theorem isSolvable_points_iff_derived (H : _root_.CommHopfAlgCat.{v} R)
    (A : CommAlgCat.{w} R) :
    Group.IsSolvable (HopfAlgebra.points (R := R) (H := H) A) ↔
      Group.IsSolvable
        (HopfAlgebra.points (R := R)
          (H := quotient H (derivedDefiningIdeal H)) A) :=
  isSolvable_points_iff_of_le_derivedDefiningIdeal H (derivedDefiningIdeal H) le_rfl A

end CommHopfAlgCat

/-- An affine group has solvable geometric points if and only if any closed subgroup containing
its derived subgroup does. This is the point-group result specialized to algebraic-closure-valued
points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_iff_of_le_derivedDefiningIdeal
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) (I : HopfIdeal k H)
    (hID : I ≤ CommHopfAlgCat.derivedDefiningIdeal H) :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient H I) := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff,
    geometricallySolvablePointsCommHopfAlgProperty_iff]
  exact CommHopfAlgCat.isSolvable_points_iff_of_le_derivedDefiningIdeal H I hID
    (CommAlgCat.of k (AlgebraicClosure k))

/-- An affine group has solvable geometric points if and only if its derived closed subgroup does.
This is `CommHopfAlgCat.isSolvable_points_iff_derived` specialized to
algebraic-closure-valued points. -/
theorem geometricallySolvablePointsCommHopfAlgProperty_iff_derived
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      geometricallySolvablePointsCommHopfAlgProperty k
        (CommHopfAlgCat.quotient H (CommHopfAlgCat.derivedDefiningIdeal H)) :=
  geometricallySolvablePointsCommHopfAlgProperty_iff_of_le_derivedDefiningIdeal
    k H (CommHopfAlgCat.derivedDefiningIdeal H) le_rfl

end TauCeti
