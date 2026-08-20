/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple

/-!
# Semisimple points and closed subgroups of groups of multiplicative type

A finite-type affine group over a field is of multiplicative type when its coordinate Hopf
algebra becomes diagonalizable after extension to an algebraic closure. Every point of a
diagonalizable group is semisimple, so the geometric fibre of a group of multiplicative type has
only semisimple geometric points. The same is true for every closed subgroup of that geometric
fibre, represented contravariantly by a Hopf quotient.

This is the semisimple-point input for comparing groups of multiplicative type with unipotent
groups. In particular, a reduced unipotent closed subgroup of the geometric fibre of a group of
multiplicative type is trivial.

## Main declarations

* `TauCeti.multiplicativeTypeCommHopfAlgProperty.geometricFiberSemisimplePoints`: the geometric
  fibre of a group of multiplicative type has only semisimple geometric points.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty.geometricFiberQuotientSemisimplePoints`: every
  closed subgroup of the geometric fibre has only semisimple geometric points.
* `TauCeti.multiplicativeTypeCommHopfAlgProperty.eq_augmentation_of_geometricallyUnipotent`: a
  reduced unipotent closed subgroup of the geometric fibre is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 4, "Diagonalizable groups and groups of multiplicative type", and supplies a
prerequisite for the torus worked example in Layer 6 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The geometric fibre of a finite-type group of multiplicative type has only semisimple
geometric points. -/
@[grind →]
theorem multiplicativeTypeCommHopfAlgProperty.geometricFiberSemisimplePoints
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H) :
    geometricallySemisimplePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hH
  obtain ⟨G, ⟨i⟩⟩ := hH
  exact (geometricallySemisimplePointsCommHopfAlgProperty
    (AlgebraicClosure k)).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
        (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
      (DiagonalizableGroup.geometricallySemisimplePointsCommHopfAlgProperty
        (AlgebraicClosure k) G)

/-- Every closed subgroup of the geometric fibre of a group of multiplicative type has only
semisimple geometric points. The subgroup is represented contravariantly by a Hopf quotient. -/
theorem multiplicativeTypeCommHopfAlgProperty.geometricFiberQuotientSemisimplePoints
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H)) :
    geometricallySemisimplePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj := by
  apply geometricallySemisimplePointsCommHopfAlgProperty_of_surjective (AlgebraicClosure k)
    (FiniteTypeCommHopfAlgCat.mkQuotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).hom
    (Ideal.Quotient.mkₐ_surjective (AlgebraicClosure k) I.toIdeal)
  exact hH.geometricFiberSemisimplePoints k H

/-- A reduced closed subgroup of the geometric fibre of a group of multiplicative type is trivial
if all of its geometric points are unipotent. Equivalently, its defining Hopf ideal is the
augmentation ideal.

Reducedness cannot be omitted: nonreduced infinitesimal groups are invisible to geometric
points. -/
theorem multiplicativeTypeCommHopfAlgProperty.eq_augmentation_of_geometricallyUnipotent
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : multiplicativeTypeCommHopfAlgProperty k H)
    (I : HopfIdeal (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H))
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I)]
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I).obj) :
    I = HopfIdeal.augmentation (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  FiniteTypeCommHopfAlgCat.eq_augmentation_of_geometricallySemisimple_of_geometricallyUnipotent
    (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) I
    (hH.geometricFiberQuotientSemisimplePoints k H I) hI

end TauCeti
