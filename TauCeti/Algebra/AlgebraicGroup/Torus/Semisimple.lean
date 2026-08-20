/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple

/-!
# Semisimple points of the geometric fibre of a torus

Every torus is a group of multiplicative type, hence becomes diagonalizable over an algebraic
closure. Its geometric fibre therefore has only semisimple geometric points.

## Main declarations

* `TauCeti.torusCommHopfAlgProperty.geometricFiberSemisimplePoints`: the geometric fibre of a
  torus has only semisimple geometric points.
* `TauCeti.torusCommHopfAlgProperty.geometricFiberQuotientSemisimplePoints`: every closed
  subgroup of the geometric fibre has only semisimple geometric points.
* `TauCeti.torusCommHopfAlgProperty.eq_augmentation_of_geometricallyUnipotent`: a reduced
  unipotent closed subgroup of the geometric fibre is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the semisimple-point prerequisite for the roadmap's Layer 6 worked example that
tori are reductive. Combined with geometric unipotence, it makes every point of a smooth
unipotent closed subgroup trivial; the remaining input for reductivity is the reduction theorem
for smooth affine groups.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The geometric fibre of a torus has only semisimple geometric points. -/
@[grind →]
theorem torusCommHopfAlgProperty.geometricFiberSemisimplePoints
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    geometricallySemisimplePointsCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H).obj :=
  hH.multiplicativeType.geometricFiberSemisimplePoints k H

/-- Every closed subgroup of the geometric fibre of a torus has only semisimple geometric
points. The subgroup is represented contravariantly by a Hopf quotient. -/
theorem torusCommHopfAlgProperty.geometricFiberQuotientSemisimplePoints
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H)
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

/-- A reduced closed subgroup of the geometric fibre of a torus is trivial if all of its
geometric points are unipotent. Equivalently, its defining Hopf ideal is the augmentation ideal.

Reducedness cannot be omitted: nonreduced infinitesimal groups are invisible to geometric
points. -/
theorem torusCommHopfAlgProperty.eq_augmentation_of_geometricallyUnipotent
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H)
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
