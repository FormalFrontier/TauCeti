/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FaithfullyFlatPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.SemidirectProduct

/-!
# Solvability under faithfully flat affine group morphisms

Let `f : H ⟶ K` be a finite-type faithfully flat morphism of commutative Hopf algebras over a
field. Contravariantly, every algebraically closed point of `Spec H` lifts to a point of
`Spec K`. The resulting homomorphism on point groups is therefore surjective, so solvability of
the source affine group descends to the target.

This applies in particular to the canonical inclusion of the coordinate algebra of a
scheme-theoretic image into the coordinate algebra of its source. Combining image descent with
solvability of the conjugation semidirect product shows that the multiplication image of a normal
solvable closed subgroup and a solvable closed subgroup is solvable whenever that canonical
inclusion is faithfully flat.

## Main declarations

* `TauCeti.CommHopfAlgCat.isSolvable_points_of_faithfullyFlat`: solvability of point groups
  descends along a finite-type faithfully flat coordinate morphism.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.of_faithfullyFlat`: geometric
  solvability descends along such a morphism.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.image_of_faithfullyFlat`: a
  faithfully flat scheme-theoretic image of a solvable affine group is solvable.
* `TauCeti.geometricallySolvablePointsCommHopfAlgProperty.productOfNormal_of_faithfullyFlat`:
  the multiplication image of two solvable closed subgroups, the first normal, is solvable under
  the corresponding faithful-flatness hypothesis.

## References

* The Stacks Project, Tags 00HQ and 00FV, for algebraically closed points of faithfully flat
  finite-type algebras.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

This supplies the image-descent step for the solvable radical in Layer 6 of the ReductiveGroups
roadmap. Together with the semidirect-product source construction, it reduces binary-product
closure of solvable subgroup schemes to faithful flatness of the canonical source-to-image
morphism.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{v} R}
variable (L : Type w) [Field L] [Algebra R L] [IsAlgClosed L]

/-- Solvability of algebraically closed point groups descends along a finite-type faithfully flat
coordinate morphism.

The point-group homomorphism is surjective by faithfully flat point lifting. A quotient of a
solvable abstract group is solvable, giving the conclusion without imposing finite-type
hypotheses on either Hopf algebra separately. -/
theorem isSolvable_points_of_faithfullyFlat (f : H ⟶ K)
    (hfinite : f.hom.toAlgHom.FiniteType)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hK : Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := K) (CommAlgCat.of R L))) :
    Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R L)) := by
  let _ : Group.IsSolvable
      (HopfAlgebra.points (R := R) (H := K) (CommAlgCat.of R L)) := hK
  exact Group.isSolvable_of_surjective
    (G := HopfAlgebra.points (R := R) (H := K) (CommAlgCat.of R L))
    (G' := HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R L))
    (f := ((mapPointsFunctor f).app (CommAlgCat.of R L)).hom)
    (mapPointsFunctor_app_surjective_of_faithfullyFlat L f hfinite hflat)

end CommHopfAlgCat

namespace geometricallySolvablePointsCommHopfAlgProperty

variable {k : Type u} [Field k]
variable {H K : _root_.CommHopfAlgCat.{v} k}

/-- Geometric solvability descends along a finite-type faithfully flat coordinate morphism. -/
theorem of_faithfullyFlat (f : H ⟶ K) (hfinite : f.hom.toAlgHom.FiniteType)
    (hflat : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hK : geometricallySolvablePointsCommHopfAlgProperty k K) :
    geometricallySolvablePointsCommHopfAlgProperty k H := by
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hK ⊢
  exact CommHopfAlgCat.isSolvable_points_of_faithfullyFlat
    (AlgebraicClosure k) f hfinite hflat hK

/-- The scheme-theoretic image of a finite-type geometrically solvable affine group is
geometrically solvable when the source-to-image morphism is faithfully flat.

Finite type of the source coordinate algebra makes the canonical image inclusion a finite-type
algebra map. Faithful flatness then lets geometric solvability descend to the image. -/
theorem image_of_faithfullyFlat (f : H ⟶ K) [Algebra.FiniteType k K]
    (hK : geometricallySolvablePointsCommHopfAlgProperty k K)
    (hflat : (CommHopfAlgCat.imageι f).hom.toAlgHom.toRingHom.FaithfullyFlat) :
    geometricallySolvablePointsCommHopfAlgProperty k (CommHopfAlgCat.image f) := by
  have hfinite : (CommHopfAlgCat.imageι f).hom.toAlgHom.FiniteType := by
    apply AlgHom.FiniteType.of_comp_finiteType
      (f := Algebra.ofId k (CommHopfAlgCat.image f))
    rw [Algebra.comp_ofId]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact of_faithfullyFlat (CommHopfAlgCat.imageι f) hfinite hflat hK

/-- The multiplication image of a normal geometrically solvable closed subgroup and another
geometrically solvable closed subgroup is geometrically solvable when its canonical
source-to-image coordinate morphism is faithfully flat.

The coordinate algebra of the source is the conjugation semidirect product of the two quotient
Hopf algebras. Its point group is solvable by extension closure; the result then follows from
faithfully flat descent to its scheme-theoretic image. -/
theorem productOfNormal_of_faithfullyFlat (H : _root_.CommHopfAlgCat.{u} k)
    (I J : HopfIdeal k H) (hI : I.IsNormal)
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H I)]
    [Algebra.FiniteType k (CommHopfAlgCat.quotient H J)]
    (hIs : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H I))
    (hJs : geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H J))
    (hflat : (CommHopfAlgCat.imageι
      (CommHopfAlgCat.productMapOfNormal H I J hI)).hom.toAlgHom.toRingHom.FaithfullyFlat) :
    geometricallySolvablePointsCommHopfAlgProperty k
      (CommHopfAlgCat.productOfNormal H I J hI) := by
  apply image_of_faithfullyFlat
    (CommHopfAlgCat.productMapOfNormal H I J hI) ?_ hflat
  exact normalSemidirectProduct k H I J hI hIs hJs

end geometricallySolvablePointsCommHopfAlgProperty

end TauCeti
