/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
public import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Semisimple unipotent affine groups are trivial

Over a perfect field, a point that is both semisimple and unipotent is the identity. This file
turns that pointwise fact into a scheme-theoretic rigidity statement: if a reduced finite-type
commutative Hopf algebra has only semisimple and unipotent geometric points, then its counit is an
isomorphism with the base field. Reducedness is essential because geometric points do not detect
infinitesimal group schemes such as `μₚ` and `αₚ` in characteristic `p`.

The main application is to diagonalizable groups. Every point of a diagonalizable group is
semisimple, and semisimplicity is reflected by a closed immersion. It follows that every reduced
finite-type closed subgroup of a diagonalizable group whose geometric points are unipotent is the
trivial group. This is the rigidity input for the reductive-groups roadmap: once the unipotent
radical is constructed, it proves that the unipotent radical of a torus is trivial.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.counitBialgEquivOfGeometricallySemisimpleUnipotent`: the
  counit equivalence for a reduced group with semisimple and unipotent geometric points.
* `TauCeti.DiagonalizableGroup.quotientCounitBialgEquivOfGeometricallyUnipotent`: a reduced
  unipotent closed subgroup of a finite-type diagonalizable group is trivial.
* `TauCeti.DiagonalizableGroup.eq_augmentation_of_geometricallyUnipotent`: its
  defining Hopf ideal is the augmentation ideal.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 12.40.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap. It
supplies the trivial-unipotent-subgroup argument needed to prove that tori are reductive, using
the geometric unipotence and diagonalizable-group semisimplicity developed in Layers 4 and 5.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

namespace HopfAlgebra

variable {k H L : Type u} [Field k]
variable [CommRing H] [_root_.HopfAlgebra k H]
variable [Field L] [Algebra k L] [PerfectField L]

/-- A point that is both semisimple and unipotent is the identity. -/
theorem IsSemisimplePoint.eq_one_of_isUnipotent {g : WithConv (H →ₐ[k] L)}
    (hsemisimple : IsSemisimplePoint g) (hunipotent : IsUnipotentPoint g) :
    g = 1 := by
  rw [isSemisimplePoint_iff_unipotentPart_eq_one] at hsemisimple
  rw [Point.isUnipotentPoint_iff_unipotentPart_eq_self] at hunipotent
  exact hunipotent.symm.trans hsemisimple

end HopfAlgebra

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- The counit of a reduced finite-type commutative Hopf algebra is bijective when every
geometric point is both semisimple and unipotent. -/
theorem counitBialgHom_bijective_of_geometricallySemisimple_of_geometricallyUnipotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k H.obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) :
    Function.Bijective (Bialgebra.counitBialgHom k H) := by
  constructor
  · intro x y hxy
    apply eq_of_forall_algHom_apply_eq (k := k) (A := H) (K := AlgebraicClosure k)
    intro f
    let g : WithConv (H →ₐ[k] AlgebraicClosure k) := toConv f
    have hgsemisimple :=
      (geometricallySemisimplePointsCommHopfAlgProperty_iff k H.obj).mp hsemisimple g
    have hgunipotent :=
      (geometricallyUnipotentPointsCommHopfAlgProperty_iff k H.obj).mp hunipotent g
    have hg : g = 1 := hgsemisimple.eq_one_of_isUnipotent hgunipotent
    have hfx : f x = algebraMap k (AlgebraicClosure k) (Coalgebra.counit x) := by
      have := congrArg (fun q : WithConv (H →ₐ[k] AlgebraicClosure k) ↦ q.ofConv x) hg
      simpa [g, AlgHom.convOne_apply] using this
    have hfy : f y = algebraMap k (AlgebraicClosure k) (Coalgebra.counit y) := by
      have := congrArg (fun q : WithConv (H →ₐ[k] AlgebraicClosure k) ↦ q.ofConv y) hg
      simpa [g, AlgHom.convOne_apply] using this
    rw [hfx, hfy]
    change Coalgebra.counit x = Coalgebra.counit y at hxy
    rw [hxy]
  · intro r
    exact ⟨algebraMap k H r, by simp⟩

/-- A reduced finite-type affine group whose geometric points are all semisimple and unipotent is
the trivial group: its counit is a bialgebra equivalence with the base field. -/
noncomputable def counitBialgEquivOfGeometricallySemisimpleUnipotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k H.obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) :
    H ≃ₐc[k] k :=
  BialgEquiv.ofBijective (Bialgebra.counitBialgHom k H)
    (counitBialgHom_bijective_of_geometricallySemisimple_of_geometricallyUnipotent
      H hsemisimple hunipotent)

/-- The equivalence from a geometrically semisimple and unipotent affine group to the base field
is its counit. -/
@[simp]
theorem counitBialgEquivOfGeometricallySemisimpleUnipotent_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k H.obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) (x : H) :
    counitBialgEquivOfGeometricallySemisimpleUnipotent H hsemisimple hunipotent x =
      Coalgebra.counit x := by
  rfl

/-- The inverse counit equivalence is the structure map from the base field. -/
@[simp]
theorem counitBialgEquivOfGeometricallySemisimpleUnipotent_symm_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k H.obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k H.obj) (r : k) :
    (counitBialgEquivOfGeometricallySemisimpleUnipotent H hsemisimple hunipotent).symm r =
      algebraMap k H r := by
  let e := counitBialgEquivOfGeometricallySemisimpleUnipotent H hsemisimple hunipotent
  apply e.injective
  change e (e.symm r) = e (algebraMap k H r)
  rw [e.apply_symm_apply]
  exact (Bialgebra.counit_algebraMap (R := k) (A := H) r).symm

/-- A Hopf ideal is the augmentation ideal when its quotient is reduced, finite type, and has
only semisimple and unipotent geometric points. Equivalently, the closed subgroup cut out by the
ideal is trivial. -/
theorem eq_augmentation_of_geometricallySemisimple_of_geometricallyUnipotent
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    [IsReduced (quotient H I)]
    (hsemisimple : geometricallySemisimplePointsCommHopfAlgProperty k (quotient H I).obj)
    (hunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k (quotient H I).obj) :
    I = HopfIdeal.augmentation k H := by
  apply HopfIdeal.ext
  intro x
  rw [HopfIdeal.mem_augmentation]
  constructor
  · exact I.counit_eq_zero
  · intro hx
    rw [← HopfIdeal.mem_toIdeal]
    apply (mkQuotient_eq_zero_iff H I x).mp
    let e := counitBialgEquivOfGeometricallySemisimpleUnipotent
      (quotient H I) hsemisimple hunipotent
    apply e.injective
    change Coalgebra.counit (R := k) (toBialgHom (mkQuotient H I) x) =
      Coalgebra.counit (R := k) (0 : quotient H I)
    simpa only [CoalgHomClass.counit_comp_apply, map_zero] using hx

end FiniteTypeCommHopfAlgCat

namespace DiagonalizableGroup

variable (k : Type u) [Field k]

/-- A reduced finite-type closed subgroup of a diagonalizable group is trivial when all of its
geometric points are unipotent.

The closed subgroup is represented by the quotient of `k[G]` by `I`. No normality or connectedness
hypothesis is needed: every quotient point embeds into the diagonalizable ambient group, hence is
semisimple, and a semisimple unipotent point is the identity. -/
noncomputable def quotientCounitBialgEquivOfGeometricallyUnipotent
    (G : FGCommGrpCat.{u})
    (I : HopfIdeal k (coordinateRing k G))
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient (coordinateRing k G) I)]
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (coordinateRing k G) I).obj) :
    FiniteTypeCommHopfAlgCat.quotient (coordinateRing k G) I ≃ₐc[k] k := by
  apply FiniteTypeCommHopfAlgCat.counitBialgEquivOfGeometricallySemisimpleUnipotent _ _ hI
  apply geometricallySemisimplePointsCommHopfAlgProperty_of_surjective k
    (FiniteTypeCommHopfAlgCat.mkQuotient (coordinateRing k G) I).hom
    (Ideal.Quotient.mkₐ_surjective k I.toIdeal)
  exact geometricallySemisimplePointsCommHopfAlgProperty k G

/-- The defining Hopf ideal of a reduced finite-type unipotent closed subgroup of a
diagonalizable group is the augmentation ideal. Thus the closed subgroup is the identity
subgroup, not merely abstractly isomorphic to it. -/
theorem eq_augmentation_of_geometricallyUnipotent
    (G : FGCommGrpCat.{u})
    (I : HopfIdeal k (coordinateRing k G))
    [IsReduced (FiniteTypeCommHopfAlgCat.quotient (coordinateRing k G) I)]
    (hI : geometricallyUnipotentPointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (coordinateRing k G) I).obj) :
    I = HopfIdeal.augmentation k (coordinateRing k G) := by
  apply
    FiniteTypeCommHopfAlgCat.eq_augmentation_of_geometricallySemisimple_of_geometricallyUnipotent
      (coordinateRing k G) I _ hI
  apply geometricallySemisimplePointsCommHopfAlgProperty_of_surjective k
    (FiniteTypeCommHopfAlgCat.mkQuotient (coordinateRing k G) I).hom
    (Ideal.Quotient.mkₐ_surjective k I.toIdeal)
  exact geometricallySemisimplePointsCommHopfAlgProperty k G

end DiagonalizableGroup

end TauCeti
