/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import Mathlib.Algebra.BigOperators.Pi

/-!
# Representability of the component group

Let `H` be the coordinate Hopf algebra of a finite-type affine group over an algebraically closed
field. This file identifies the fppf quotient `H / H⁰` with the fppf points sheaf of the finite
constant group of connected components of `Spec H`.

The key point is stronger than local surjectivity. Every point of the constant component group
over a test algebra lifts to a point of `H`: its orthogonal idempotents split the test algebra into
components, and on each component one uses a chosen rational point of the corresponding connected
component of `Spec H`. The kernel calculation for the component coordinate morphism then identifies
the pointwise quotient with the constant-group points. Sheafifying this natural isomorphism gives
the desired representability.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom_surjective`: the component morphism is
  surjective on points over every test algebra.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentPointwiseQuotientMulEquiv`: the pointwise quotient by
  the identity component is the constant component group.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupFppfGroupObjectIso`: the fppf component-group
  quotient is represented by the finite constant group scheme, compatibly with its group
  structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Sections 6.7 and 14.

This completes the algebraically closed-field representability step of Layer 3, "Identity
component `G°` and component group `π₀(G)`", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    Fintype (ConnectedComponents (PrimeSpectrum H)) :=
  Fintype.ofFinite _

private noncomputable instance (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    DecidableEq (ConnectedComponents (PrimeSpectrum H)) :=
  Classical.decEq _

/-- A chosen rational point in each connected component of the spectrum. -/
private noncomputable def componentRepresentative
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (C : ConnectedComponents (PrimeSpectrum H)) :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) :=
  Classical.choose (rationalComponentMap_surjective H C)

@[simp]
private theorem rationalComponentMap_componentRepresentative
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (C : ConnectedComponents (PrimeSpectrum H)) :
    rationalComponentMap H (componentRepresentative H C) = C :=
  Classical.choose_spec (rationalComponentMap_surjective H C)

/-- The algebra map obtained by gluing the chosen component representatives along the
orthogonal idempotents of a constant-group point. -/
private noncomputable def componentPointLiftAlgHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points
      (R := k)
      (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A) :
    H →ₐ[k] A := by
  classical
  let C := ConnectedComponents (PrimeSpectrum H)
  let qFun : (C → k) →ₐ[k] A := q.ofConv.comp (ConstantGroup.functionAlgEquiv k C).symm.toAlgHom
  let e : C → A := fun D ↦ qFun (Pi.single D 1)
  have he : CompleteOrthogonalIdempotents e := by
    exact (CompleteOrthogonalIdempotents.single (fun _ : C ↦ k)).map qFun.toRingHom
  refine
    { toFun := fun x ↦ ∑ D, e D * algebraMap k A ((componentRepresentative H D).ofConv x)
      map_zero' := by simp
      map_add' := fun x y ↦ by
        simp only [map_add, mul_add, Finset.sum_add_distrib]
      map_one' := by
        simp only [map_one, mul_one, he.complete]
      map_mul' := fun x y ↦ ?_
      commutes' := fun a ↦ ?_ }
  · rw [Finset.sum_mul_sum]
    symm
    apply Finset.sum_congr rfl
    intro D _
    rw [Finset.sum_eq_single D]
    · rw [map_mul]
      calc
        e D * algebraMap k A ((componentRepresentative H D).ofConv x) *
            (e D * algebraMap k A ((componentRepresentative H D).ofConv y)) =
            (e D * e D) *
              (algebraMap k A ((componentRepresentative H D).ofConv x) *
                algebraMap k A ((componentRepresentative H D).ofConv y)) := by
          ring
        _ = e D * algebraMap k A
            ((componentRepresentative H D).ofConv x *
              (componentRepresentative H D).ofConv y) := by
          rw [he.idem, map_mul]
    · intro E _ hED
      calc
        e D * algebraMap k A ((componentRepresentative H D).ofConv x) *
            (e E * algebraMap k A ((componentRepresentative H E).ofConv y)) =
            (e D * e E) *
              (algebraMap k A ((componentRepresentative H D).ofConv x) *
                algebraMap k A ((componentRepresentative H E).ofConv y)) := by
          ring
        _ = 0 := by rw [he.ortho hED.symm, zero_mul]
    · simp
  · simp_rw [AlgHom.commutes]
    rw [← Finset.sum_mul, he.complete, one_mul]
    rw [Algebra.algebraMap_self_apply]

private theorem componentPointLiftAlgHom_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points
      (R := k)
      (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A)
    (x : H) :
    componentPointLiftAlgHom H A q x =
      ∑ D,
        q.ofConv ((ConstantGroup.functionAlgEquiv k
          (ConnectedComponents (PrimeSpectrum H))).symm (Pi.single D 1)) *
          algebraMap k A ((componentRepresentative H D).ofConv x) := by
  rfl

private theorem componentPointLiftAlgHom_comp_componentCoordinateMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points
      (R := k)
      (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A) :
    (componentPointLiftAlgHom H A q).comp (componentCoordinateMap H) = q.ofConv := by
  classical
  let C := ConnectedComponents (PrimeSpectrum H)
  let qFun : (C → k) →ₐ[k] A := q.ofConv.comp (ConstantGroup.functionAlgEquiv k C).symm.toAlgHom
  ext x
  rw [AlgHom.comp_apply, componentPointLiftAlgHom_apply]
  have hrepresentative (D : C) :
      (componentRepresentative H D).ofConv (componentCoordinateMap H x) =
        ConstantGroup.functionAlgEquiv k C x D := by
    have h := AlgHom.congr_fun
      (eval_componentCoordinateMap H (componentRepresentative H D)) x
    rw [rationalComponentMap_componentRepresentative, ConstantGroup.eval_apply] at h
    exact h
  simp_rw [hrepresentative]
  have hq : q.ofConv x = qFun (ConstantGroup.functionAlgEquiv k C x) := by
    dsimp only [qFun, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    rw [AlgEquiv.symm_apply_apply]
  have hqFun_sum :
      (∑ D, q.ofConv ((ConstantGroup.functionAlgEquiv k C).symm (Pi.single D 1)) *
          algebraMap k A (ConstantGroup.functionAlgEquiv k C x D)) =
        ∑ D, qFun (Pi.single D 1) *
          algebraMap k A (ConstantGroup.functionAlgEquiv k C x D) := by
    rfl
  rw [hqFun_sum, hq]
  let f := ConstantGroup.functionAlgEquiv k C x
  calc
    (∑ D, qFun (Pi.single D 1) * algebraMap k A (f D)) =
        ∑ D, qFun ((f D) • Pi.single D 1) := by
      apply Finset.sum_congr rfl
      intro D _
      rw [map_smul, Algebra.smul_def]
      ring
    _ = qFun (∑ D, (f D) • Pi.single D 1) := by rw [map_sum]
    _ = qFun f := congrArg qFun (pi_eq_sum_univ' f).symm

private theorem componentPointLiftAlgHom_componentCoordinateHom_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points
      (R := k)
      (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A)
    (x : ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) :
    (toConv (componentPointLiftAlgHom H A q)).ofConv
        ((componentCoordinateHom H).hom.toAlgHom x) = q.ofConv x := by
  simp only [BialgHom.coe_toAlgHom]
  rw [componentCoordinateHom_apply]
  simpa only [AlgHom.comp_apply] using
    AlgHom.congr_fun (componentPointLiftAlgHom_comp_componentCoordinateMap H A q) x

/-- The component-coordinate morphism on points over a commutative test algebra. -/
noncomputable def componentPointsHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := H) A →*
      HopfAlgebra.points
        (R := k)
        (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A :=
  AlgHom.mapDomain (componentCoordinateHom H).hom

/-- The component morphism on points is precomposition with the component coordinate map. -/
@[simp]
theorem componentPointsHom_apply
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (g : HopfAlgebra.points (R := k) (H := H) A) :
    componentPointsHom H A g =
      toConv (g.ofConv.comp (componentCoordinateHom H).hom.toAlgHom) := by
  exact AlgHom.mapDomain_apply (A := A) (componentCoordinateHom H).hom g

/-- The component-coordinate morphism is surjective on points over every commutative test
algebra. -/
theorem componentPointsHom_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    Function.Surjective (componentPointsHom H A) := by
  intro q
  refine ⟨toConv (componentPointLiftAlgHom H A q), ?_⟩
  apply ofConv_injective
  ext x
  rw [componentPointsHom_apply, ofConv_toConv, AlgHom.comp_apply,
    componentPointLiftAlgHom_componentCoordinateHom_apply]

private theorem quotientPointsSubgroup_identityComponent_eq_componentPointsHom_ker
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) A =
      (componentPointsHom H A).ker := by
  ext g
  rw [MonoidHom.mem_ker, componentPointsHom_apply,
    CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff]
  rw [kernelHopfIdeal_componentCoordinateHom]

/-- The group structure on the pointwise quotient, exposed locally for the first isomorphism
theorem. -/
noncomputable local instance componentPointwiseQuotientGroup
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    Group (CommHopfAlgCat.pointwiseQuotientGroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (isNormal_identityComponentHopfIdeal H) A) :=
  (CommHopfAlgCat.pointwiseQuotientGroup H.obj
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
    (isNormal_identityComponentHopfIdeal H) A).str

/-- The pointwise quotient by the identity component is canonically the group of points of the
finite constant component group. -/
noncomputable def componentPointwiseQuotientMulEquiv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k) :
    CommHopfAlgCat.pointwiseQuotientGroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (isNormal_identityComponentHopfIdeal H) A ≃*
      HopfAlgebra.points
        (R := k)
        (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) A := by
  let I := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let hI := isNormal_identityComponentHopfIdeal H
  let N := CommHopfAlgCat.quotientPointsSubgroup H.obj I A
  let phi := componentPointsHom H A
  let hN : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal H.obj I hI A
  let hker : phi.ker.Normal := phi.normal_ker
  let _ : N.Normal := hN
  let _ : phi.ker.Normal := hker
  let _ : Group (HopfAlgebra.points (R := k) (H := H) A ⧸ phi.ker) :=
    QuotientGroup.Quotient.group phi.ker
  exact (@QuotientGroup.quotientMulEquivOfEq _ _ N phi.ker hN hker
      (quotientPointsSubgroup_identityComponent_eq_componentPointsHom_ker H A)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (componentPointsHom H A)
      (componentPointsHom_surjective H A))

/-- The pointwise component-group equivalence sends the class of an ambient point to its image
under the component-coordinate morphism. -/
@[simp]
theorem componentPointwiseQuotientMulEquiv_mk
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (A : CommAlgCat.{u} k)
    (g : HopfAlgebra.points (R := k) (H := H) A) :
    componentPointwiseQuotientMulEquiv H A
        (CommHopfAlgCat.pointwiseQuotientMk H.obj
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
          (isNormal_identityComponentHopfIdeal H) A g) =
      componentPointsHom H A g := by
  let _ : (CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) A).Normal :=
    CommHopfAlgCat.quotientPointsSubgroup_normal H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (isNormal_identityComponentHopfIdeal H) A
  rw [CommHopfAlgCat.pointwiseQuotientMk_apply]
  rw [QuotientGroup.mk'_apply, componentPointwiseQuotientMulEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- The component morphism on points commutes with extension of the value algebra. -/
@[simp]
theorem mapPoints_componentPointsHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {A B : CommAlgCat.{u} k} (f : A ⟶ B)
    (g : HopfAlgebra.points (R := k) (H := H) A) :
    HopfAlgebra.mapPoints
        (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) f
        (componentPointsHom H A g) =
      componentPointsHom H B (HopfAlgebra.mapPoints (H := H) f g) := by
  exact DFunLike.congr_fun
    (AlgHom.mapValue_mapDomain (componentCoordinateHom H).hom f.hom) g

/-- The pointwise quotient functor by the identity component is naturally isomorphic to the
functor of points of the finite constant component group. -/
noncomputable def componentPointwiseQuotientNatIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.pointwiseQuotientFunctor H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (isNormal_identityComponentHopfIdeal H) ≅
      HopfAlgebra.pointsFunctor
        (R := k)
        (H := ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))) :=
  NatIso.ofComponents (fun A ↦
    eqToIso (CommHopfAlgCat.pointwiseQuotientFunctor_obj H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (isNormal_identityComponentHopfIdeal H) A) ≪≫
        (componentPointwiseQuotientMulEquiv H A).toGrpIso ≪≫
          eqToIso (HopfAlgebra.pointsFunctor_obj A).symm) <| by
    intro A B f
    have hbare :
        CommHopfAlgCat.mapPointwiseQuotient H.obj
            (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
            (isNormal_identityComponentHopfIdeal H) f ≫
          (componentPointwiseQuotientMulEquiv H B).toGrpIso.hom =
        (componentPointwiseQuotientMulEquiv H A).toGrpIso.hom ≫
          HopfAlgebra.mapPoints
            (H := ConstantGroup.coordinateRing k
              (ConnectedComponents (PrimeSpectrum H))) f := by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro q
      obtain ⟨g, rfl⟩ := CommHopfAlgCat.pointwiseQuotientMk_surjective H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (isNormal_identityComponentHopfIdeal H) A q
      simp only [GrpCat.hom_comp, MonoidHom.comp_apply, MulEquiv.toGrpIso_hom,
        MulEquiv.toMonoidHom_eq_coe, ConcreteCategory.hom_ofHom, MonoidHom.coe_coe]
      rw [CommHopfAlgCat.mapPointwiseQuotient_mk,
        componentPointwiseQuotientMulEquiv_mk,
        componentPointwiseQuotientMulEquiv_mk,
        mapPoints_componentPointsHom]
    have hpoints :
        eqToHom (HopfAlgebra.pointsFunctor_obj A).symm ≫
            (HopfAlgebra.pointsFunctor
              (R := k)
              (H := ConstantGroup.coordinateRing k
                (ConnectedComponents (PrimeSpectrum H)))).map f =
          HopfAlgebra.mapPoints
              (H := ConstantGroup.coordinateRing k
                (ConnectedComponents (PrimeSpectrum H))) f ≫
            eqToHom (HopfAlgebra.pointsFunctor_obj B).symm := by
      exact HopfAlgebra.pointsFunctor_map_eqToHom f
    simpa only [Iso.trans_hom, eqToIso.hom,
      CommHopfAlgCat.pointwiseQuotientFunctor_map,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id, hpoints] using congrArg (fun z ↦
        eqToHom (CommHopfAlgCat.pointwiseQuotientFunctor_obj H.obj
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
          (isNormal_identityComponentHopfIdeal H) A) ≫ z ≫
        eqToHom (HopfAlgebra.pointsFunctor_obj B).symm) hbare

/-- Before sheafification, the pointwise component quotient and the constant component group are
isomorphic as group objects in type-valued presheaves on the affine fppf site. -/
noncomputable def componentPointwiseQuotientPresheafGrpIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.pointwiseQuotientPresheafGrp H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (isNormal_identityComponentHopfIdeal H) ≅
      CommHopfAlgCat.pointsPresheafGrp
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) := by
  let e := Functor.isoWhiskerLeft (opOpEquivalence (CommAlgCat.{u} k)).functor
    (componentPointwiseQuotientNatIso H)
  let e' := Functor.isoWhiskerRight e GrpCat.uliftFunctor.{u + 1, u}
  exact eqToIso (CommHopfAlgCat.pointwiseQuotientPresheafGrp_eq H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (isNormal_identityComponentHopfIdeal H)) ≪≫
    CommHopfAlgCat.groupFunctorGrpIso e' ≪≫
      eqToIso (CommHopfAlgCat.pointsPresheafGrp.eq_1
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k
            (ConnectedComponents (PrimeSpectrum H))))).symm

/-- Before sheafification, the pointwise component quotient and the constant component group are
isomorphic as type-valued presheaves on the affine fppf site. -/
noncomputable def componentPointwiseQuotientPresheafIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (CommHopfAlgCat.pointwiseQuotientPresheafGrp H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
        (isNormal_identityComponentHopfIdeal H)).X ≅
      (CommHopfAlgCat.pointsPresheafGrp
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))))).X :=
  (Grp.forget _).mapIso (componentPointwiseQuotientPresheafGrpIso H)

/-- The fppf component-group quotient is represented by the finite constant group scheme,
compatibly with multiplication, the unit, and inversion. -/
noncomputable def componentGroupFppfGroupObjectIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    componentGroupFppfSheaf H ≅
      CommHopfAlgCat.pointsFppfGroupObject
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) := by
  let _ : (presheafToSheaf
      (CommAlgCat.fppfTopology k) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact eqToIso (CommHopfAlgCat.fppfQuotientSheaf_eq H.obj
      (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))
      (isNormal_identityComponentHopfIdeal H)) ≪≫
    (presheafToSheaf
      (CommAlgCat.fppfTopology k) (Type (u + 1))).mapGrp.mapIso
        (componentPointwiseQuotientPresheafGrpIso H) ≪≫
      eqToIso (CommHopfAlgCat.pointsFppfGroupObject.eq_1
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k
            (ConnectedComponents (PrimeSpectrum H))))).symm

/-- The underlying fppf sheaf of the component-group quotient is represented by the finite
constant group scheme on the connected components of the prime spectrum. -/
noncomputable def componentGroupFppfSheafIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (componentGroupFppfSheaf H).X ≅
      (CommHopfAlgCat.pointsFppfGroupObject
        (CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))))).X :=
  (Grp.forget _).mapIso (componentGroupFppfGroupObjectIso H)

end TauCeti.FiniteTypeCommHopfAlgCat
