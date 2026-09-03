/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# General-linear points cut out by Hopf ideals

This file transports the algebra-valued points of a quotient of the coordinate Hopf algebra of
`GLₙ` through `GeneralLinear.pointsMulEquiv`. The resulting matrix subgroup is characterized by
vanishing on the Hopf ideal and is functorial in the value algebra.

## Main declarations

* `TauCeti.GeneralLinear.hopfIdealPointsSubgroup`: the matrix subgroup cut out by a Hopf ideal
  in the general-linear coordinate ring.
* `TauCeti.GeneralLinear.mem_hopfIdealPointsSubgroup_iff`: membership is characterized by
  vanishing on the Hopf ideal.
* `TauCeti.GeneralLinear.hopfIdealPointsSubgroup_le_of_le`: larger Hopf ideals cut out smaller
  point subgroups.
* `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup`: functoriality of that subgroup in the
  value algebra.
* `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup_injective`: an injective homomorphism of
  value algebras induces an injective map of point subgroups.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u w w'

variable {R : Type u} [CommRing R] (n : ℕ)

section HopfIdealPoints

variable {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The subgroup of `GLₙ(A)` cut out by a Hopf ideal in the general-linear coordinate Hopf
algebra. -/
noncomputable def hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] : Subgroup (Matrix.GeneralLinearGroup (Fin n) A) :=
  (CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I (CommAlgCat.of R A)).map
    (pointsMulEquiv n).toMonoidHom

/-- Membership in the general-linear point subgroup cut out by a Hopf ideal is vanishing on
that ideal. -/
@[simp]
theorem mem_hopfIdealPointsSubgroup_iff
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] (g : Matrix.GeneralLinearGroup (Fin n) A) :
    g ∈ hopfIdealPointsSubgroup n I A ↔
      ∀ x ∈ I, ((pointsMulEquiv (R := R) n).symm g).ofConv x = 0 := by
  unfold hopfIdealPointsSubgroup
  rw [Subgroup.mem_map_equiv, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]

/-- A general-linear point lying in the subgroup cut out by a Hopf ideal remains in that
subgroup after transport to its matrix representation. -/
theorem pointsMulEquiv_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A]
    (q : HopfAlgebra.points
      (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A))
    (hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I (CommAlgCat.of R A)) :
    pointsMulEquiv n q ∈ hopfIdealPointsSubgroup n I A := by
  exact ⟨q, hq, rfl⟩

/-- A point pulled back along a coordinate morphism that kills a Hopf ideal lies in the
general-linear subgroup cut out by that ideal. -/
theorem pointsMulEquiv_mapPointsFunctor_mem_hopfIdealPointsSubgroup
    {H : CommHopfAlgCat.{u} R}
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (φ : coordinateHopfAlgebra R n ⟶ H)
    (hφ : I.toIdeal ≤ RingHom.ker φ.hom.toAlgHom.toRingHom)
    (A : Type w) [CommRing A] [Algebra R A]
    (p : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R A)) :
    pointsMulEquiv n ((CommHopfAlgCat.mapPointsFunctor φ).app (CommAlgCat.of R A) p) ∈
      hopfIdealPointsSubgroup n I A := by
  let q : HopfAlgebra.points
      (R := R) (H := coordinateHopfAlgebra R n) (CommAlgCat.of R A) :=
    (CommHopfAlgCat.mapPointsFunctor φ).app (CommAlgCat.of R A) p
  apply pointsMulEquiv_mem_hopfIdealPointsSubgroup n I A q
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  dsimp only [q]
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply]
  have hx' := hφ hx
  rw [RingHom.mem_ker] at hx'
  have hxmap : φ.hom x = 0 := by
    simpa only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx'
  rw [hxmap, map_zero]

/-- Applying a value-algebra homomorphism entrywise preserves the general-linear point subgroup
cut out by a Hopf ideal. -/
theorem map_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B)
    {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ hopfIdealPointsSubgroup n I A) :
    Matrix.GeneralLinearGroup.map φ.toRingHom g ∈ hopfIdealPointsSubgroup n I B := by
  obtain ⟨q, hq, rfl⟩ := hg
  refine ⟨AlgHom.mapValue φ q,
    CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup
      (coordinateHopfAlgebra R n) I φ hq, ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom] using pointsMulEquiv_mapValue n φ q

/-- The map between general-linear point subgroups cut out by the same Hopf ideal, induced by a
homomorphism of value algebras. -/
noncomputable def mapHopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B) :
    hopfIdealPointsSubgroup n I A →* hopfIdealPointsSubgroup n I B :=
  (((Matrix.GeneralLinearGroup.map φ.toRingHom).domRestrict
    (hopfIdealPointsSubgroup n I A)).codRestrict
      (hopfIdealPointsSubgroup n I B)
      fun g => map_mem_hopfIdealPointsSubgroup n I φ g.property)

/-- The induced map on a general-linear Hopf-ideal point subgroup applies the value-algebra
homomorphism entrywise. -/
@[simp]
theorem coe_mapHopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (φ : A →ₐ[R] B)
    (g : hopfIdealPointsSubgroup n I A) :
    (mapHopfIdealPointsSubgroup n I φ g : Matrix.GeneralLinearGroup (Fin n) B) =
      Matrix.GeneralLinearGroup.map φ.toRingHom g := by
  rfl

/-- The identity value-algebra homomorphism induces the identity on a general-linear Hopf-ideal
point subgroup. -/
@[simp]
theorem mapHopfIdealPointsSubgroup_id
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (A : Type w)
    [CommRing A] [Algebra R A] :
    mapHopfIdealPointsSubgroup n I (AlgHom.id R A) =
      MonoidHom.id (hopfIdealPointsSubgroup n I A) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  have h_id : (AlgHom.id R A).toRingHom = RingHom.id A := AlgHom.id_toRingHom R A
  rw [coe_mapHopfIdealPointsSubgroup, MonoidHom.id_apply, h_id,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]

/-- Maps between general-linear Hopf-ideal point subgroups preserve composition of value-algebra
homomorphisms. -/
@[simp]
theorem mapHopfIdealPointsSubgroup_comp
    {C : Type*} [CommRing C] [Algebra R C]
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    mapHopfIdealPointsSubgroup n I (ψ.comp φ) =
      (mapHopfIdealPointsSubgroup n I ψ).comp
        (mapHopfIdealPointsSubgroup n I φ) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  have h_comp : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom :=
    AlgHom.comp_toRingHom ψ φ
  rw [coe_mapHopfIdealPointsSubgroup, MonoidHom.comp_apply,
    coe_mapHopfIdealPointsSubgroup, coe_mapHopfIdealPointsSubgroup,
    h_comp, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]

/-- An injective homomorphism of value algebras induces an injective map of general-linear
Hopf-ideal point subgroups: reading a matrix point over a subalgebra as a point over the ambient
algebra loses no information. -/
theorem mapHopfIdealPointsSubgroup_injective
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapHopfIdealPointsSubgroup n I φ) := by
  have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin n) φ.toRingHom) :=
    Units.map_injective (Matrix.map_injective hφ)
  intro g g' h
  refine Subtype.ext (hmap ?_)
  rw [← coe_mapHopfIdealPointsSubgroup, ← coe_mapHopfIdealPointsSubgroup, h]

/-- Larger Hopf ideals cut out smaller general-linear point subgroups. -/
theorem hopfIdealPointsSubgroup_le_of_le
    {I J : HopfIdeal R (coordinateHopfAlgebra R n)} (hIJ : I ≤ J)
    (A : Type w) [CommRing A] [Algebra R A] :
    hopfIdealPointsSubgroup n J A ≤ hopfIdealPointsSubgroup n I A :=
  Subgroup.map_mono (CommHopfAlgCat.quotientPointsSubgroup_le_of_le
    (coordinateHopfAlgebra R n) hIJ (CommAlgCat.of R A))

end HopfIdealPoints

end TauCeti.GeneralLinear
