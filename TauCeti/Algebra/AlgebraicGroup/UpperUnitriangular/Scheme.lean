/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.FunctorOfPoints
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.FiniteType

/-!
# The upper-unitriangular group scheme

For a commutative ring `R`, the polynomial Hopf algebra on the entries strictly above the
diagonal represents the upper-unitriangular group `U_n`.  The entrywise inclusion of
upper-unitriangular matrices into `GL_n` is represented by a surjective coordinate Hopf-algebra
morphism, and hence gives a closed immersion of affine group schemes.

The construction includes rank zero and the zero ring.  As in the existing general-linear
scheme interface, scheme-valued points are stated in the same universe as the base ring.

## Main declarations

* `TauCeti.UpperUnitriangular.coordinateMap`: the coordinate morphism
  `O(GL_n) ⟶ O(U_n)`.
* `TauCeti.UpperUnitriangular.groupScheme`: the finite-type affine upper-unitriangular group
  scheme on a finite linearly ordered index type.
* `TauCeti.UpperUnitriangular.inclusion`: the closed immersion `U_n ⟶ GL_n`.
* `TauCeti.UpperUnitriangular.schemePointsMulEquiv`: scheme-valued points are
  upper-unitriangular matrices on the chosen index type.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

The functor-of-points recovery follows the pattern used for root subgroups in
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup`.
-/

public section

open CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.UpperUnitriangular

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

section CoordinateMap

variable {A : Type w} [CommRing A] [Algebra R A]

/-- On algebra-valued points, include an upper-unitriangular matrix into the general linear
group. -/
noncomputable def inclusionPoints :
    WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A) →*
      WithConv (GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A) :=
  (GeneralLinear.pointsMulEquiv (R := R) n).symm.toMonoidHom.comp
    ((upperUnitriangularGroup (Fin n) A).subtype.comp
      (pointsMulEquiv (R := R) (A := A) (Fin n)).toMonoidHom)

/-- The general-linear matrix attached to `inclusionPoints f` is the underlying matrix of the
upper-unitriangular point attached to `f`. -/
@[simp]
theorem pointToGeneralLinear_inclusionPoints
    (f : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    GeneralLinear.pointToGeneralLinear n (inclusionPoints (R := R) n f) =
      (pointsMulEquiv R (Fin n) f : upperUnitriangularGroup (Fin n) A) := by
  simp [inclusionPoints]

/-- Inclusion of upper-unitriangular points commutes with extension of the value algebra. -/
theorem mapValue_inclusionPoints {B : Type w} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra R n) φ
        (inclusionPoints (R := R) n f) =
      inclusionPoints (R := R) n
        (AlgHom.mapValue (H := coordinateHopfAlgebra R (Fin n)) φ f) := by
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := B) n).injective
  calc
    GeneralLinear.pointsMulEquiv n
        (AlgHom.mapValue (H := GeneralLinear.coordinateHopfAlgebra R n) φ
          (inclusionPoints (R := R) n f)) =
        Matrix.GeneralLinearGroup.map φ.toRingHom
          (GeneralLinear.pointsMulEquiv n (inclusionPoints (R := R) n f)) :=
      GeneralLinear.pointsMulEquiv_mapValue n φ _
    _ = (UpperUnitriangularGroup.map φ.toRingHom (pointsMulEquiv R (Fin n) f) :
          upperUnitriangularGroup (Fin n) B) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        pointToGeneralLinear_inclusionPoints]
      exact (UpperUnitriangularGroup.coe_map φ.toRingHom _).symm
    _ = GeneralLinear.pointsMulEquiv n
        (inclusionPoints (R := R) n
          (AlgHom.mapValue (H := coordinateHopfAlgebra R (Fin n)) φ f)) := by
      rw [GeneralLinear.pointsMulEquiv_apply,
        pointToGeneralLinear_inclusionPoints, pointsMulEquiv_mapValue]

end CoordinateMap

/-- The natural inclusion from upper-unitriangular points to general-linear points. -/
noncomputable def inclusionPointsMap :
    HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R (Fin n)) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n) where
  app A := GrpCat.ofHom (inclusionPoints (R := R) (A := A) n)
  naturality _ _ φ := by
    ext f
    exact (mapValue_inclusionPoints (R := R) n φ.hom f).symm

/-- The coordinate morphism `O(GL_n) ⟶ O(U_n)` recovered from the natural inclusion on
points. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R n ⟶ coordinateHopfAlgebra R (Fin n) :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (inclusionPointsMap.{u, u} (R := R) n)).unop

/-- Precomposition by `coordinateMap` is the upper-unitriangular inclusion on points. -/
theorem mapPointsFunctor_coordinateMap :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u} (coordinateMap R n) :
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R (Fin n)) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := GeneralLinear.coordinateHopfAlgebra R n)) =
      inclusionPointsMap.{u, u} (R := R) n := by
  unfold coordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On every same-universe value algebra, `coordinateMap` induces the ordinary inclusion of
upper-unitriangular matrices. -/
@[simp]
theorem mapPointsFunctor_coordinateMap_app (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R (Fin n)) A) :
    toConv (f.ofConv.comp ↑(CommHopfAlgCat.Hom.hom (coordinateMap R n))) =
      inclusionPoints (R := R) n f := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply, mapPointsFunctor_coordinateMap]
  rfl

private theorem pointsMulEquiv_id_apply (i j : Fin n) :
    ((pointsMulEquiv R (Fin n)
        (toConv (AlgHom.id R (coordinateHopfAlgebra R (Fin n)))) :
      upperUnitriangularGroup (Fin n) (coordinateHopfAlgebra R (Fin n))) :
        Matrix.GeneralLinearGroup (Fin n) (coordinateHopfAlgebra R (Fin n))) i j =
      coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
  rw [pointsMulEquiv_apply, pointToUpperUnitriangular_apply, AlgHom.id_apply]

/-- The coordinate morphism sends a generic general-linear matrix entry to the corresponding
entry of the generic upper-unitriangular matrix. -/
@[simp]
theorem coordinateMap_genericMatrix_apply (i j : Fin n) :
    (coordinateMap R n).hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
  let e : WithConv
      (coordinateHopfAlgebra R (Fin n) →ₐ[R] coordinateHopfAlgebra R (Fin n)) :=
    toConv (AlgHom.id R (coordinateHopfAlgebra R (Fin n)))
  have h := congrArg WithConv.ofConv
    (mapPointsFunctor_coordinateMap_app R n
      (CommAlgCat.of R (coordinateHopfAlgebra R (Fin n))) e)
  have h' := congrArg (fun f ↦ f
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
        (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j))))) h
  calc
    (coordinateMap R n).hom
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
            (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
        (inclusionPoints (R := R) n e).ofConv
          (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
            (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) := by
      simpa only [BialgHom.coe_toAlgHom, e, WithConv.ofConv_toConv, AlgHom.id_comp] using h'
    _ = GeneralLinear.pointToGeneralLinear n (inclusionPoints (R := R) n e) i j :=
      (GeneralLinear.pointToGeneralLinear_apply (R := R) n
        (inclusionPoints (R := R) n e) i j).symm
    _ = ((pointsMulEquiv R (Fin n) e :
          upperUnitriangularGroup (Fin n) (coordinateHopfAlgebra R (Fin n))) :
            Matrix.GeneralLinearGroup (Fin n) (coordinateHopfAlgebra R (Fin n))) i j := by
      rw [pointToGeneralLinear_inclusionPoints]
    _ = coordinateHopfAlgebraAlgEquiv R (Fin n) (genericMatrix R (Fin n) i j) := by
      exact pointsMulEquiv_id_apply R n i j

private theorem coordinateMap_toAlgHom_surjective :
    Function.Surjective (coordinateMap R n).hom.toAlgHom := by
  intro x
  obtain ⟨p, rfl⟩ := (coordinateHopfAlgebraAlgEquiv R (Fin n)).surjective x
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact ⟨algebraMap R (GeneralLinear.coordinateHopfAlgebra R n) r, by simp⟩
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p ij hp =>
      obtain ⟨a, ha⟩ := hp
      let xij := GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
        (GeneralLinear.coordinateRingMap R n
          (MvPolynomial.X (ij.1.1, ij.1.2)))
      refine ⟨a * xij, ?_⟩
      calc
        (coordinateMap R n).hom (a * xij) =
            (coordinateMap R n).hom a * (coordinateMap R n).hom xij :=
          (coordinateMap R n).hom.map_mul a xij
        _ = coordinateHopfAlgebraAlgEquiv R (Fin n) p *
            coordinateHopfAlgebraAlgEquiv R (Fin n)
              (genericMatrix R (Fin n) ij.1.1 ij.1.2) :=
          congrArg₂ (fun x y ↦ x * y) ha
            (coordinateMap_genericMatrix_apply R n ij.1.1 ij.1.2)
        _ = coordinateHopfAlgebraAlgEquiv R (Fin n) (p * MvPolynomial.X ij) := by
          rw [genericMatrix_apply_of_lt R (Fin n) ij.2, map_mul]

/-- The coordinate morphism `O(GL_n) ⟶ O(U_n)` is surjective. -/
theorem coordinateMap_surjective : Function.Surjective (coordinateMap R n).hom :=
  coordinateMap_toAlgHom_surjective R n

/-! ### The group scheme and its closed immersion -/

section GroupScheme

variable (m : Type) [Fintype m] [LinearOrder m]

/-- The upper-unitriangular group scheme obtained by applying relative spectrum to its
coordinate Hopf algebra. -/
noncomputable def groupScheme : Grp (Over (AlgebraicGeometry.Spec (CommRingCat.of R))) :=
  (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
    (Opposite.op (coordinateHopfAlgebra R m))

/-- The upper-unitriangular group scheme is the Hopf spectrum of its coordinate algebra. -/
theorem groupScheme_def :
    groupScheme R m =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op (coordinateHopfAlgebra R m)) := by
  unfold groupScheme
  rfl

/-- The underlying scheme is the spectrum of the upper-unitriangular coordinate Hopf algebra. -/
theorem groupScheme_X_left :
    (groupScheme R m).X.left =
      AlgebraicGeometry.Spec (CommRingCat.of (coordinateHopfAlgebra R m)) := by
  simpa only [groupScheme] using
    hopfSpec_obj_X_left R (coordinateHopfAlgebra R m)

end GroupScheme

/-- The closed immersion of the upper-unitriangular group scheme into `GL_n`. -/
noncomputable def inclusion : groupScheme R (Fin n) ⟶ GeneralLinear.groupScheme R n :=
  eqToHom (groupScheme_def R (Fin n)) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R n).op ≫
    eqToHom (GeneralLinear.groupScheme_def R n).symm

/-- The upper-unitriangular inclusion is relative spectrum applied contravariantly to
`coordinateMap`. -/
theorem inclusion_def :
    inclusion R n =
      eqToHom (groupScheme_def R (Fin n)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (coordinateMap R n).op ≫
        eqToHom (GeneralLinear.groupScheme_def R n).symm := by
  unfold inclusion
  rfl

/-- The upper-unitriangular group scheme is affine. -/
instance isAffine_groupScheme (m : Type) [Fintype m] [LinearOrder m] :
    AlgebraicGeometry.IsAffine (groupScheme R m).X.left := by
  rw [groupScheme_X_left]
  exact AlgebraicGeometry.isAffine_Spec _

/-- The structural morphism of the upper-unitriangular group scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme (m : Type) [Fintype m] [LinearOrder m] :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R m).X.hom := by
  rw [groupScheme_def]
  exact (algebraFiniteType_iff_locallyOfFiniteType_hopfSpec R
    (coordinateHopfAlgebra R m)).mp
      (by
        rw [← finiteTypeCoordinateHopfAlgebra_obj]
        exact (finiteTypeCoordinateHopfAlgebra R m).property)

/-- The inclusion `U_n ⟶ GL_n` is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R n).hom.hom.left := by
  let e₁ := (eqToHom (groupScheme_def R (Fin n))).hom.hom.left
  let c := ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
    (coordinateMap R n).op).hom.hom.left
  let e₂ := (eqToHom (GeneralLinear.groupScheme_def R n).symm).hom.hom.left
  have he₁ : IsIso e₁ :=
    ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))).mapIso
        (eqToIso (groupScheme_def R (Fin n))))).isIso_hom
  have he₂ : IsIso e₂ :=
    ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))).mapIso
        (eqToIso (GeneralLinear.groupScheme_def R n).symm))).isIso_hom
  have hc : AlgebraicGeometry.IsClosedImmersion c := by
    dsimp only [c]
    rw [CommHopfAlgCat.isClosedImmersion_hopfSpec_map_iff]
    exact coordinateMap_surjective R n
  have he₁c : AlgebraicGeometry.IsClosedImmersion (e₁ ≫ c) :=
    (@MorphismProperty.cancel_left_of_respectsIso
      _ _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ e₁ c he₁).2 hc
  have he₁ce₂ : AlgebraicGeometry.IsClosedImmersion ((e₁ ≫ c) ≫ e₂) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      _ _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ (e₁ ≫ c) e₂ he₂).2 he₁c
  rw [inclusion_def]
  simp only [Grp.comp', Mon.comp_hom', Over.comp_left]
  exact he₁ce₂

/-! ### Scheme-valued points -/

section SchemePoints

section

variable {R} (m : Type) [Fintype m] [LinearOrder m]
  (A : Type u) [CommRing A] [Algebra R A]

/-- The canonical equivalence from algebra-valued points to scheme-valued
upper-unitriangular points. -/
noncomputable def groupSchemePointMulEquiv :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) ≃*
      ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
          (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :=
  CommHopfAlgCat.mapMulEquivOfPresentation
    (coordinateHopfAlgebra R m) A (groupScheme_def R m)

/-- The underlying spectrum map of the canonical algebra-to-scheme point equivalence. -/
@[simp]
theorem groupSchemePointMulEquiv_apply_left
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (groupSchemePointMulEquiv m A f).left =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R m).symm := by
  simpa only [groupSchemePointMulEquiv] using
    CommHopfAlgCat.mapMulEquivOfPresentation_apply_left
      (coordinateHopfAlgebra R m) A (groupScheme_def R m)
        (groupScheme_X_left R m) f

/-- Scheme-valued upper-unitriangular points are upper-unitriangular matrices. -/
noncomputable def schemePointsMulEquiv :
    ((AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) ≃*
      upperUnitriangularGroup m A :=
  (groupSchemePointMulEquiv m A).symm.trans (pointsMulEquiv R m)

/-- A scheme point presented by an algebra point corresponds to the same upper-unitriangular
matrix under `schemePointsMulEquiv`. -/
@[simp]
theorem schemePointsMulEquiv_groupSchemePointMulEquiv
    (q : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    schemePointsMulEquiv m A (groupSchemePointMulEquiv m A q) =
      pointsMulEquiv R m q := by
  simp [schemePointsMulEquiv]

/-- Evaluating the scheme-points equivalence directly on a scheme morphism. -/
theorem schemePointsMulEquiv_apply
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :
    schemePointsMulEquiv m A p =
      pointsMulEquiv R m ((groupSchemePointMulEquiv m A).symm p) := by
  unfold schemePointsMulEquiv
  rfl

/-- The inverse scheme-points equivalence presents an upper-unitriangular matrix as the
corresponding spectrum point. -/
@[simp]
theorem schemePointsMulEquiv_symm_apply (g : upperUnitriangularGroup m A) :
    (schemePointsMulEquiv m A).symm g =
      groupSchemePointMulEquiv m A ((pointsMulEquiv R m).symm g) := by
  rfl

variable {B : Type u} [CommRing B] [Algebra R B]

/-- The scheme-valued point identification is covariantly natural in the value algebra. An
`R`-algebra map `A → B` becomes precomposition by the reversed spectrum map and acts entrywise on
the corresponding upper-unitriangular matrix. -/
theorem schemePointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R m).X) :
    schemePointsMulEquiv m B
        ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (AlgebraicGeometry.Spec (CommRingCat.of R)) ≫ p) =
      UpperUnitriangularGroup.map φ.toRingHom (schemePointsMulEquiv m A p) := by
  let q : WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
    (groupSchemePointMulEquiv m A).symm p
  have hpre :
      (groupSchemePointMulEquiv m B).symm
          ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
            (AlgebraicGeometry.Spec (CommRingCat.of R)) ≫ p) =
        HopfAlgebra.mapPoints (H := coordinateHopfAlgebra R m)
          (CommAlgCat.ofHom φ) q := by
    simpa only [q, groupSchemePointMulEquiv] using
      CommHopfAlgCat.mapMulEquivOfPresentation_mapValue
        (coordinateHopfAlgebra R m) φ (groupScheme_def R m) p
  simp only [schemePointsMulEquiv, MulEquiv.trans_apply]
  rw [hpre, HopfAlgebra.mapPoints_apply, ← AlgHom.mapValue_apply]
  exact pointsMulEquiv_mapValue (R := R) m φ q

end

variable {R} (A : Type u) [CommRing A] [Algebra R A]

private theorem groupSchemePointMulEquiv_comp_inclusion
    (q : WithConv (coordinateHopfAlgebra R (Fin n) →ₐ[R] A)) :
    groupSchemePointMulEquiv (Fin n) A q ≫ (inclusion R n).hom.hom =
      GeneralLinear.groupSchemePointMulEquiv n A (inclusionPoints (R := R) n q) := by
  rw [inclusion_def, ← mapPointsFunctor_coordinateMap_app R n (CommAlgCat.of R A) q]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain
    (R := R) A (GeneralLinear.groupScheme_def R n) (groupScheme_def R (Fin n))
      (GeneralLinear.groupSchemePointMulEquiv n A) (groupSchemePointMulEquiv (Fin n) A)
      (GeneralLinear.groupSchemePointMulEquiv_apply_left n A)
      (groupSchemePointMulEquiv_apply_left (Fin n) A) (coordinateMap R n) q

/-- Composing a scheme-valued point with `U_n ⟶ GL_n` is ordinary subgroup inclusion on
matrices. -/
@[simp]
theorem schemePointsMulEquiv_comp_inclusion
    (p : (AlgebraicGeometry.Spec (CommRingCat.of A)).asOver
        (AlgebraicGeometry.Spec (CommRingCat.of R)) ⟶ (groupScheme R (Fin n)).X) :
    GeneralLinear.schemePointsMulEquiv n A (p ≫ (inclusion R n).hom.hom) =
      (schemePointsMulEquiv (Fin n) A p : upperUnitriangularGroup (Fin n) A) := by
  obtain ⟨q, rfl⟩ := (groupSchemePointMulEquiv (Fin n) A).surjective p
  rw [groupSchemePointMulEquiv_comp_inclusion,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    GeneralLinear.pointsMulEquiv_apply,
    pointToGeneralLinear_inclusionPoints]

end SchemePoints

end TauCeti.UpperUnitriangular
