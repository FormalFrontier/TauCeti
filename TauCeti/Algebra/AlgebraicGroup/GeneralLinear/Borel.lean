/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
import TauCeti.CategoryTheory.Comma.Over

/-!
# The upper-triangular Borel subgroup scheme of `GL₂`

For a commutative ring `R`, the lower-left coordinate `X₁₀` in the coordinate Hopf algebra of
`GL₂` generates a Hopf ideal. Its quotient represents the closed subgroup scheme of invertible
upper-triangular matrices. On every commutative `R`-algebra `A`, its points are naturally the
existing group `TauCeti.GL2Borel A`.

This is the Borel component of the standard pinning of `GL₂`. It is a worked example for the
pinning interface required by Layer 9 of the ReductiveGroups roadmap: the diagonal split torus
can be placed in this closed subgroup scheme, and the positive simple-root subgroup is proved to
land in it below.

The construction uses the equation

```text
Δ(X₁₀) = X₁₀ ⊗ X₀₀ + X₁₁ ⊗ X₁₀
```

and the fact that the lower-left entry of the inverse of an invertible upper-triangular matrix
vanishes. Thus the defining ideal is stable under comultiplication, counit, and antipode over an
arbitrary commutative base ring.

## Main declarations

* `TauCeti.GeneralLinear.Borel.definingHopfIdeal`: the Hopf ideal `(X₁₀)` in `O(GL₂)`.
* `TauCeti.GeneralLinear.Borel.coordinateHopfAlgebra`: the quotient coordinate Hopf algebra.
* `TauCeti.GeneralLinear.Borel.groupScheme`: the resulting closed subgroup scheme of `GL₂`.
* `TauCeti.GeneralLinear.Borel.inclusion`: its closed immersion into the named `GL₂` group scheme.
* `TauCeti.GeneralLinear.Borel.diagonalTorus`: the diagonal split torus as a morphism into the
  Borel subgroup scheme.
* `TauCeti.GeneralLinear.Borel.diagonalTorus_comp_inclusion`: composing the Borel diagonal torus
  with the inclusion is the ambient diagonal torus of `GL₂`.
* `TauCeti.GeneralLinear.Borel.rootSubgroup`: the positive root subgroup morphism `x₀₁ : 𝔾ₐ → B`.
* `TauCeti.GeneralLinear.Borel.rootSubgroup_comp_inclusion`: composing the Borel root subgroup with
  the inclusion is the ambient `GL₂` root subgroup `x₀₁`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §8.2.
* The quotient coordinate Hopf algebra, closed subgroup scheme packaging, algebra-valued points,
  and functoriality are the rank-two specialization of
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Borel

universe u w

variable (R : Type u) [CommRing R]

/-- The lower-left coordinate of the localized generic `2 × 2` matrix. -/
noncomputable def lowerLeftCoordinate : GeneralLinear.coordinateHopfAlgebra R 2 :=
  GeneralLinear.coordinateHopfAlgebraAlgEquiv R 2
    (GeneralLinear.coordinateRingMap R 2 (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2))))

/-- The lower-left coordinate is the image of the corresponding generic matrix variable. -/
theorem lowerLeftCoordinate_def :
    lowerLeftCoordinate R =
      GeneralLinear.coordinateHopfAlgebraAlgEquiv R 2
        (GeneralLinear.coordinateRingMap R 2
          (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))) :=
  by
    unfold lowerLeftCoordinate
    rfl

/-- The weights `(1, 0)` whose weight parabolic is the standard upper-triangular Borel. -/
abbrev weights : Fin 2 → ℤ :=
  UpperTriangular.weights 2

/-- For the weights `(1, 0)`, the weight-parabolic relation set is the singleton containing the
lower-left coordinate. -/
theorem weightParabolicRelationSet_borelWeights :
    GeneralLinear.weightParabolicRelationSet R weights = {lowerLeftCoordinate R} := by
  ext x
  rw [GeneralLinear.mem_weightParabolicRelationSet_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j
    · simp [weights] at hij
    · simp [weights] at hij
    · exact (lowerLeftCoordinate_def R).symm
    · simp [weights] at hij
  · rintro rfl
    exact ⟨(1 : Fin 2), (0 : Fin 2), by simp [weights], (lowerLeftCoordinate_def R).symm⟩

/-- The Hopf ideal `(X₁₀)` cutting out the upper-triangular matrices inside `GL₂`. -/
noncomputable abbrev definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R 2) :=
  GeneralLinear.weightParabolicDefiningHopfIdeal R weights

/-- The underlying ideal of the Borel Hopf ideal is the principal ideal `(X₁₀)`. -/
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R).toIdeal = Ideal.span {lowerLeftCoordinate R} :=
  by rw [definingHopfIdeal, GeneralLinear.weightParabolicDefiningHopfIdeal_toIdeal,
    weightParabolicRelationSet_borelWeights]

/-- The coordinate Hopf algebra of the upper-triangular Borel subgroup scheme of `GL₂`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  GeneralLinear.weightParabolicCoordinateHopfAlgebra R weights

/-- The quotient coordinate morphism from `O(GL₂)` to the Borel coordinate Hopf algebra. -/
noncomputable abbrev coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R 2 ⟶ coordinateHopfAlgebra R :=
  GeneralLinear.weightParabolicCoordinateMap R weights

/-- The Borel coordinate morphism is the canonical quotient morphism. -/
theorem coordinateMap_def :
    coordinateMap R =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R 2)
        (definingHopfIdeal R) := by
  ext h
  exact GeneralLinear.weightParabolicCoordinateMap_apply R weights h

/-- The Borel coordinate morphism sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R 2) :
    (coordinateMap R).hom h =
      Ideal.Quotient.mkₐ R (definingHopfIdeal R).toIdeal h :=
  GeneralLinear.weightParabolicCoordinateMap_apply R weights h

/-- The lower-left coordinate vanishes in the Borel coordinate Hopf algebra. -/
@[simp↓]
theorem coordinateMap_lowerLeftCoordinate :
    (coordinateMap R).hom (lowerLeftCoordinate R) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (definingHopfIdeal_toIdeal R ▸ Ideal.mem_span_singleton_self _)

/-- The upper-triangular Borel subgroup scheme of `GL₂`. -/
noncomputable abbrev groupScheme :=
  GeneralLinear.weightParabolicGroupScheme R weights

/-- The Borel group scheme is the Hopf spectrum of its quotient coordinate algebra. -/
theorem groupScheme_def :
    groupScheme R =
      CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R 2)
        (definingHopfIdeal R) :=
  by
    unfold groupScheme definingHopfIdeal
    rfl

/-- The closed-subgroup inclusion from the Borel subgroup scheme into the named general-linear
group scheme `GL₂`. -/
noncomputable abbrev inclusion : groupScheme R ⟶ GeneralLinear.groupScheme R 2 :=
  GeneralLinear.weightParabolicInclusion R weights

/-- The Borel inclusion into the named general-linear group scheme is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R).hom.hom.left := by infer_instance

/-- The Borel coordinate Hopf algebra, bundled with its finite-type property. -/
noncomputable abbrev finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra R weights

/-- The finite-type package has the Borel coordinate Hopf algebra as its underlying object. -/
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R).obj = coordinateHopfAlgebra R :=
  by rw [finiteTypeCoordinateHopfAlgebra,
    GeneralLinear.weightParabolicFiniteTypeCoordinateHopfAlgebra_obj]

/-- The structural morphism of the Borel subgroup scheme is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R).X.hom := by infer_instance

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The positive simple-root subgroup `x₀₁` of `GL₂` lands in the Borel subgroup on every
algebra-valued point. -/
theorem rootSubgroupPoints_mem
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    GeneralLinear.rootSubgroupPoints (R := R) (N := 2) (by decide : (0 : Fin 2) ≠ 1) f ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R 2) (definingHopfIdeal R)
        (CommAlgCat.of R A) := by
  apply (UpperTriangular.mem_definingPointsSubgroup_iff R 2 _).mpr
  rw [GeneralLinear.pointsMulEquiv_rootSubgroupPoints]
  exact GL2Borel.mem_iff.mpr (by simp [Matrix.transvection])

/-- The diagonal torus of `GL₂` lands in the Borel subgroup on every algebra-valued point. -/
theorem diagonalTorusPoints_mem
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) →ₐ[R] A)) :
    GeneralLinear.diagonalTorusPoints (R := R) (N := 2) f ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R 2) (definingHopfIdeal R)
        (CommAlgCat.of R A) := by
  apply (UpperTriangular.mem_definingPointsSubgroup_iff R 2 _).mpr
  rw [GeneralLinear.pointsMulEquiv_diagonalTorusPoints]
  exact GL2Borel.mem_iff.mpr (by simp [diagGL_apply])

end Points

section DiagonalTorus

/-- The coordinate morphism of the diagonal torus into the Borel coordinate Hopf algebra. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R)
    (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := 2))
    (by
      rw [definingHopfIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff,
        SetLike.mem_coe, RingHom.mem_ker]
      let id_pt : WithConv
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) →ₐ[R]
            MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ))) :=
        WithConv.toConv (AlgHom.id R _)
      have hmem := diagonalTorusPoints_mem (R := R) id_pt
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem
      have hzero := hmem (lowerLeftCoordinate R)
        (HopfIdeal.mem_toIdeal.mp
          (definingHopfIdeal_toIdeal R ▸ Ideal.mem_span_singleton_self _))
      have heq :
          GeneralLinear.diagonalTorusPoints (R := R) (N := 2) id_pt =
            (CommHopfAlgCat.mapPointsFunctor
              (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := 2))).app
              (CommAlgCat.of R
                (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)))) id_pt := by
        rw [GeneralLinear.mapPointsFunctor_diagonalTorusCoordinateMap_app]
      rw [heq, CommHopfAlgCat.mapPointsFunctor_app_apply] at hzero
      exact hzero)

/-- Precomposing the Borel diagonal-torus coordinate morphism with the quotient coordinate map
yields the ambient general-linear diagonal-torus coordinate morphism. -/
@[simp]
theorem coordinateMap_comp_diagonalTorusCoordinateMap :
    coordinateMap R ≫ diagonalTorusCoordinateMap R =
      GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := 2) := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- **The diagonal split torus of `GL₂` inside its Borel subgroup scheme**. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin 2)) ⟶ groupScheme R :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin 2)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap R).op ≫
    eqToHom (groupScheme_def R).symm

/-- The diagonal torus into the Borel subgroup scheme is relative spectrum applied
contravariantly to its coordinate morphism, transported across the named presentations. -/
theorem diagonalTorus_def :
    diagonalTorus R =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin 2)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap R).op ≫
        eqToHom (groupScheme_def R).symm := by
  unfold diagonalTorus
  rfl

/-- Composing the diagonal torus inside the Borel subgroup scheme with the Borel inclusion into
`GL₂` gives the standard diagonal torus of `GL₂`. -/
@[simp]
theorem diagonalTorus_comp_inclusion :
    diagonalTorus R ≫ inclusion R =
      GeneralLinear.diagonalTorus (R := R) (N := 2) := by
  rw [diagonalTorus_def, inclusion, GeneralLinear.diagonalTorus_def]
  rw [GeneralLinear.weightParabolicInclusion_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  have hmap :
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap R).op ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R 2)
            (definingHopfIdeal R)).op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (GeneralLinear.diagonalTorusCoordinateMap (R := R) (N := 2)).op := by
    rw [← Functor.map_comp, ← op_comp, ← coordinateMap_def R,
      coordinateMap_comp_diagonalTorusCoordinateMap]
  congr 1
  rw [← Category.assoc, hmap]
  rfl

variable (A : Type u) [CommRing A] [Algebra R A]

/-- Under the Borel and general-linear point equivalences, the factored diagonal-torus
coordinate morphism gives the same diagonal matrix as the ambient diagonal-torus morphism. -/
theorem pointsMulEquiv_diagonalTorusCoordinateMap
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin 2) →₀ ℤ)) →ₐ[R] A)) :
    ((UpperTriangular.pointsMulEquiv (R := R) (n := 2) (A := A)
        (WithConv.toConv (f.ofConv.comp (diagonalTorusCoordinateMap R).hom)) : GL2Borel A) :
      GL (Fin 2) A) =
      GeneralLinear.pointsMulEquiv 2
        (GeneralLinear.diagonalTorusPoints (R := R) (N := 2) f) := by
  have hcoe := UpperTriangular.pointsMulEquiv_coe (R := R) (n := 2) (A := A)
    (WithConv.toConv (f.ofConv.comp (diagonalTorusCoordinateMap R).hom))
  rw [← hcoe, GeneralLinear.pointsMulEquiv_apply]
  congr 1
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  have hcomp :
      (coordinateMap R ≫ diagonalTorusCoordinateMap R).hom.toAlgHom =
        (diagonalTorusCoordinateMap R).hom.toAlgHom.comp
          (coordinateMap R).hom.toAlgHom := rfl
  rw [WithConv.ofConv_toConv, AlgHom.comp_assoc, ← coordinateMap_def R, ← hcomp,
    coordinateMap_comp_diagonalTorusCoordinateMap]
  have hmap := GeneralLinear.mapPointsFunctor_diagonalTorusCoordinateMap_app
    (R := R) (N := 2) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hmap
  exact hmap

end DiagonalTorus

section RootSubgroup

/-- The coordinate morphism of the positive root subgroup into the Borel coordinate Hopf algebra. -/
noncomputable def rootSubgroupCoordinateMap :
    coordinateHopfAlgebra R ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R)
    (GeneralLinear.rootSubgroupCoordinateMap (by decide : (0 : Fin 2) ≠ 1))
    (by
      rw [definingHopfIdeal_toIdeal, Ideal.span_le, Set.singleton_subset_iff,
        SetLike.mem_coe, RingHom.mem_ker]
      have hmem := rootSubgroupPoints_mem (R := R)
        (A := AdditiveGroup.coordinateHopfAlgebra R)
        (WithConv.toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R)))
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem
      have h0 := hmem (lowerLeftCoordinate R)
        (HopfIdeal.mem_toIdeal.mp
          (definingHopfIdeal_toIdeal R ▸ Ideal.mem_span_singleton_self _))
      have heq :
          GeneralLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1)
              (WithConv.toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))) =
            (CommHopfAlgCat.mapPointsFunctor
              (GeneralLinear.rootSubgroupCoordinateMap
                (by decide : (0 : Fin 2) ≠ 1))).app
              (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R))
              (WithConv.toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))) := by
        rw [GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app]
      rw [heq, CommHopfAlgCat.mapPointsFunctor_app_apply] at h0
      exact h0)

/-- Precomposing the Borel root-subgroup coordinate morphism with the quotient coordinate map
yields the ambient general-linear root-subgroup coordinate morphism. -/
@[simp]
theorem coordinateMap_comp_rootSubgroupCoordinateMap :
    coordinateMap R ≫ rootSubgroupCoordinateMap R =
      GeneralLinear.rootSubgroupCoordinateMap (by decide : (0 : Fin 2) ≠ 1) := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- **The positive simple-root subgroup of `GL₂` inside the Borel subgroup scheme**: the affine
group-scheme morphism `x₀₁ : 𝔾ₐ → B` whose value on points is `c ↦ x₀₁(c)`. -/
noncomputable def rootSubgroup :
    AdditiveGroup.groupScheme R ⟶ groupScheme R :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (rootSubgroupCoordinateMap R).op ≫
    eqToHom (groupScheme_def R).symm

/-- The root subgroup into the Borel subgroup scheme is relative spectrum applied contravariantly
to its coordinate morphism, transported across the named presentations of `𝔾ₐ` and `B`. -/
theorem rootSubgroup_def :
    rootSubgroup R =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (rootSubgroupCoordinateMap R).op ≫
        eqToHom (groupScheme_def R).symm := by
  unfold rootSubgroup
  rfl

/-- Composing the Borel root-subgroup morphism with the Borel inclusion into `GL₂` gives the
standard general-linear root subgroup `x₀₁`. -/
@[simp]
theorem rootSubgroup_comp_inclusion :
    rootSubgroup R ≫ inclusion R =
      GeneralLinear.rootSubgroup (by decide : (0 : Fin 2) ≠ 1) := by
  rw [rootSubgroup_def, inclusion, GeneralLinear.rootSubgroup_def]
  rw [GeneralLinear.weightParabolicInclusion_def]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  rw [CommHopfAlgCat.quotientSpecι_def]
  have hmap :
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap R).op ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R 2)
            (definingHopfIdeal R)).op =
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (GeneralLinear.rootSubgroupCoordinateMap (by decide : (0 : Fin 2) ≠ 1)).op := by
    rw [← Functor.map_comp, ← op_comp, ← coordinateMap_def R,
      coordinateMap_comp_rootSubgroupCoordinateMap]
  congr 1
  rw [← Category.assoc, hmap]
  rfl

variable (A : Type w) [CommRing A] [Algebra R A]

/-- The positive root subgroup morphism lands in the expected upper-triangular matrix on
algebra-valued points. -/
theorem pointsMulEquiv_rootSubgroupCoordinateMap
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ((UpperTriangular.pointsMulEquiv (R := R) (n := 2) (A := A)
        (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R).hom)) : GL2Borel A) : GL (Fin 2) A) =
      GeneralLinear.pointsMulEquiv 2
        (GeneralLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) f) := by
  have hcoe := UpperTriangular.pointsMulEquiv_coe (R := R) (n := 2) (A := A)
    (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R).hom))
  rw [← hcoe, GeneralLinear.pointsMulEquiv_apply]
  congr 1
  rw [CommHopfAlgCat.quotientPointsHom_apply]
  have hcomp :
      (coordinateMap R ≫ rootSubgroupCoordinateMap R).hom.toAlgHom =
      (rootSubgroupCoordinateMap R).hom.toAlgHom.comp (coordinateMap R).hom.toAlgHom := rfl
  rw [ofConv_toConv, AlgHom.comp_assoc, ← coordinateMap_def R, ← hcomp,
    coordinateMap_comp_rootSubgroupCoordinateMap]
  let id_pt :
      WithConv
        (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] AdditiveGroup.coordinateHopfAlgebra R) :=
    toConv (AlgHom.id R (AdditiveGroup.coordinateHopfAlgebra R))
  have hcomp_alg :
      (GeneralLinear.rootSubgroupCoordinateMap (by decide : (0 : Fin 2) ≠ 1)).hom.toAlgHom =
        (GeneralLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) id_pt).ofConv := by
    have hmap := GeneralLinear.mapPointsFunctor_rootSubgroupCoordinateMap_app (R := R)
      (by decide : (0 : Fin 2) ≠ 1) (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)) id_pt
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply] at hmap
    exact congrArg WithConv.ofConv hmap
  rw [hcomp_alg]
  have hmap_gl :
      GeneralLinear.pointsMulEquiv 2
          (toConv (f.ofConv.comp
            (GeneralLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) id_pt).ofConv)) =
        Matrix.GeneralLinearGroup.map f.ofConv.toRingHom
          (GeneralLinear.pointsMulEquiv 2
            (GeneralLinear.rootSubgroupPoints (by decide : (0 : Fin 2) ≠ 1) id_pt)) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
      Matrix.GeneralLinearGroup.map_apply, GeneralLinear.pointsMulEquiv_apply,
      GeneralLinear.pointToGeneralLinear_apply]
    rfl
  have hid_pt : AlgHom.mapValue f.ofConv id_pt = f := by
    apply WithConv.ext
    exact AlgHom.comp_id f.ofConv
  have hcoe_ring (x : AdditiveGroup.coordinateHopfAlgebra R) :
      f.ofConv.toRingHom x = f.ofConv x := rfl
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) 2).injective
  rw [hmap_gl, GeneralLinear.pointsMulEquiv_rootSubgroupPoints,
    map_transvectionUnit, hcoe_ring,
    ← AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue f.ofConv id_pt,
    hid_pt,
    GeneralLinear.pointsMulEquiv_rootSubgroupPoints]

end RootSubgroup

end TauCeti.GeneralLinear.Borel
