/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.SmoothConnected
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat

/-!
# The upper-triangular Borel subgroup scheme of `GL₂`

For a commutative ring `R`, the lower-left coordinate `X₁₀` in the coordinate Hopf algebra of
`GL₂` generates a Hopf ideal. Its quotient represents the closed subgroup scheme of invertible
upper-triangular matrices. On every commutative `R`-algebra `A`, its points are naturally the
existing group `TauCeti.GL2Borel A`.

This is the rank-two specialization of the standard upper-triangular subgroup. The general-rank
`UpperTriangular` API places both the diagonal split torus and every positive root subgroup in
this closed subgroup scheme.

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
* `TauCeti.GeneralLinear.Borel.isBorel_definingHopfIdeal`: the upper-triangular subgroup is a
  Borel subgroup over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §8.2.
* The quotient coordinate Hopf algebra, closed subgroup scheme packaging, algebra-valued points,
  and functoriality are the rank-two specialization of
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic`.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear.Borel

universe u

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

/-- The general-linear base-change isomorphism carries the scalar extension of the
upper-triangular defining ideal to the upper-triangular defining ideal over the new field. -/
private theorem map_baseChangeHopfIdeal_definingHopfIdeal
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 2).hom.hom =
      definingHopfIdeal K := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal k) (definingHopfIdeal K)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 2)
    (definingHopfIdeal_toIdeal k) (definingHopfIdeal_toIdeal K) ?_
  simp only [Set.image_singleton]
  congr 1
  rw [lowerLeftCoordinate_def, lowerLeftCoordinate_def]
  simpa using GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, u}
    k K 2 1 (MvPolynomial.X ((1 : Fin 2), (0 : Fin 2)))

section Field

variable {k : Type u} [Field k]

/-- The smooth, geometrically connected, geometrically solvable maximality condition over one
field. This local predicate is used to transport the geometric Borel condition across the
canonical base-change isomorphism for `GL₂`. -/
private def isBorelOverField (F : Type u) [Field F]
    (H : FiniteTypeCommHopfAlgCat.{u, u} F) (I : HopfIdeal F H.obj) : Prop :=
  Minimal (fun J : HopfIdeal F H.obj ↦
    smoothCommHopfAlgProperty F (FiniteTypeCommHopfAlgCat.quotient H J).obj ∧
      geometricallyConnectedCommHopfAlgProperty F
        (FiniteTypeCommHopfAlgCat.quotient H J).obj ∧
      geometricallySolvablePointsCommHopfAlgProperty F
        (FiniteTypeCommHopfAlgCat.quotient H J).obj) I

private theorem isBorelOverField_iff (F : Type u) [Field F]
    (H : FiniteTypeCommHopfAlgCat.{u, u} F) (I : HopfIdeal F H.obj) :
    isBorelOverField F H I ↔
      smoothCommHopfAlgProperty F (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
        geometricallyConnectedCommHopfAlgProperty F
          (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
        geometricallySolvablePointsCommHopfAlgProperty F
          (FiniteTypeCommHopfAlgCat.quotient H I).obj ∧
        ∀ J : HopfIdeal F H.obj,
          smoothCommHopfAlgProperty F (FiniteTypeCommHopfAlgCat.quotient H J).obj →
            geometricallyConnectedCommHopfAlgProperty F
              (FiniteTypeCommHopfAlgCat.quotient H J).obj →
            geometricallySolvablePointsCommHopfAlgProperty F
              (FiniteTypeCommHopfAlgCat.quotient H J).obj →
            J ≤ I → I ≤ J := by
  constructor
  · rintro ⟨⟨hsmooth, hconnected, hsolvable⟩, hmax⟩
    exact ⟨hsmooth, hconnected, hsolvable,
      fun J hJsmooth hJconnected hJsolvable hJI ↦
        hmax ⟨hJsmooth, hJconnected, hJsolvable⟩ hJI⟩
  · rintro ⟨hsmooth, hconnected, hsolvable, hmax⟩
    exact ⟨⟨hsmooth, hconnected, hsolvable⟩,
      fun J hJ hJI ↦ hmax J hJ.1 hJ.2.1 hJ.2.2 hJI⟩

/-- Over a field, the upper-triangular subgroup of `GL₂` is maximal among smooth geometrically
connected solvable closed subgroups. -/
private theorem isBorelOverField_definingHopfIdeal :
    isBorelOverField k
      ⟨GeneralLinear.coordinateHopfAlgebra k 2,
        (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
      (definingHopfIdeal k) := by
  rw [isBorelOverField_iff]
  refine ⟨UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra 2 k,
    UpperTriangular.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra 2 k,
    UpperTriangular.geometricallySolvablePointsCommHopfAlgProperty_coordinateHopfAlgebra k 2,
    ?_⟩
  intro I hIsmooth _ hIsolvable hIB
  let H := GeneralLinear.coordinateHopfAlgebra k 2
  let K := AlgebraicClosure k
  let P := GeneralLinear.hopfIdealPointsSubgroup 2 I K
  have hBP : GL2Borel K ≤ P := by
    -- `GL2Borel` abbreviates this upper-triangular subgroup; no propositional equality lemma is
    -- retained solely to restate that definitional equality.
    change upperTriangularGroup (Fin 2) K ≤ P
    rw [← UpperTriangular.hopfIdealPointsSubgroup_eq k 2]
    exact GeneralLinear.hopfIdealPointsSubgroup_le_of_le 2 hIB K
  let e := GeneralLinear.hopfIdealPointsSubgroupMulEquiv 2 I (CommAlgCat.of k K)
  rw [geometricallySolvablePointsCommHopfAlgProperty_iff] at hIsolvable
  let _ : Group.IsSolvable
      (HopfAlgebra.points (R := k) (H := CommHopfAlgCat.quotient H I)
        (CommAlgCat.of k K)) := hIsolvable
  let _ : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hPB : P ≤ GL2Borel K := GL2Borel.le_of_isSolvable K P hBP
  let _ : IsReduced (CommHopfAlgCat.quotient H I) :=
    ((smoothCommHopfAlgProperty_iff_geometricallyReduced k
      (CommHopfAlgCat.quotient H I)).mp hIsmooth).isReduced
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := K)
  intro q hq
  have hqP : GeneralLinear.pointsMulEquiv 2 q ∈ P :=
    GeneralLinear.pointsMulEquiv_mem_hopfIdealPointsSubgroup 2 I K q hq
  have hqB : GeneralLinear.pointsMulEquiv 2 q ∈
      GeneralLinear.hopfIdealPointsSubgroup 2 (definingHopfIdeal k) K := by
    rw [UpperTriangular.hopfIdealPointsSubgroup_eq k 2]
    exact hPB hqP
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hqB
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [MulEquiv.symm_apply_apply] using hqB

/-- **The upper-triangular subgroup scheme of `GL₂` is a Borel subgroup over every field.**
Its base change to an algebraic closure is smooth, connected, solvable, and maximal among closed
subgroups with those properties. -/
theorem isBorel_definingHopfIdeal :
    HopfIdeal.IsBorel k (GeneralLinear.coordinateHopfAlgebra k 2) (definingHopfIdeal k) := by
  simp only [HopfIdeal.isBorel_iff]
  let K := AlgebraicClosure k
  let H : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨GeneralLinear.coordinateHopfAlgebra k 2,
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  let L : FiniteTypeCommHopfAlgCat.{u, u} K :=
    ⟨GeneralLinear.coordinateHopfAlgebra K 2,
      (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
  let e : H' ≅ L := ObjectProperty.isoMk _
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K 2)
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal k)
  rw [← isBorelOverField_iff K H' I']
  have htarget : isBorelOverField K L (definingHopfIdeal K) := by
    simpa only [L] using (isBorelOverField_definingHopfIdeal (k := K))
  have hpull : isBorelOverField K H'
      ((definingHopfIdeal K).comapOfSurjective
        (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) :=
    FiniteTypeCommHopfAlgCat.minimal_quotientProperty_comapOfIso
      (H := H') (K := L)
      ((smoothCommHopfAlgProperty K ⊓
        (geometricallyConnectedCommHopfAlgProperty K ⊓
          geometricallySolvablePointsCommHopfAlgProperty K)).inverseImage
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} K)
          (_root_.CommHopfAlgCat.{u} K))) (definingHopfIdeal K) htarget e
  let f := FiniteTypeCommHopfAlgCat.toBialgHom e.hom
  have hf : Function.Bijective f := ConcreteCategory.bijective_of_isIso e.hom
  have hmap : I'.map f = definingHopfIdeal K := by
    exact map_baseChangeHopfIdeal_definingHopfIdeal k K
  have hcomap :
      (definingHopfIdeal K).comapOfSurjective f hf.2 = I' := by
    rw [← hmap]
    exact HopfIdeal.comapOfSurjective_map_of_bijective I' f hf
  rwa [hcomap] at hpull

end Field

end TauCeti.GeneralLinear.Borel
