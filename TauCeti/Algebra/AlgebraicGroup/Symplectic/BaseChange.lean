/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Base change of the symplectic group

For a morphism of commutative rings `R → K`, scalar extension of the coordinate Hopf algebra
of `Sp₂ₘ` is canonically the coordinate Hopf algebra constructed directly over `K`.

The proof transports the entries of the matrix relation `X Jₘ Xᵀ - Jₘ` across the existing
base-change isomorphism for `GL (m + m)`. It therefore identifies the base change of the
symplectic defining Hopf ideal with the symplectic defining ideal over `K`, after which the
general base-change theorem for Hopf-ideal quotients gives the result.

## Main declarations

* `TauCeti.Symplectic.coordinateHopfAlgebraBaseChangeIso`: base change of the coordinate Hopf
  algebra of `Sp₂ₘ`.
* `TauCeti.Symplectic.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom`:
  compatibility with the closed immersion into `GL (m + m)`.
* `TauCeti.Symplectic.finiteTypeCoordinateHopfAlgebraBaseChangeIso`: the finite-type form of the
  same isomorphism.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).

The quotient-transport construction follows
`TauCeti.SpecialLinear.coordinateHopfAlgebraBaseChangeIso`, replacing its determinant relation
by the symplectic matrix relations.

This is the scalar-extension compatibility needed before the `Sp₂ₘ` worked example can be
proved reductive in Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Matrix
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (m : ℕ)

/-- The general-linear base-change isomorphism sends the scalar extension of the generic matrix
to the generic matrix over the new base. -/
private theorem coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix :
    let _ : Algebra R (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
      Algebra.compHom _ (algebraMap R K)
    let _ : IsScalarTower R K (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    (genericMatrix R m).map
        (((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K
          (m + m)).hom.hom.toAlgHom.restrictScalars R).comp
          (Algebra.TensorProduct.includeRight :
            GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R]
              K ⊗[R] GeneralLinear.coordinateHopfAlgebra R (m + m))) =
      genericMatrix K m := by
  let _ : Algebra R (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
    Algebra.compHom _ (algebraMap R K)
  let _ : IsScalarTower R K (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  ext i j
  rw [Matrix.map_apply]
  rw [genericMatrix_apply]
  rw [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]
  rw [genericMatrix_apply]
  have h := GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply.{u, v}
    R K (m + m) 1 (MvPolynomial.X (i, j))
  -- The categorical concrete map and the stored bialgebra homomorphism are the same map, but the
  -- object-property wrapper prevents the elaborator from seeing that equality definitionally.
  change (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom.toAlgHom
      (1 ⊗ₜ[R] GeneralLinear.coordinateHopfAlgebraAlgEquiv R (m + m)
        (GeneralLinear.coordinateRingMap R (m + m) (MvPolynomial.X (i, j)))) = _ at h
  simpa only [AlgHom.coe_restrictScalars', one_smul, MvPolynomial.map_X] using h

/-- The general-linear base-change isomorphism carries each scalar-extended symplectic relation
to the corresponding relation over the new base. -/
private theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix (i j : Fin (m + m)) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
        (1 ⊗ₜ[R] relationMatrix R m i j) =
      relationMatrix K m i j := by
  let _ : Algebra R (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
    Algebra.compHom _ (algebraMap R K)
  let _ : IsScalarTower R K (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let φ :=
    ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K
      (m + m)).hom.hom.toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight :
        GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R]
          K ⊗[R] GeneralLinear.coordinateHopfAlgebra R (m + m))
  have hgeneric : (genericMatrix R m).map φ = genericMatrix K m :=
    coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix R K m
  -- `φ` is the restriction to the original coordinate algebra of the map on its scalar
  -- extension; exposing that application lets the public relation-matrix mapping theorem apply.
  change φ (relationMatrix R m i j) = relationMatrix K m i j
  have hmatrix := relationMatrix_map R m φ
  rw [hgeneric, JFin_map] at hmatrix
  rw [relationMatrix_def K m, JFin_map]
  exact congrFun (congrFun hmatrix i) j

/-- The general-linear base-change isomorphism carries the base-changed symplectic defining Hopf
ideal onto the symplectic defining Hopf ideal over the new base. -/
private theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom =
      definingHopfIdeal K m := by
  apply HopfIdeal.ext
  intro x
  change x ∈
      ((CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom).toIdeal ↔
    x ∈ (definingHopfIdeal K m).toIdeal
  rw [HopfIdeal.map_toIdeal,
    CommHopfAlgCat.baseChangeHopfIdeal_toIdeal, definingHopfIdeal_toIdeal,
    definingHopfIdeal_toIdeal, Ideal.map_span, Ideal.map_span]
  constructor
  · intro hx
    have hle : Ideal.span
        ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K
            (m + m)).hom.hom.toAlgHom.toRingHom ''
          Algebra.TensorProduct.includeRight '' relationSet R m) ≤
        Ideal.span (relationSet K m) := by
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff R m).mp hz
      have hmem := Ideal.subset_span (relationMatrix_mem_relationSet K m i j)
      rw [← coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix R K m i j] at hmem
      simpa only [Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hmem
    exact hle hx
  · intro hx
    have hle : Ideal.span (relationSet K m) ≤
        Ideal.span
          ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K
              (m + m)).hom.hom.toAlgHom.toRingHom ''
            Algebra.TensorProduct.includeRight '' relationSet R m) := by
      rw [Ideal.span_le]
      intro z hz
      obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff K m).mp hz
      exact Ideal.subset_span ⟨1 ⊗ₜ[R] relationMatrix R m i j,
        ⟨relationMatrix R m i j, relationMatrix_mem_relationSet R m i j, rfl⟩,
        by simpa only [Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using
          coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix R K m i j⟩
    exact hle hx

/-- Pulling the symplectic defining Hopf ideal back along the general-linear base-change
isomorphism recovers its base change. -/
private theorem comap_definingHopfIdeal_baseChangeIso :
    (definingHopfIdeal K m).comap
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom).2 =
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m) := by
  let e := GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)
  have he := ConcreteCategory.bijective_of_isIso e.hom
  rw [← map_baseChangeHopfIdeal_definingHopfIdeal R K m,
    HopfIdeal.comap_map_of_surjective,
    (HopfIdeal.kerOfSurjective_eq_bot_iff e.hom.hom he.2).2 he.1, sup_bot_eq]

/-- Quotient maps commute with transporting their defining ideal along an equality. -/
private theorem mkQuotient_comp_eqToIso
    {I J : HopfIdeal K (CommHopfAlgCat.baseChange (K := K)
      (GeneralLinear.coordinateHopfAlgebra R (m + m)))} (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := K)
            (GeneralLinear.coordinateHopfAlgebra R (m + m))) I ≫
        (eqToIso (congrArg (CommHopfAlgCat.quotient
          (CommHopfAlgCat.baseChange (K := K)
            (GeneralLinear.coordinateHopfAlgebra R (m + m)))) hIJ)).hom =
      CommHopfAlgCat.mkQuotient
        (CommHopfAlgCat.baseChange (K := K)
          (GeneralLinear.coordinateHopfAlgebra R (m + m))) J := by
  subst J
  simp

/-- Base change of the symplectic coordinate Hopf algebra is canonically the symplectic
coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R m) ≅
      coordinateHopfAlgebra K m :=
  (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingHopfIdeal R m)).symm ≪≫
    eqToIso (congrArg
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := K)
          (GeneralLinear.coordinateHopfAlgebra R (m + m))))
      (comap_definingHopfIdeal_baseChangeIso R K m).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m))
      (definingHopfIdeal K m)

/-- The symplectic base-change isomorphism is compatible with the quotient coordinate morphisms
from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m) ≫
        (coordinateHopfAlgebraBaseChangeIso R K m).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom ≫
        coordinateMap K m := by
  rw [coordinateMap_def, coordinateMap_def]
  let e := GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)
  let h := comap_definingHopfIdeal_baseChangeIso R K m
  have hbase :
      CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra R (m + m)) (definingHopfIdeal R m)) ≫
          (CommHopfAlgCat.quotientBaseChangeIso
            (K := K) (definingHopfIdeal R m)).symm.hom =
        CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := K)
            (GeneralLinear.coordinateHopfAlgebra R (m + m)))
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)) := by
    rw [← cancel_mono (CommHopfAlgCat.quotientBaseChangeIso
      (K := K) (definingHopfIdeal R m)).hom]
    simp
  rw [coordinateHopfAlgebraBaseChangeIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc, hbase, ← Category.assoc,
    mkQuotient_comp_eqToIso R K m h.symm]
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom e (definingHopfIdeal K m)

/-- The finite-type coordinate Hopf algebra of `Sp₂ₘ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R m) ≅
      finiteTypeCoordinateHopfAlgebra K m :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
      (finiteTypeCoordinateHopfAlgebra_obj R m)) ≪≫
    coordinateHopfAlgebraBaseChangeIso R K m ≪≫
    eqToIso (finiteTypeCoordinateHopfAlgebra_obj K m).symm

/-- The underlying commutative-Hopf-algebra morphism of the finite-type base-change isomorphism
is the coordinate-Hopf-algebra base-change isomorphism, with the object equalities made explicit.
-/
@[simp]
theorem finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom :
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso R K m).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
          (finiteTypeCoordinateHopfAlgebra_obj R m)) ≪≫
        coordinateHopfAlgebraBaseChangeIso R K m ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K m).symm).hom := by
  simp only [finiteTypeCoordinateHopfAlgebraBaseChangeIso,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom]

end TauCeti.Symplectic
