/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Base change of the special linear group

For a morphism of commutative rings `R → K`, scalar extension of the coordinate Hopf algebra
of `SLₙ` is canonically the coordinate Hopf algebra constructed directly over `K`.

The proof starts from the corresponding base-change isomorphism for `GLₙ`. It sends the
base-changed generic determinant to the generic determinant over `K`, and therefore carries the
base change of the determinant-one Hopf ideal onto the determinant-one Hopf ideal over `K`.
The result then follows from the general theorem that a Hopf-ideal quotient commutes with base
change.

## Main declarations

* `TauCeti.SpecialLinear.coordinateHopfAlgebraBaseChangeIso`: base change of the coordinate Hopf
  algebra of `SLₙ`.
* `TauCeti.SpecialLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso`: the finite-type form of
  the same isomorphism.
* `TauCeti.SpecialLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom`: its underlying
  commutative-Hopf-algebra morphism.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).

This is the scalar-extension compatibility needed to assemble the `SLₙ` worked example in
Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.SpecialLinear

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

/-- The general-linear base-change isomorphism sends the scalar extension of the generic
determinant to the generic determinant over the new base. -/
private theorem coordinateHopfAlgebraBaseChangeIso_hom_determinantGroupLike :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (1 ⊗ₜ[R]
          (GeneralLinear.determinantGroupLike R n :
            GeneralLinear.coordinateHopfAlgebra R n)) =
      (GeneralLinear.determinantGroupLike K n :
        GeneralLinear.coordinateHopfAlgebra K n) := by
  have hdet :
      MvPolynomial.map (algebraMap R K)
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) =
        Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K) := by
    rw [RingHom.map_det]
    congr 1
    funext i j
    simp [Matrix.mvPolynomialX]
  rw [GeneralLinear.determinantGroupLike_val,
    GeneralLinear.det_localizedGenericMatrix,
    GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply,
    GeneralLinear.determinantGroupLike_val,
    GeneralLinear.det_localizedGenericMatrix, hdet, one_smul]

/-- The general-linear base-change isomorphism carries the base-changed determinant-one Hopf
ideal onto the determinant-one Hopf ideal over the new base. -/
private theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      definingHopfIdeal K n := by
  have hdet :
      ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom :
          CommHopfAlgCat.baseChange (K := K)
              (GeneralLinear.coordinateHopfAlgebra R n) →+*
            GeneralLinear.coordinateHopfAlgebra K n)
          (1 ⊗ₜ[R]
            (GeneralLinear.determinantGroupLike R n :
              GeneralLinear.coordinateHopfAlgebra R n)) =
        (GeneralLinear.determinantGroupLike K n :
          GeneralLinear.coordinateHopfAlgebra K n) :=
    coordinateHopfAlgebraBaseChangeIso_hom_determinantGroupLike R K n
  apply HopfIdeal.ext
  intro x
  rw [← HopfIdeal.mem_toIdeal, HopfIdeal.map_toIdeal,
    CommHopfAlgCat.baseChangeHopfIdeal_toIdeal, definingHopfIdeal_toIdeal]
  rw [Ideal.map_span, Set.image_singleton]
  rw [Ideal.map_span, Set.image_singleton]
  rw [
    Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_sub, map_sub,
    ← Algebra.TensorProduct.one_def, map_one,
    hdet,
    ← HopfIdeal.mem_toIdeal, definingHopfIdeal_toIdeal]

/-- Pulling the determinant-one Hopf ideal back along the general-linear base-change
isomorphism recovers its base change. -/
private theorem comap_definingHopfIdeal_baseChangeIso :
    (definingHopfIdeal K n).comap
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom).2 =
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n) := by
  let e := GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n
  have he := ConcreteCategory.bijective_of_isIso e.hom
  rw [← map_baseChangeHopfIdeal_definingHopfIdeal R K n,
    HopfIdeal.comap_map_of_surjective,
    (HopfIdeal.kerOfSurjective_eq_bot_iff e.hom.hom he.2).2 he.1, sup_bot_eq]

/-- Quotient maps commute with transporting their defining ideal along an equality. -/
private theorem mkQuotient_comp_eqToIso
    {I J : HopfIdeal K (CommHopfAlgCat.baseChange (K := K)
      (GeneralLinear.coordinateHopfAlgebra R n))} (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := K) (GeneralLinear.coordinateHopfAlgebra R n)) I ≫
        (eqToIso (congrArg (CommHopfAlgCat.quotient
          (CommHopfAlgCat.baseChange (K := K) (GeneralLinear.coordinateHopfAlgebra R n)))
          hIJ)).hom =
      CommHopfAlgCat.mkQuotient
        (CommHopfAlgCat.baseChange (K := K) (GeneralLinear.coordinateHopfAlgebra R n)) J := by
  subst J
  simp

/-- Base change of the special-linear coordinate Hopf algebra is canonically the
special-linear coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  (CommHopfAlgCat.quotientBaseChangeIso (K := K) (definingHopfIdeal R n)).symm ≪≫
    eqToIso (congrArg
      (CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := K) (GeneralLinear.coordinateHopfAlgebra R n)))
      (comap_definingHopfIdeal_baseChangeIso R K n).symm) ≪≫
    CommHopfAlgCat.quotientIsoOfIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n) (definingHopfIdeal K n)

/-- The special-linear base-change isomorphism is compatible with the quotient coordinate
morphisms from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n := by
  let e := GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n
  let h := comap_definingHopfIdeal_baseChangeIso R K n
  have hbase :
      CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) ≫
          (CommHopfAlgCat.quotientBaseChangeIso
            (K := K) (definingHopfIdeal R n)).symm.hom =
        CommHopfAlgCat.mkQuotient
          (CommHopfAlgCat.baseChange (K := K)
            (GeneralLinear.coordinateHopfAlgebra R n))
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R n)) := by
    rw [← cancel_mono (CommHopfAlgCat.quotientBaseChangeIso
      (K := K) (definingHopfIdeal R n)).hom]
    simp
  rw [coordinateHopfAlgebraBaseChangeIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc, hbase, ← Category.assoc,
    mkQuotient_comp_eqToIso R K n h.symm]
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom e (definingHopfIdeal K n)

/-- The finite-type coordinate Hopf algebra of `SLₙ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R n) ≅
      finiteTypeCoordinateHopfAlgebra K n :=
  ObjectProperty.isoMk _ <|
    eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
      (finiteTypeCoordinateHopfAlgebra_obj R n)) ≪≫
    coordinateHopfAlgebraBaseChangeIso R K n ≪≫
    eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n).symm

/-- The underlying commutative-Hopf-algebra morphism of the finite-type base-change isomorphism
is the coordinate-Hopf-algebra base-change isomorphism, with the object equalities made explicit.
-/
@[simp]
theorem finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom :
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
          (finiteTypeCoordinateHopfAlgebra_obj R n)) ≪≫
        coordinateHopfAlgebraBaseChangeIso R K n ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n).symm).hom := by
  simp only [finiteTypeCoordinateHopfAlgebraBaseChangeIso,
    ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom]

end TauCeti.SpecialLinear
