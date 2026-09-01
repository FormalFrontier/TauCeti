/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic

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

namespace TauCeti

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

namespace SpecialLinear

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
    GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_determinantGroupLike R K n
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (definingHopfIdeal_toIdeal R n) (definingHopfIdeal_toIdeal K n) ?_
  simp only [Set.image_singleton, TensorProduct.tmul_sub, map_sub,
    ← Algebra.TensorProduct.one_def, map_one]
  congr 1
  exact congrArg (fun x => x - 1) hdet

/-- Base change of the special-linear coordinate Hopf algebra is canonically the
special-linear coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K n)

/-- The special-linear base-change isomorphism is compatible with the quotient coordinate
morphisms from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n := by
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R n) (definingHopfIdeal K n)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n)
    (map_baseChangeHopfIdeal_definingHopfIdeal R K n)

/-- The finite-type coordinate Hopf algebra of `SLₙ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R n) ≅
      finiteTypeCoordinateHopfAlgebra K n :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (finiteTypeCoordinateHopfAlgebra_obj R n) (finiteTypeCoordinateHopfAlgebra_obj K n)
    (coordinateHopfAlgebraBaseChangeIso R K n)

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
  exact FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso_hom
    (finiteTypeCoordinateHopfAlgebra_obj R n) (finiteTypeCoordinateHopfAlgebra_obj K n)
    (coordinateHopfAlgebraBaseChangeIso R K n)

end SpecialLinear

end TauCeti
