/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

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
  compatibility with the quotient coordinate morphisms from `O(GL (m + m))`.
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

/-- The `R`-algebra structure obtained by restricting the coordinate algebra over `K`. -/
noncomputable local instance : Algebra R (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
  Algebra.compHom _ (algebraMap R K)

/-- The coordinate algebra over `K` is a scalar tower over `R → K`. -/
local instance : IsScalarTower R K (GeneralLinear.coordinateHopfAlgebra K (m + m)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The restriction of the general-linear base-change isomorphism to the original coordinate
Hopf algebra. -/
private noncomputable def baseChangeAlgHom :
    GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R]
      GeneralLinear.coordinateHopfAlgebra K (m + m) :=
  ((GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K
    (m + m)).hom.hom.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight :
      GeneralLinear.coordinateHopfAlgebra R (m + m) →ₐ[R]
        K ⊗[R] GeneralLinear.coordinateHopfAlgebra R (m + m))

/-- Applying the restricted base-change map is applying the ambient isomorphism to a scalar pure
tensor. -/
private theorem baseChangeAlgHom_apply (x : GeneralLinear.coordinateHopfAlgebra R (m + m)) :
    baseChangeAlgHom R K m x =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
        (1 ⊗ₜ[R] x) := by
  simp only [baseChangeAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.coe_restrictScalars', BialgHom.coe_toAlgHom]

/-- The general-linear base-change isomorphism carries each scalar-extended symplectic relation
to the corresponding relation over the new base. -/
private theorem coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix (i j : Fin (m + m)) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
        (1 ⊗ₜ[R] relationMatrix R m i j) =
      relationMatrix K m i j := by
  rw [← baseChangeAlgHom_apply R K m]
  have hgeneric : (genericMatrix R m).map (baseChangeAlgHom R K m) = genericMatrix K m := by
    ext i j
    rw [Matrix.map_apply, genericMatrix_apply, genericMatrix_apply]
    have h := congrFun (congrFun
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_genericMatrix R K (m + m)) i) j
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply,
      GeneralLinear.genericMatrix_apply] at h
    simpa only [baseChangeAlgHom] using h
  have hmatrix := relationMatrix_map R m (baseChangeAlgHom R K m)
  rw [hgeneric] at hmatrix
  rw [relationMatrix_def K m, JFin_map]
  exact congrFun (congrFun hmatrix i) j

/-- The general-linear base-change isomorphism carries the base-changed symplectic defining Hopf
ideal onto the symplectic defining Hopf ideal over the new base. -/
private theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R m)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom =
      definingHopfIdeal K m := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m))
    (definingHopfIdeal_toIdeal R m) (definingHopfIdeal_toIdeal K m) ?_
  have hrel (i j : Fin (m + m)) :
      (fun x : GeneralLinear.coordinateHopfAlgebra R (m + m) =>
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom.hom
          (1 ⊗ₜ[R] x)) (relationMatrix R m i j) = relationMatrix K m i j :=
    coordinateHopfAlgebraBaseChangeIso_hom_relationMatrix R K m i j
  ext x
  constructor
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff R m).mp hy
    exact (hrel i j).symm ▸ relationMatrix_mem_relationSet K m i j
  · intro hx
    obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff K m).mp hx
    exact ⟨relationMatrix R m i j, relationMatrix_mem_relationSet R m i j,
      hrel i j⟩

/-- Base change of the symplectic coordinate Hopf algebra is canonically the symplectic
coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R m) ≅
      coordinateHopfAlgebra K m :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m))
    (map_baseChangeHopfIdeal_definingHopfIdeal R K m)

/-- The symplectic base-change isomorphism is compatible with the quotient coordinate morphisms
from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m) ≫
        (coordinateHopfAlgebraBaseChangeIso R K m).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).hom ≫
        coordinateMap K m := by
  rw [coordinateMap_def, coordinateMap_def]
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R m) (definingHopfIdeal K m)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m))
    (map_baseChangeHopfIdeal_definingHopfIdeal R K m)

/-- The finite-type coordinate Hopf algebra of `Sp₂ₘ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R m) ≅
      finiteTypeCoordinateHopfAlgebra K m :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (finiteTypeCoordinateHopfAlgebra_obj R m) (finiteTypeCoordinateHopfAlgebra_obj K m)
    (coordinateHopfAlgebraBaseChangeIso R K m)

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
  exact FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso_hom
    (finiteTypeCoordinateHopfAlgebra_obj R m) (finiteTypeCoordinateHopfAlgebra_obj K m)
    (coordinateHopfAlgebraBaseChangeIso R K m)

end TauCeti.Symplectic
