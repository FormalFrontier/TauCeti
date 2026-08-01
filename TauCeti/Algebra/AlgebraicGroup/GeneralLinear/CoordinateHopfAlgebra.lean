/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.CoordinateBialgebra

/-!
# The general linear coordinate Hopf algebra

For a commutative ring `R`, this file constructs the coordinate Hopf algebra of `GLₙ` as

`R[Xᵢⱼ][det(X)⁻¹]`.

The matrix-monoid comultiplication and counit extend across the localization because the generic
determinant is group-like. The antipode evaluates the polynomial generators at the nonsingular
inverse of the localized generic matrix. The bialgebra and Hopf laws are proved by localization
extensionality and polynomial-generator calculations; in particular, the construction never
assumes that the localization map is injective.

The raw structure dictionaries are named values rather than global instances. The bundled
`coordinateHopfAlgebra` is the coherence boundary for the chosen matrix-coordinate structure,
and `finiteTypeCoordinateHopfAlgebra` records that this localization is of finite type. The
construction includes rank zero and the zero ring, with no nontriviality or positive-rank
hypothesis.

## Main declarations

* `TauCeti.GeneralLinear.CoordinateRing`: the determinant localization.
* `TauCeti.GeneralLinear.comul`, `TauCeti.GeneralLinear.counit`: the localized coalgebra maps.
* `TauCeti.GeneralLinear.antipode`: the inverse-matrix antipode.
* `TauCeti.GeneralLinear.hopfAlgebra`: the selected Hopf-algebra dictionary.
* `TauCeti.GeneralLinear.coordinateHopfAlgebra`: the bundled commutative Hopf algebra.
* `TauCeti.GeneralLinear.finiteTypeCoordinateHopfAlgebra`: its finite-type package.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags
  [022W](https://stacks.math.columbia.edu/tag/022W),
  [022X](https://stacks.math.columbia.edu/tag/022X), and
  [00CM](https://stacks.math.columbia.edu/tag/00CM).
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace GeneralLinear

open Algebra.TensorProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The coordinate ring of `GLₙ`, obtained by inverting the determinant of Mathlib's generic
matrix in the matrix-monoid coordinate ring. -/
abbrev CoordinateRing :=
  Localization.Away
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))

/-- The canonical algebra map from the matrix-monoid coordinate ring into its determinant
localization. -/
noncomputable def coordinateRingMap :
    MatrixMonoid.CoordinateRing R n →ₐ[R] CoordinateRing R n :=
  IsScalarTower.toAlgHom R (MatrixMonoid.CoordinateRing R n) (CoordinateRing R n)

/-- Mathlib's generic matrix after applying the canonical map into the determinant localization. -/
noncomputable def localizedGenericMatrix :
    Matrix (Fin n) (Fin n) (CoordinateRing R n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).map (coordinateRingMap R n)

/-- An entry of the localized generic matrix is the image of the corresponding polynomial
generator. -/
@[simp]
theorem localizedGenericMatrix_apply (i j : Fin n) :
    localizedGenericMatrix R n i j =
      coordinateRingMap R n (MvPolynomial.X (i, j)) := by
  simp [localizedGenericMatrix, Matrix.mvPolynomialX]

private noncomputable def comulBase :
    MatrixMonoid.CoordinateRing R n →ₐ[R]
      CoordinateRing R n ⊗[R] CoordinateRing R n :=
  (Algebra.TensorProduct.map (coordinateRingMap R n) (coordinateRingMap R n)).comp
    (MatrixMonoid.comul R n)

/-- The determinant of the localized generic matrix is the image of the generic determinant. -/
@[simp]
theorem det_localizedGenericMatrix :
    Matrix.det (localizedGenericMatrix R n) =
      coordinateRingMap R n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)) := by
  rw [localizedGenericMatrix, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

/-- The determinant of the localized generic matrix is a unit. -/
theorem isUnit_det_localizedGenericMatrix :
    IsUnit (Matrix.det (localizedGenericMatrix R n)) := by
  rw [det_localizedGenericMatrix]
  exact IsLocalization.Away.algebraMap_isUnit
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))

private theorem comulBase_determinant_isUnit :
    IsUnit (comulBase R n
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  rw [comulBase, AlgHom.comp_apply, MatrixMonoid.comul_determinant, map_tmul]
  have h : IsUnit
      (coordinateRingMap R n
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) :=
    IsLocalization.Away.algebraMap_isUnit
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
  have hl : IsUnit
      ((includeLeft : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n)
        (coordinateRingMap R n
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))) :=
    h.map includeLeft
  have hr : IsUnit
      ((includeRight : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n)
        (coordinateRingMap R n
          (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))) :=
    h.map includeRight
  convert hl.mul hr using 1
  all_goals simp

/-- The matrix-multiplication comultiplication extended across the determinant localization. -/
noncomputable def comul :
    CoordinateRing R n →ₐ[R] CoordinateRing R n ⊗[R] CoordinateRing R n :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
    (comulBase_determinant_isUnit R n)

private theorem counitBase_determinant_isUnit :
    IsUnit (MatrixMonoid.counit R n
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  rw [MatrixMonoid.counit_determinant]
  exact isUnit_one

/-- The identity-matrix counit extended across the determinant localization. -/
noncomputable def counit : CoordinateRing R n →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
    (counitBase_determinant_isUnit R n)

/-- The localized comultiplication restricts to the matrix-monoid comultiplication followed by
the two canonical localization maps. -/
@[simp low]
theorem comul_coordinateRingMap (x : MatrixMonoid.CoordinateRing R n) :
    comul R n (coordinateRingMap R n x) =
      Algebra.TensorProduct.map (coordinateRingMap R n) (coordinateRingMap R n)
        (MatrixMonoid.comul R n x) := by
  simp [comul, coordinateRingMap, comulBase]

/-- The localized counit restricts to the matrix-monoid counit. -/
@[simp low]
theorem counit_coordinateRingMap (x : MatrixMonoid.CoordinateRing R n) :
    counit R n (coordinateRingMap R n x) = MatrixMonoid.counit R n x := by
  simp [counit, coordinateRingMap]

private noncomputable def antipodeBase :
    MatrixMonoid.CoordinateRing R n →ₐ[R] CoordinateRing R n :=
  MvPolynomial.aeval fun ij : Fin n × Fin n => ((localizedGenericMatrix R n)⁻¹) ij.1 ij.2

private theorem antipodeBase_determinant_isUnit :
    IsUnit (antipodeBase R n
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  rw [antipodeBase, AlgHom.map_det]
  rw [Matrix.mvPolynomialX_mapMatrix_aeval]
  exact Matrix.isUnit_nonsing_inv_det _ (isUnit_det_localizedGenericMatrix R n)

/-- The antipode of the general linear coordinate ring. It evaluates the polynomial generators
at the nonsingular inverse of the localized generic matrix and extends across the localization. -/
noncomputable def antipode : CoordinateRing R n →ₐ[R] CoordinateRing R n :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
    (antipodeBase_determinant_isUnit R n)

/-- On the polynomial subalgebra, the antipode is evaluation at the nonsingular inverse of the
localized generic matrix. -/
@[simp low]
theorem antipode_coordinateRingMap (x : MatrixMonoid.CoordinateRing R n) :
    antipode R n (coordinateRingMap R n x) =
      MvPolynomial.aeval
        (fun ij : Fin n × Fin n => ((localizedGenericMatrix R n)⁻¹) ij.1 ij.2) x := by
  simp [antipode, coordinateRingMap, antipodeBase]

private theorem algHom_ext_away {T : Type*} [Semiring T] [Algebra R T]
    {f g : CoordinateRing R n →ₐ[R] T}
    (h : f.comp (coordinateRingMap R n) = g.comp (coordinateRingMap R n)) : f = g := by
  apply AlgHom.ext
  have h' : f.toRingHom = g.toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers
        (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, coordinateRingMap,
      IsScalarTower.coe_toAlgHom] using congrArg AlgHom.toRingHom h
  exact RingHom.congr_fun h'

/-- Comultiplication sends a localized generic entry to the matrix-multiplication sum. -/
@[simp]
theorem comul_X (i j : Fin n) :
    comul R n (coordinateRingMap R n (MvPolynomial.X (i, j))) =
      ∑ k : Fin n,
        coordinateRingMap R n (MvPolynomial.X (i, k)) ⊗ₜ[R]
          coordinateRingMap R n (MvPolynomial.X (k, j)) := by
  rw [comul_coordinateRingMap]
  simp [MatrixMonoid.comul_X]

/-- The counit sends a localized generic entry to the corresponding identity-matrix entry. -/
@[simp]
theorem counit_X (i j : Fin n) :
    counit R n (coordinateRingMap R n (MvPolynomial.X (i, j))) =
      if i = j then 1 else 0 := by
  rw [counit_coordinateRingMap]
  exact MatrixMonoid.counit_X R n i j

/-- The antipode sends a localized generic entry to the corresponding entry of the nonsingular
inverse. -/
@[simp]
theorem antipode_X (i j : Fin n) :
    antipode R n (coordinateRingMap R n (MvPolynomial.X (i, j))) =
      ((localizedGenericMatrix R n)⁻¹) i j := by
  rw [antipode_coordinateRingMap]
  simp

/-- Applying comultiplication entrywise to the localized generic matrix gives the product of its
left- and right-tensor copies, in the order representing ordinary matrix multiplication. -/
@[simp]
theorem map_comul_localizedGenericMatrix :
    (localizedGenericMatrix R n).map (comul R n) =
      (localizedGenericMatrix R n).map
          (includeLeft : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) *
        (localizedGenericMatrix R n).map
          (includeRight : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) := by
  ext i j
  simp [Matrix.mul_apply]

/-- Applying the counit entrywise to the localized generic matrix gives the identity matrix. -/
@[simp]
theorem map_counit_localizedGenericMatrix :
    (localizedGenericMatrix R n).map (counit R n) = 1 := by
  ext i j
  simp [Matrix.one_apply]

/-- Applying the antipode entrywise to the localized generic matrix gives its nonsingular
inverse. -/
@[simp]
theorem map_antipode_localizedGenericMatrix :
    (localizedGenericMatrix R n).map (antipode R n) =
      (localizedGenericMatrix R n)⁻¹ := by
  ext i j
  simp

/-- The determinant of the localized generic matrix remains group-like for the localized
comultiplication. -/
theorem comul_det_localizedGenericMatrix :
    comul R n (Matrix.det (localizedGenericMatrix R n)) =
      Matrix.det (localizedGenericMatrix R n) ⊗ₜ[R]
        Matrix.det (localizedGenericMatrix R n) := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_comul_localizedGenericMatrix,
    Matrix.det_mul]
  rw [← AlgHom.mapMatrix_apply
      (includeLeft : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n),
    ← AlgHom.mapMatrix_apply
      (includeRight : CoordinateRing R n →ₐ[R]
        CoordinateRing R n ⊗[R] CoordinateRing R n),
    ← AlgHom.map_det, ← AlgHom.map_det]
  simp

/-- The counit sends the determinant of the localized generic matrix to one. -/
theorem counit_det_localizedGenericMatrix :
    counit R n (Matrix.det (localizedGenericMatrix R n)) = 1 := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_counit_localizedGenericMatrix,
    Matrix.det_one]

/-- The antipode sends the localized generic determinant to its ring inverse. -/
theorem antipode_det_localizedGenericMatrix :
    antipode R n (Matrix.det (localizedGenericMatrix R n)) =
      Ring.inverse (Matrix.det (localizedGenericMatrix R n)) := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_antipode_localizedGenericMatrix,
    Matrix.det_nonsing_inv]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (CoordinateRing R n) (CoordinateRing R n) (CoordinateRing R n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R n) (.id R (CoordinateRing R n))).comp
        (comul R n)) =
      (Algebra.TensorProduct.map (.id R (CoordinateRing R n)) (comul R n)).comp
        (comul R n) := by
  apply algHom_ext_away R n
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, AlgHom.id_apply]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  simp only [map_sum]
  rw [Finset.sum_comm]
  rfl

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R n) (.id R (CoordinateRing R n))).comp
        (comul R n) =
      (Algebra.TensorProduct.lid R (CoordinateRing R n)).symm := by
  apply algHom_ext_away R n
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, counit_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [hki.symm]
  · simp

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id R (CoordinateRing R n)) (counit R n)).comp
        (comul R n) =
      (Algebra.TensorProduct.rid R R (CoordinateRing R n)).symm := by
  apply algHom_ext_away R n
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, counit_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- The bialgebra structure on the determinant localization, with matrix-multiplication
comultiplication and identity-matrix counit.

This is intentionally a named value rather than a global instance. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (CoordinateRing R n) :=
  Bialgebra.ofAlgHom (comul R n) (counit R n)
    (comul_coassoc R n) (comul_rTensor_counit R n) (comul_lTensor_counit R n)

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R n) (.id R (CoordinateRing R n))
      fun _ _ ↦ Commute.all _ _).comp (comul R n) =
        (Algebra.ofId R (CoordinateRing R n)).comp (counit R n) := by
  apply algHom_ext_away R n
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  simpa [antipodeBase, Matrix.mul_apply, Matrix.one_apply] using congrFun
    (congrFun (Matrix.nonsing_inv_mul (localizedGenericMatrix R n)
      (isUnit_det_localizedGenericMatrix R n)) i) j

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (CoordinateRing R n)) (antipode R n)
      fun _ _ ↦ Commute.all _ _).comp (comul R n) =
        (Algebra.ofId R (CoordinateRing R n)).comp (counit R n) := by
  apply algHom_ext_away R n
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  simpa [antipodeBase, Matrix.mul_apply, Matrix.one_apply] using congrFun
    (congrFun (Matrix.mul_nonsing_inv (localizedGenericMatrix R n)
      (isUnit_det_localizedGenericMatrix R n)) i) j

/-- The Hopf-algebra structure on the determinant localization whose antipode is inverse-matrix
evaluation.

This is intentionally a named value rather than a global instance. Use `coordinateHopfAlgebra`
as the bundled coherence boundary. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R (CoordinateRing R n) := by
  letI : Bialgebra R (CoordinateRing R n) := bialgebra R n
  exact HopfAlgebra.ofAlgHom (antipode R n)
    (mul_antipode_rTensor_comul R n) (mul_antipode_lTensor_comul R n)

/-- Selecting `hopfAlgebra R n` makes its comultiplication the explicit localized map `comul R n`.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_comul :
    HEq (letI : Module R (CoordinateRing R n) :=
        (hopfAlgebra R n).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R n) := (hopfAlgebra R n).toCoalgebra
      Coalgebra.comul (R := R) (A := CoordinateRing R n)) (comul R n).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R n` makes its counit the explicit localized map `counit R n`.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_counit :
    HEq (letI : Module R (CoordinateRing R n) :=
        (hopfAlgebra R n).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R n) := (hopfAlgebra R n).toCoalgebra
      Coalgebra.counit (R := R) (A := CoordinateRing R n)) (counit R n).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R n` makes its antipode the explicit inverse-matrix map `antipode R n`.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_antipode :
    HEq (letI : Module R (CoordinateRing R n) :=
        (hopfAlgebra R n).toAlgebra.toModule
      letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
      HopfAlgebra.antipode R (A := CoordinateRing R n)) (antipode R n).toLinearMap :=
  heq_of_eq rfl

/-- The determinant localization bundled with the selected general linear Hopf-algebra
structure. -/
noncomputable def coordinateHopfAlgebra : _root_.CommHopfAlgCat R :=
  letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
  _root_.CommHopfAlgCat.of R (CoordinateRing R n)

/-- The canonical algebra equivalence from the determinant localization to the carrier of its
bundled coordinate Hopf algebra. -/
noncomputable def coordinateHopfAlgebraAlgEquiv :
    CoordinateRing R n ≃ₐ[R] coordinateHopfAlgebra R n := by
  letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
  exact AlgEquiv.refl

/-- Mathlib has no `CommHopfAlgCat.of_comul` lemma exposing the comultiplication stored by
`CommHopfAlgCat.of`. This bridge locally crosses the two definitional wrappers:
`coordinateHopfAlgebra` stores `(hopfAlgebra R n).toCoalgebra` on the raw coordinate ring, and
`coordinateHopfAlgebraAlgEquiv` is the identity algebra equivalence on that carrier. After those
reductions, transporting the stored comultiplication is `Algebra.TensorProduct.map_id`. -/
private theorem coordinateHopfAlgebra_comul_transport (x : CoordinateRing R n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          ((hopfAlgebra R n).toCoalgebra.toCoalgebraStruct.comul x) := by
  change (hopfAlgebra R n).toCoalgebra.toCoalgebraStruct.comul x =
    Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing R n))
      (AlgHom.id R (CoordinateRing R n))
      ((hopfAlgebra R n).toCoalgebra.toCoalgebraStruct.comul x)
  rw [Algebra.TensorProduct.map_id]
  rfl

private theorem coordinateHopfAlgebra_counit_transport (x : CoordinateRing R n) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      (hopfAlgebra R n).toCoalgebra.toCoalgebraStruct.counit x := by
  rfl

/-- Mathlib has no lemma exposing the antipode stored by `CommHopfAlgCat.of`. This bridge locally
crosses the bundled carrier and its identity algebra equivalence, while selecting exactly the
module and Hopf-algebra dictionaries stored by `coordinateHopfAlgebra`. -/
private theorem coordinateHopfAlgebra_antipode_transport (x : CoordinateRing R n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      coordinateHopfAlgebraAlgEquiv R n
        (letI : Module R (CoordinateRing R n) :=
            (hopfAlgebra R n).toAlgebra.toModule;
          letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n;
          HopfAlgebra.antipode R (A := CoordinateRing R n) x) := by
  rfl

/-- Comultiplication on the bundled coordinate Hopf algebra agrees with the explicit localized
comultiplication after transport through `coordinateHopfAlgebraAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_comul_apply (x : CoordinateRing R n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R n).toAlgHom (comul R n x) := by
  rw [coordinateHopfAlgebra_comul_transport, eq_of_heq (hopfAlgebra_comul R n),
    AlgHom.toLinearMap_apply]

/-- The counit on the bundled coordinate Hopf algebra agrees with the explicit localized
counit after transport through `coordinateHopfAlgebraAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_counit_apply (x : CoordinateRing R n) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) = counit R n x := by
  rw [coordinateHopfAlgebra_counit_transport, eq_of_heq (hopfAlgebra_counit R n),
    AlgHom.toLinearMap_apply]

/-- The antipode on the bundled coordinate Hopf algebra agrees with inverse-matrix evaluation
after transport through `coordinateHopfAlgebraAlgEquiv`. -/
@[simp low]
theorem coordinateHopfAlgebra_antipode_apply (x : CoordinateRing R n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      coordinateHopfAlgebraAlgEquiv R n (antipode R n x) := by
  rw [coordinateHopfAlgebra_antipode_transport,
    eq_of_heq (hopfAlgebra_antipode R n), AlgHom.toLinearMap_apply]

/-- The bundled coordinate Hopf algebra retains the matrix-multiplication comultiplication on
localized generic entries. -/
@[simp]
theorem coordinateHopfAlgebra_comul_X (i j : Fin n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      (∑ k : Fin n,
        coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (i, k))) ⊗ₜ[R]
          coordinateHopfAlgebraAlgEquiv R n
            (coordinateRingMap R n (MvPolynomial.X (k, j))) :
        coordinateHopfAlgebra R n ⊗[R] coordinateHopfAlgebra R n) := by
  rw [coordinateHopfAlgebra_comul_apply, comul_X, map_sum]
  simp

/-- The bundled coordinate Hopf algebra retains the identity-matrix counit on localized generic
entries. -/
@[simp]
theorem coordinateHopfAlgebra_counit_X (i j : Fin n) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      if i = j then 1 else 0 := by
  rw [coordinateHopfAlgebra_counit_apply]
  exact counit_X R n i j

/-- The bundled coordinate Hopf algebra sends a localized generic entry under the antipode to
the corresponding inverse-matrix entry. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_X (i j : Fin n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n
          (coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      coordinateHopfAlgebraAlgEquiv R n ((localizedGenericMatrix R n)⁻¹ i j) := by
  rw [coordinateHopfAlgebra_antipode_apply, antipode_X]

/-- The general linear coordinate Hopf algebra bundled with its finite-type algebra property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  ⟨coordinateHopfAlgebra R n,
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType R (CoordinateRing R n))
      (coordinateHopfAlgebraAlgEquiv R n)⟩

/-- The underlying commutative Hopf algebra of `finiteTypeCoordinateHopfAlgebra` is
`coordinateHopfAlgebra`. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R n).obj = coordinateHopfAlgebra R n :=
  (rfl)

end GeneralLinear

end TauCeti
