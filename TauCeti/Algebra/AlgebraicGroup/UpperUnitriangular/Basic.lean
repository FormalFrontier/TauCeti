/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular

/-!
# The upper-unitriangular coordinate Hopf algebra

For a commutative ring `R`, the coordinate ring of the upper-unitriangular group `U_m` is the
polynomial algebra on the entries strictly above the diagonal.  Its generic matrix has ones on
the diagonal and zeros below it.  Matrix multiplication and inversion give the comultiplication
and antipode, so its `A`-valued points are naturally the upper-unitriangular matrices over every
commutative `R`-algebra `A`.

This supplies a multiplicative equivalence between Hopf-algebra points and upper-unitriangular
matrices over each commutative `R`-algebra, natural in the value algebra. It does not yet package a
natural isomorphism of `pointsFunctor`s or a group scheme. This is the coordinate-Hopf-algebra part
of the upper-unitriangular model in Layer 5, "Unipotent groups", of the ReductiveGroups roadmap. A
subsequent closed-immersion module can identify its map to `GL_m` with the corresponding Hopf-ideal
quotient.

## Main declarations

* `TauCeti.UpperUnitriangular.CoordinateRing`: the polynomial coordinate ring of `U_m`.
* `TauCeti.UpperUnitriangular.genericMatrix`: the generic upper-unitriangular matrix.
* `TauCeti.UpperUnitriangular.coordinateHopfAlgebra`: its bundled commutative Hopf algebra.
* `TauCeti.UpperUnitriangular.finiteTypeCoordinateHopfAlgebra`: its finite-type package.
* `TauCeti.UpperUnitriangular.pointsMulEquiv`: its convolution points are the existing
  `TauCeti.upperUnitriangularGroup`.
* `TauCeti.UpperUnitriangular.pointToUpperUnitriangular_mapValue`: the point identification is
  natural in the value algebra.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

The coordinate-ring and Hopf-algebra layout follows `TauCeti.MatrixMonoid` in
`GeneralLinear.Coordinate.Bialgebra` and `TauCeti.GeneralLinear` in
`GeneralLinear.Coordinate.HopfAlgebra`; the points layout follows
`GeneralLinear.FunctorOfPoints`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct WithConv

universe u w

/-- Pairs indexing the entries strictly above the diagonal of a square matrix. -/
abbrev Index (m : Type*) [LT m] := {ij : m × m // ij.1 < ij.2}

/-- The polynomial coordinate ring of the upper-unitriangular group. -/
abbrev CoordinateRing (R : Type u) [CommSemiring R] (m : Type*) [LT m] :=
  MvPolynomial (Index m) R

section Bialgebra

variable (R : Type u) [CommSemiring R] (m : Type*) [LinearOrder m]

/-- The generic upper-unitriangular matrix. -/
noncomputable def genericMatrix : Matrix m m (CoordinateRing R m) :=
  fun i j => if h : i < j then MvPolynomial.X (show Index m from ⟨(i, j), h⟩)
    else if i = j then 1 else 0

@[simp]
theorem genericMatrix_apply_of_lt {i j : m} (h : i < j) :
    genericMatrix R m i j = MvPolynomial.X (show Index m from ⟨(i, j), h⟩) := by
  simp [genericMatrix, h]

@[simp]
theorem genericMatrix_apply_diag (i : m) : genericMatrix R m i i = 1 := by
  simp [genericMatrix]

@[simp]
theorem genericMatrix_apply_eq_zero_of_gt {i j : m} (h : j < i) :
    genericMatrix R m i j = 0 := by
  simp [genericMatrix, h.asymm, h.ne']

/-- The generic matrix is upper unitriangular. -/
theorem isUpperUnitriangular_genericMatrix : (genericMatrix R m).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro i j h
    exact genericMatrix_apply_eq_zero_of_gt R m h
  · exact genericMatrix_apply_diag R m

private theorem matrix_eq_of_isUpperUnitriangular_of_apply_of_lt {A : Type*} [Semiring A]
    {M N : Matrix m m A} (hM : M.IsUpperUnitriangular) (hN : N.IsUpperUnitriangular)
    (h : ∀ i j, i < j → M i j = N i j) : M = N := by
  ext i j
  by_cases hij : i < j
  · exact h i j hij
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (hM.isUpperTriangular hji).trans (hN.isUpperTriangular hji).symm
    · exact (hM.apply_diag _).trans (hN.apply_diag _).symm

/-- Evaluating the strict-upper coordinates of the generic matrix at an upper-unitriangular
matrix recovers that matrix. -/
theorem map_aeval_genericMatrix {A : Type w} [CommSemiring A] [Algebra R A]
    (M : Matrix m m A) (hM : M.IsUpperUnitriangular) :
    (genericMatrix R m).map
        (MvPolynomial.aeval fun ij : Index m => M ij.1.1 ij.1.2) = M := by
  apply matrix_eq_of_isUpperUnitriangular_of_apply_of_lt (m := m)
    ((isUpperUnitriangular_genericMatrix R m).map _) hM
  intro i j hij
  simp [Matrix.map_apply, genericMatrix, hij]

variable [Fintype m]

/-- Matrix-multiplication comultiplication on the coordinate ring of `U_m`. -/
noncomputable def comul :
    CoordinateRing R m →ₐ[R] CoordinateRing R m ⊗[R] CoordinateRing R m :=
  MvPolynomial.aeval fun ij : Index m =>
    ((genericMatrix R m).map
        (includeLeft : CoordinateRing R m →ₐ[R]
          CoordinateRing R m ⊗[R] CoordinateRing R m) *
      (genericMatrix R m).map
        (includeRight : CoordinateRing R m →ₐ[R]
          CoordinateRing R m ⊗[R] CoordinateRing R m)) ij.1.1 ij.1.2

omit [Fintype m] in
/-- Identity-matrix counit on the coordinate ring of `U_m`. -/
noncomputable def counit : CoordinateRing R m →ₐ[R] R :=
  MvPolynomial.aeval fun ij : Index m => (1 : Matrix m m R) ij.1.1 ij.1.2

/-- Comultiplication evaluates the generic matrix at the product of its two tensor-factor
copies. -/
@[simp]
theorem map_comul_genericMatrix :
    (genericMatrix R m).map (comul R m) =
      (genericMatrix R m).map
          (includeLeft : CoordinateRing R m →ₐ[R]
            CoordinateRing R m ⊗[R] CoordinateRing R m) *
        (genericMatrix R m).map
          (includeRight : CoordinateRing R m →ₐ[R]
            CoordinateRing R m ⊗[R] CoordinateRing R m) := by
  apply map_aeval_genericMatrix
  exact (isUpperUnitriangular_genericMatrix R m).map includeLeft |>.mul
    ((isUpperUnitriangular_genericMatrix R m).map includeRight)

omit [Fintype m] in
/-- The counit evaluates the generic matrix at the identity. -/
@[simp]
theorem map_counit_genericMatrix : (genericMatrix R m).map (counit R m) = 1 := by
  simpa [counit] using map_aeval_genericMatrix R m (1 : Matrix m m R)
    (Matrix.isUpperUnitriangular_one (m := m) (R := R))

/-- Comultiplication on every generic matrix entry is matrix multiplication. -/
theorem comul_genericMatrix_apply (i j : m) :
    comul R m (genericMatrix R m i j) =
      ∑ k : m, genericMatrix R m i k ⊗ₜ[R] genericMatrix R m k j := by
  simpa [Matrix.map_apply, Matrix.mul_apply] using
    congrFun (congrFun (map_comul_genericMatrix R m) i) j

omit [Fintype m] in
/-- The counit on every generic matrix entry is the corresponding identity-matrix entry. -/
@[simp]
theorem counit_genericMatrix_apply (i j : m) :
    counit R m (genericMatrix R m i j) = if i = j then 1 else 0 := by
  exact congrFun (congrFun (map_counit_genericMatrix R m) i) j

/-- Comultiplication on a strict-upper coordinate is the corresponding entry of the product of
the two generic matrices. -/
@[simp]
theorem comul_X (ij : Index m) :
    comul R m (MvPolynomial.X ij) =
      ∑ k : m,
        genericMatrix R m ij.1.1 k ⊗ₜ[R]
          genericMatrix R m k ij.1.2 := by
  rw [← genericMatrix_apply_of_lt R m ij.2]
  exact comul_genericMatrix_apply R m ij.1.1 ij.1.2

omit [Fintype m] in
/-- The counit vanishes on every strict-upper coordinate. -/
@[simp]
theorem counit_X (ij : Index m) : counit R m (MvPolynomial.X ij) = 0 := by
  simp [counit, Matrix.one_apply_ne ij.2.ne]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (CoordinateRing R m) (CoordinateRing R m) (CoordinateRing R m)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R m) (.id R (CoordinateRing R m))).comp
        (comul R m)) =
      (Algebra.TensorProduct.map (.id R (CoordinateRing R m)) (comul R m)).comp
        (comul R m) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, AlgHom.id_apply]
  simp only [comul_genericMatrix_apply, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum]
  rw [Finset.sum_comm]
  rfl

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R m) (.id R (CoordinateRing R m))).comp
        (comul R m) =
      (Algebra.TensorProduct.lid R (CoordinateRing R m)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single i]
  · simp [genericMatrix_apply_of_lt R m hij]
  · intro k _ hki
    simp [hki.symm]
  · simp

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id R (CoordinateRing R m)) (counit R m)).comp
        (comul R m) =
      (Algebra.TensorProduct.rid R R (CoordinateRing R m)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp [genericMatrix_apply_of_lt R m hij]
  · intro k _ hkj
    simp [hkj]
  · simp

/-- The bialgebra structure dual to multiplication of upper-unitriangular matrices. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (CoordinateRing R m) :=
  Bialgebra.ofAlgHom (comul R m) (counit R m)
    (comul_coassoc R m) (comul_rTensor_counit R m) (comul_lTensor_counit R m)

end Bialgebra

section HopfAlgebra

variable (R : Type u) [CommRing R] (m : Type*) [Fintype m] [LinearOrder m]

/-- Inverse-matrix antipode on the coordinate ring of `U_m`. -/
noncomputable def antipode : CoordinateRing R m →ₐ[R] CoordinateRing R m :=
  let h := isUpperUnitriangular_genericMatrix R m
  MvPolynomial.aeval fun ij : Index m =>
    ((↑((h.toGL : Matrix.GeneralLinearGroup m (CoordinateRing R m))⁻¹) :
      Matrix m m (CoordinateRing R m)) ij.1.1 ij.1.2)

/-- The antipode evaluates the generic matrix at its inverse. -/
@[simp]
theorem map_antipode_genericMatrix :
    (genericMatrix R m).map (antipode R m) =
      (↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
        Matrix m m (CoordinateRing R m)) := by
  let h := isUpperUnitriangular_genericMatrix R m
  let g : upperUnitriangularGroup m (CoordinateRing R m) :=
    ⟨h.toGL⁻¹, (upperUnitriangularGroup m (CoordinateRing R m)).inv_mem
      (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h)⟩
  rw [antipode]
  simpa only [g] using
    map_aeval_genericMatrix R m
      ((g : Matrix.GeneralLinearGroup m (CoordinateRing R m)) :
        Matrix m m (CoordinateRing R m))
      (UpperUnitriangularGroup.isUpperUnitriangular g)

/-- The antipode on every generic matrix entry is the corresponding inverse-matrix entry. -/
@[simp]
theorem antipode_genericMatrix_apply (i j : m) :
    antipode R m (genericMatrix R m i j) =
      (↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
        Matrix m m (CoordinateRing R m)) i j := by
  exact congrFun (congrFun (map_antipode_genericMatrix R m) i) j

/-- The antipode sends a strict-upper coordinate to the corresponding inverse-matrix entry. -/
@[simp]
theorem antipode_X (ij : Index m) :
    antipode R m (MvPolynomial.X ij) =
      (↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
        Matrix m m (CoordinateRing R m)) ij.1.1 ij.1.2 := by
  rw [← genericMatrix_apply_of_lt R m ij.2]
  exact antipode_genericMatrix_apply R m ij.1.1 ij.1.2

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R m) (.id R (CoordinateRing R m))
      fun _ _ => Commute.all _ _).comp (comul R m) =
        (Algebra.ofId R (CoordinateRing R m)).comp (counit R m) := by
  apply MvPolynomial.algHom_ext
  rintro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  let h := isUpperUnitriangular_genericMatrix R m
  have hentry := congrFun (congrFun h.toGL.inv_mul ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, h, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (CoordinateRing R m)) (antipode R m)
      fun _ _ => Commute.all _ _).comp (comul R m) =
        (Algebra.ofId R (CoordinateRing R m)).comp (counit R m) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  let h := isUpperUnitriangular_genericMatrix R m
  have hentry := congrFun (congrFun h.toGL.mul_inv ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, h, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

/-- The Hopf-algebra structure dual to the upper-unitriangular group law. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R (CoordinateRing R m) := by
  letI : Bialgebra R (CoordinateRing R m) := bialgebra R m
  exact HopfAlgebra.ofAlgHom (antipode R m)
    (mul_antipode_rTensor_comul R m) (mul_antipode_lTensor_comul R m)

/-- Selecting `hopfAlgebra R m` makes its comultiplication the explicit map `comul R m`.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_comul :
    HEq (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R m) := (hopfAlgebra R m).toCoalgebra
      Coalgebra.comul (R := R) (A := CoordinateRing R m)) (comul R m).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R m` makes its counit the explicit map `counit R m`.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_counit :
    HEq (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R m) := (hopfAlgebra R m).toCoalgebra
      Coalgebra.counit (R := R) (A := CoordinateRing R m)) (counit R m).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R m` makes its antipode inverse-matrix evaluation.
The equality is heterogeneous because opacity hides the stored module structure. -/
theorem hopfAlgebra_antipode :
    HEq (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule
      letI : HopfAlgebra R (CoordinateRing R m) := hopfAlgebra R m
      HopfAlgebra.antipode R (A := CoordinateRing R m)) (antipode R m).toLinearMap :=
  heq_of_eq rfl

/-- The coordinate ring bundled with its upper-unitriangular Hopf-algebra structure. -/
noncomputable def coordinateHopfAlgebra : CommHopfAlgCat R :=
  letI : HopfAlgebra R (CoordinateRing R m) := hopfAlgebra R m
  CommHopfAlgCat.of R (CoordinateRing R m)

/-- The identity algebra equivalence to the bundled coordinate Hopf algebra. -/
noncomputable def coordinateHopfAlgebraAlgEquiv :
    CoordinateRing R m ≃ₐ[R] coordinateHopfAlgebra R m := by
  letI : HopfAlgebra R (CoordinateRing R m) := hopfAlgebra R m
  exact AlgEquiv.refl

/-- Mathlib has no `CommHopfAlgCat.of_comul` lemma exposing the comultiplication stored by
`CommHopfAlgCat.of`. This bridge crosses that bundled carrier and its identity algebra
equivalence; after those reductions, transport is `Algebra.TensorProduct.map_id`. -/
private theorem coordinateHopfAlgebra_comul_transport (x : CoordinateRing R m) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R m).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R m).toAlgHom
          ((hopfAlgebra R m).toCoalgebra.toCoalgebraStruct.comul x) := by
  change (hopfAlgebra R m).toCoalgebra.toCoalgebraStruct.comul x =
    Algebra.TensorProduct.map (AlgHom.id R (CoordinateRing R m))
      (AlgHom.id R (CoordinateRing R m))
      ((hopfAlgebra R m).toCoalgebra.toCoalgebraStruct.comul x)
  rw [Algebra.TensorProduct.map_id]
  rfl

/-- This bridge exposes the counit stored by `CommHopfAlgCat.of` across the bundled carrier and
its identity algebra equivalence. -/
private theorem coordinateHopfAlgebra_counit_transport (x : CoordinateRing R m) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) =
      (hopfAlgebra R m).toCoalgebra.toCoalgebraStruct.counit x := by
  rfl

/-- Mathlib has no lemma exposing the antipode stored by `CommHopfAlgCat.of`. This bridge crosses
the bundled carrier and its identity algebra equivalence while selecting the stored dictionaries. -/
private theorem coordinateHopfAlgebra_antipode_transport (x : CoordinateRing R m) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) =
      coordinateHopfAlgebraAlgEquiv R m
        (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule;
          letI : HopfAlgebra R (CoordinateRing R m) := hopfAlgebra R m;
          HopfAlgebra.antipode R (A := CoordinateRing R m) x) := by
  rfl

/-- The bundled comultiplication agrees with matrix multiplication on the raw coordinate ring. -/
@[simp low]
theorem coordinateHopfAlgebra_comul_apply (x : CoordinateRing R m) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R m).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R m).toAlgHom (comul R m x) := by
  rw [coordinateHopfAlgebra_comul_transport, eq_of_heq (hopfAlgebra_comul R m),
    AlgHom.toLinearMap_apply]

/-- The bundled counit agrees with evaluation at the identity matrix. -/
@[simp low]
theorem coordinateHopfAlgebra_counit_apply (x : CoordinateRing R m) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) = counit R m x := by
  rw [coordinateHopfAlgebra_counit_transport, eq_of_heq (hopfAlgebra_counit R m),
    AlgHom.toLinearMap_apply]

/-- The bundled antipode agrees with inverse-matrix evaluation on the raw coordinate ring. -/
@[simp low]
theorem coordinateHopfAlgebra_antipode_apply (x : CoordinateRing R m) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m x) =
      coordinateHopfAlgebraAlgEquiv R m (antipode R m x) := by
  rw [coordinateHopfAlgebra_antipode_transport,
    eq_of_heq (hopfAlgebra_antipode R m), AlgHom.toLinearMap_apply]

/-- The bundled comultiplication formula on a strict-upper coordinate. -/
@[simp]
theorem coordinateHopfAlgebra_comul_X (ij : Index m) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
      ∑ k : m,
        coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m ij.1.1 k) ⊗ₜ[R]
          coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m k ij.1.2) := by
  rw [coordinateHopfAlgebra_comul_apply, comul_X, map_sum]
  simp

/-- The bundled counit vanishes on every strict-upper coordinate. -/
@[simp]
theorem coordinateHopfAlgebra_counit_X (ij : Index m) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) = 0 := by
  rw [coordinateHopfAlgebra_counit_apply, counit_X]

/-- The bundled antipode sends a strict-upper coordinate to the corresponding inverse-matrix
entry. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_X (ij : Index m) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
      coordinateHopfAlgebraAlgEquiv R m
        ((↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
          Matrix m m (CoordinateRing R m)) ij.1.1 ij.1.2) := by
  rw [coordinateHopfAlgebra_antipode_apply, antipode_X]

/-- The bundled antipode sends a generic entry to the corresponding inverse-matrix entry. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_genericMatrix_apply (i j : m) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m i j)) =
      coordinateHopfAlgebraAlgEquiv R m
        ((↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
          Matrix m m (CoordinateRing R m)) i j) := by
  rw [coordinateHopfAlgebra_antipode_apply, antipode_genericMatrix_apply]

/-- `coordinateHopfAlgebra` bundled as a finite-type commutative Hopf algebra, using that its
polynomial coordinate ring is a finitely generated `R`-algebra. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  letI : HopfAlgebra R (CoordinateRing R m) := hopfAlgebra R m
  FiniteTypeCommHopfAlgCat.of R (CoordinateRing R m)

/-- The underlying Hopf algebra of the finite-type package is `coordinateHopfAlgebra`. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R m).obj = coordinateHopfAlgebra R m :=
  (rfl)

/-- Two algebra homomorphisms out of the bundled coordinate Hopf algebra are equal if they agree
on every strict-upper coordinate. -/
theorem coordinateHopfAlgebra_algHom_ext {T : Type*} [Semiring T] [Algebra R T]
    {f g : coordinateHopfAlgebra R m →ₐ[R] T}
    (h : ∀ ij : Index m,
      f (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
        g (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij))) : f = g := by
  have hcomp : f.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom =
      g.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro ij
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using h ij
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (coordinateHopfAlgebraAlgEquiv R m).surjective x
  exact DFunLike.congr_fun hcomp y

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

private theorem upperUnitriangularGroup_ext_of_lt
    (g h : upperUnitriangularGroup m A)
    (heq : ∀ i j, i < j →
      ((g : Matrix.GeneralLinearGroup m A) : Matrix m m A) i j =
        ((h : Matrix.GeneralLinearGroup m A) : Matrix m m A) i j) : g = h := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congrFun (congrFun
    (matrix_eq_of_isUpperUnitriangular_of_apply_of_lt (m := m)
      (UpperUnitriangularGroup.isUpperUnitriangular g)
      (UpperUnitriangularGroup.isUpperUnitriangular h) heq) i) j

/-- Evaluate a point of the coordinate Hopf algebra on the generic matrix. -/
private noncomputable def matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) : Matrix m m A :=
  (genericMatrix R m).map (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom)

private theorem isUpperUnitriangular_matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (matrixOfPoint R m f).IsUpperUnitriangular :=
  (isUpperUnitriangular_genericMatrix R m).map
    (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R m).toAlgHom)

@[simp]
private theorem matrixOfPoint_apply
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) (i j : m) :
    matrixOfPoint R m f i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m i j)) := by
  rfl

/-- The upper-unitriangular matrix obtained by evaluating a point on the generic matrix. -/
noncomputable def pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    upperUnitriangularGroup m A :=
  let h := isUpperUnitriangular_matrixOfPoint R m f
  ⟨h.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h⟩

@[simp]
private theorem coe_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    (((pointToUpperUnitriangular R m f : upperUnitriangularGroup m A) :
      Matrix.GeneralLinearGroup m A) : Matrix m m A) =
        matrixOfPoint R m f := by
  simp [pointToUpperUnitriangular]

/-- On a strict-upper entry, point evaluation is coordinate evaluation. -/
@[simp]
theorem pointToUpperUnitriangular_apply_of_lt
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) {i j : m} (h : i < j) :
    ((pointToUpperUnitriangular R m f : upperUnitriangularGroup m A) :
        Matrix.GeneralLinearGroup m A) i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R m
        (MvPolynomial.X (show Index m from ⟨(i, j), h⟩))) := by
  simp [pointToUpperUnitriangular, matrixOfPoint, genericMatrix_apply_of_lt, h]

/-- Evaluate the strict-upper polynomial coordinates at an upper-unitriangular matrix. -/
noncomputable def upperUnitriangularToPoint
    (g : upperUnitriangularGroup m A) :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  toConv ((MvPolynomial.aeval fun ij : Index m =>
    ((g : Matrix.GeneralLinearGroup m A) : Matrix m m A)
      ij.1.1 ij.1.2).comp
        (coordinateHopfAlgebraAlgEquiv R m).symm.toAlgHom)

@[simp]
theorem upperUnitriangularToPoint_apply
    (g : upperUnitriangularGroup m A) (ij : Index m) :
    (upperUnitriangularToPoint R m g).ofConv
        (coordinateHopfAlgebraAlgEquiv R m (MvPolynomial.X ij)) =
      ((g : Matrix.GeneralLinearGroup m A) : Matrix m m A)
        ij.1.1 ij.1.2 := by
  simp [upperUnitriangularToPoint]

@[simp]
theorem pointToUpperUnitriangular_upperUnitriangularToPoint
    (g : upperUnitriangularGroup m A) :
    pointToUpperUnitriangular R m (upperUnitriangularToPoint R m g) = g := by
  apply upperUnitriangularGroup_ext_of_lt
  intro i j hij
  rw [coe_pointToUpperUnitriangular]
  rw [matrixOfPoint_apply, genericMatrix_apply_of_lt R m hij,
    upperUnitriangularToPoint_apply]

@[simp]
theorem upperUnitriangularToPoint_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    upperUnitriangularToPoint R m (pointToUpperUnitriangular R m f) = f := by
  apply WithConv.ext
  apply coordinateHopfAlgebra_algHom_ext R m
  intro ij
  simp [upperUnitriangularToPoint, pointToUpperUnitriangular, matrixOfPoint,
    genericMatrix, ij.2]

/-- Evaluation on the generic matrix carries convolution to matrix multiplication. -/
@[simp]
theorem pointToUpperUnitriangular_mul
    (f g : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointToUpperUnitriangular R m (f * g) =
      pointToUpperUnitriangular R m f * pointToUpperUnitriangular R m g := by
  apply upperUnitriangularGroup_ext_of_lt
  intro i j hij
  simp only [pointToUpperUnitriangular_apply_of_lt R m _ hij]
  rw [AlgHom.convMul_apply, coordinateHopfAlgebra_comul_X]
  simp only [map_sum, lift_tmul, Subgroup.coe_mul, Units.val_mul,
    coe_pointToUpperUnitriangular, Matrix.mul_apply, matrixOfPoint_apply]

/-- The convolution group of points of the coordinate Hopf algebra is the ordinary
upper-unitriangular matrix group. -/
noncomputable def pointsMulEquiv :
    WithConv (coordinateHopfAlgebra R m →ₐ[R] A) ≃*
      upperUnitriangularGroup m A where
  toFun := pointToUpperUnitriangular R m
  invFun := upperUnitriangularToPoint R m
  left_inv := upperUnitriangularToPoint_pointToUpperUnitriangular R m
  right_inv := pointToUpperUnitriangular_upperUnitriangularToPoint R m
  map_mul' := pointToUpperUnitriangular_mul R m

/-- The forward map of `pointsMulEquiv` is evaluation on the generic matrix. -/
@[simp]
theorem pointsMulEquiv_apply
    (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointsMulEquiv R m f = pointToUpperUnitriangular R m f :=
  (rfl)

/-- The inverse map of `pointsMulEquiv` is polynomial evaluation on strict-upper entries. -/
@[simp]
theorem pointsMulEquiv_symm_apply (g : upperUnitriangularGroup m A) :
    (pointsMulEquiv R m).symm g = upperUnitriangularToPoint R m g :=
  (rfl)

/-- Reading a point as an upper-unitriangular matrix commutes with maps of value algebras. -/
theorem pointToUpperUnitriangular_mapValue {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R m →ₐ[R] A)) :
    pointToUpperUnitriangular R m
        (AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ f) =
      UpperUnitriangularGroup.map φ.toRingHom (pointToUpperUnitriangular R m f) := by
  apply upperUnitriangularGroup_ext_of_lt
  intro i j hij
  rw [pointToUpperUnitriangular_apply_of_lt R m _ hij,
    UpperUnitriangularGroup.map_apply,
    pointToUpperUnitriangular_apply_of_lt R m f hij]
  rfl

end Points

end HopfAlgebra

end TauCeti.UpperUnitriangular
