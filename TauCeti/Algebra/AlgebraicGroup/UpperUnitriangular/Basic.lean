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

For a commutative ring `R`, the coordinate ring of the upper-unitriangular group `U_n` is the
polynomial algebra on the entries strictly above the diagonal.  Its generic matrix has ones on
the diagonal and zeros below it.  Matrix multiplication and inversion give the comultiplication
and antipode, so its `A`-valued points are naturally the upper-unitriangular matrices over every
commutative `R`-algebra `A`.

This is the coordinate-Hopf-algebra and functor-of-points part of the upper-unitriangular model in
Layer 5, "Unipotent groups", of the ReductiveGroups roadmap.  A subsequent closed-immersion
module can identify its map to `GL_n` with the corresponding Hopf-ideal quotient.

## Main declarations

* `TauCeti.UpperUnitriangular.CoordinateRing`: the polynomial coordinate ring of `U_n`.
* `TauCeti.UpperUnitriangular.coordinateHopfAlgebra`: its bundled commutative Hopf algebra.
* `TauCeti.UpperUnitriangular.pointsMulEquiv`: its convolution points are the existing
  `TauCeti.upperUnitriangularGroup`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct WithConv

universe u w

/-- Pairs indexing the entries strictly above the diagonal of an `n x n` matrix. -/
abbrev Index (n : Nat) := {ij : Fin n × Fin n // ij.1 < ij.2}

/-- The polynomial coordinate ring of the upper-unitriangular group. -/
abbrev CoordinateRing (R : Type u) [CommRing R] (n : Nat) := MvPolynomial (Index n) R

variable (R : Type u) [CommRing R] (n : Nat)

/-- The generic upper-unitriangular matrix. -/
noncomputable def genericMatrix : Matrix (Fin n) (Fin n) (CoordinateRing R n) :=
  fun i j => if h : i < j then MvPolynomial.X (show Index n from ⟨(i, j), h⟩)
    else if i = j then 1 else 0

@[simp]
theorem genericMatrix_apply_of_lt {i j : Fin n} (h : i < j) :
    genericMatrix R n i j = MvPolynomial.X (show Index n from ⟨(i, j), h⟩) := by
  simp [genericMatrix, h]

@[simp]
theorem genericMatrix_apply_diag (i : Fin n) : genericMatrix R n i i = 1 := by
  simp [genericMatrix]

@[simp]
theorem genericMatrix_apply_of_lt_rev {i j : Fin n} (h : j < i) :
    genericMatrix R n i j = 0 := by
  simp [genericMatrix, h.asymm, h.ne']

/-- The generic matrix is upper unitriangular. -/
theorem genericMatrix_isUpperUnitriangular : (genericMatrix R n).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro i j h
    exact genericMatrix_apply_of_lt_rev R n h
  · exact genericMatrix_apply_diag R n

/-- Evaluating the strict-upper coordinates of the generic matrix at an upper-unitriangular
matrix recovers that matrix. -/
theorem map_genericMatrix_aeval {A : Type w} [CommRing A] [Algebra R A]
    (M : Matrix (Fin n) (Fin n) A) (hM : M.IsUpperUnitriangular) :
    (genericMatrix R n).map
        (MvPolynomial.aeval fun ij : Index n => M ij.1.1 ij.1.2) = M := by
  ext i j
  by_cases hij : i < j
  · simp [Matrix.map_apply, genericMatrix, hij]
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · simp only [Matrix.map_apply, genericMatrix_apply_of_lt_rev R n hji, map_zero]
      exact (hM.isUpperTriangular hji).symm
    · simp [Matrix.map_apply, genericMatrix, hM.apply_diag]

/-- Matrix-multiplication comultiplication on the coordinate ring of `U_n`. -/
noncomputable def comul :
    CoordinateRing R n →ₐ[R] CoordinateRing R n ⊗[R] CoordinateRing R n :=
  MvPolynomial.aeval fun ij : Index n =>
    ((genericMatrix R n).map
        (includeLeft : CoordinateRing R n →ₐ[R]
          CoordinateRing R n ⊗[R] CoordinateRing R n) *
      (genericMatrix R n).map
        (includeRight : CoordinateRing R n →ₐ[R]
          CoordinateRing R n ⊗[R] CoordinateRing R n)) ij.1.1 ij.1.2

/-- Identity-matrix counit on the coordinate ring of `U_n`. -/
noncomputable def counit : CoordinateRing R n →ₐ[R] R :=
  MvPolynomial.aeval fun _ : Index n => 0

/-- Inverse-matrix antipode on the coordinate ring of `U_n`. -/
noncomputable def antipode : CoordinateRing R n →ₐ[R] CoordinateRing R n :=
  let h := genericMatrix_isUpperUnitriangular R n
  MvPolynomial.aeval fun ij : Index n =>
    ((↑((h.toGL : Matrix.GeneralLinearGroup (Fin n) (CoordinateRing R n))⁻¹) :
      Matrix (Fin n) (Fin n) (CoordinateRing R n)) ij.1.1 ij.1.2)

/-- Comultiplication evaluates the generic matrix at the product of its two tensor-factor
copies. -/
@[simp]
theorem map_comul_genericMatrix :
    (genericMatrix R n).map (comul R n) =
      (genericMatrix R n).map
          (includeLeft : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) *
        (genericMatrix R n).map
          (includeRight : CoordinateRing R n →ₐ[R]
            CoordinateRing R n ⊗[R] CoordinateRing R n) := by
  apply map_genericMatrix_aeval
  exact (genericMatrix_isUpperUnitriangular R n).map includeLeft |>.mul
    ((genericMatrix_isUpperUnitriangular R n).map includeRight)

/-- The counit evaluates the generic matrix at the identity. -/
@[simp]
theorem map_counit_genericMatrix : (genericMatrix R n).map (counit R n) = 1 := by
  ext i j
  by_cases hij : i < j
  · simp [Matrix.map_apply, genericMatrix, counit, hij, hij.ne]
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · simp [Matrix.map_apply, genericMatrix, counit, hij, hji.ne']
    · simp [Matrix.map_apply, genericMatrix, counit]

/-- The antipode evaluates the generic matrix at its inverse. -/
@[simp]
theorem map_antipode_genericMatrix :
    (genericMatrix R n).map (antipode R n) =
      (↑((genericMatrix_isUpperUnitriangular R n).toGL⁻¹) :
        Matrix (Fin n) (Fin n) (CoordinateRing R n)) := by
  let h := genericMatrix_isUpperUnitriangular R n
  let g : upperUnitriangularGroup (Fin n) (CoordinateRing R n) :=
    ⟨h.toGL⁻¹, (upperUnitriangularGroup (Fin n) (CoordinateRing R n)).inv_mem
      (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h)⟩
  rw [antipode]
  simpa only [g] using
    map_genericMatrix_aeval R n
      ((g : Matrix.GeneralLinearGroup (Fin n) (CoordinateRing R n)) :
        Matrix (Fin n) (Fin n) (CoordinateRing R n))
      (UpperUnitriangularGroup.isUpperUnitriangular g)

/-- Comultiplication on every generic matrix entry is matrix multiplication. -/
@[simp]
theorem comul_genericMatrix_apply (i j : Fin n) :
    comul R n (genericMatrix R n i j) =
      ∑ k : Fin n, genericMatrix R n i k ⊗ₜ[R] genericMatrix R n k j := by
  simpa [Matrix.map_apply, Matrix.mul_apply] using
    congrFun (congrFun (map_comul_genericMatrix R n) i) j

/-- The counit on every generic matrix entry is the corresponding identity-matrix entry. -/
@[simp]
theorem counit_genericMatrix_apply (i j : Fin n) :
    counit R n (genericMatrix R n i j) = if i = j then 1 else 0 := by
  exact congrFun (congrFun (map_counit_genericMatrix R n) i) j

/-- The antipode on every generic matrix entry is the corresponding inverse-matrix entry. -/
@[simp]
theorem antipode_genericMatrix_apply (i j : Fin n) :
    antipode R n (genericMatrix R n i j) =
      (↑((genericMatrix_isUpperUnitriangular R n).toGL⁻¹) :
        Matrix (Fin n) (Fin n) (CoordinateRing R n)) i j := by
  exact congrFun (congrFun (map_antipode_genericMatrix R n) i) j

/-- Comultiplication on a strict-upper coordinate is the corresponding entry of the product of
the two generic matrices. -/
@[simp]
theorem comul_X (ij : Index n) :
    comul R n (MvPolynomial.X ij) =
      ∑ k : Fin n,
        genericMatrix R n ij.1.1 k ⊗ₜ[R]
          genericMatrix R n k ij.1.2 := by
  have h := congrFun (congrFun (map_comul_genericMatrix R n) ij.1.1) ij.1.2
  simpa [genericMatrix_apply_of_lt R n ij.2, Matrix.mul_apply] using h

/-- The counit vanishes on every strict-upper coordinate. -/
@[simp]
theorem counit_X (ij : Index n) : counit R n (MvPolynomial.X ij) = 0 := by
  simp [counit]

private theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (CoordinateRing R n) (CoordinateRing R n) (CoordinateRing R n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R n) (.id R (CoordinateRing R n))).comp
        (comul R n)) =
      (Algebra.TensorProduct.map (.id R (CoordinateRing R n)) (comul R n)).comp
        (comul R n) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, AlgHom.id_apply]
  simp only [comul_genericMatrix_apply, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum]
  rw [Finset.sum_comm]
  rfl

private theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R n) (.id R (CoordinateRing R n))).comp
        (comul R n) =
      (Algebra.TensorProduct.lid R (CoordinateRing R n)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single i]
  · simp [genericMatrix_apply_of_lt R n hij]
  · intro k _ hki
    simp [hki.symm]
  · simp

private theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id R (CoordinateRing R n)) (counit R n)).comp
        (comul R n) =
      (Algebra.TensorProduct.rid R R (CoordinateRing R n)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp [genericMatrix_apply_of_lt R n hij]
  · intro k _ hkj
    simp [hkj]
  · simp

/-- The bialgebra structure dual to multiplication of upper-unitriangular matrices. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (CoordinateRing R n) :=
  Bialgebra.ofAlgHom (comul R n) (counit R n)
    (comul_coassoc R n) (comul_rTensor_counit R n) (comul_lTensor_counit R n)

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R n) (.id R (CoordinateRing R n))
      fun _ _ => Commute.all _ _).comp (comul R n) =
        (Algebra.ofId R (CoordinateRing R n)).comp (counit R n) := by
  apply MvPolynomial.algHom_ext
  rintro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  let h := genericMatrix_isUpperUnitriangular R n
  have hentry := congrFun (congrFun h.toGL.inv_mul ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, h, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (CoordinateRing R n)) (antipode R n)
      fun _ _ => Commute.all _ _).comp (comul R n) =
        (Algebra.ofId R (CoordinateRing R n)).comp (counit R n) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  let h := genericMatrix_isUpperUnitriangular R n
  have hentry := congrFun (congrFun h.toGL.mul_inv ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, h, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

/-- The Hopf-algebra structure dual to the upper-unitriangular group law. -/
@[instance_reducible]
noncomputable def hopfAlgebra : HopfAlgebra R (CoordinateRing R n) := by
  letI : Bialgebra R (CoordinateRing R n) := bialgebra R n
  exact HopfAlgebra.ofAlgHom (antipode R n)
    (mul_antipode_rTensor_comul R n) (mul_antipode_lTensor_comul R n)

/-- Selecting `hopfAlgebra` makes its antipode inverse-matrix evaluation. -/
theorem hopfAlgebra_antipode :
    HEq (letI : Module R (CoordinateRing R n) := (hopfAlgebra R n).toAlgebra.toModule
      letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
      HopfAlgebra.antipode R (A := CoordinateRing R n)) (antipode R n).toLinearMap :=
  heq_of_eq rfl

/-- The coordinate ring bundled with its upper-unitriangular Hopf-algebra structure. -/
noncomputable def coordinateHopfAlgebra : CommHopfAlgCat R :=
  letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
  CommHopfAlgCat.of R (CoordinateRing R n)

/-- The identity algebra equivalence to the bundled coordinate Hopf algebra. -/
noncomputable def coordinateHopfAlgebraAlgEquiv :
    CoordinateRing R n ≃ₐ[R] coordinateHopfAlgebra R n := by
  letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n
  exact AlgEquiv.refl

private theorem coordinateHopfAlgebra_comul_transport (x : CoordinateRing R n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          ((hopfAlgebra R n).toCoalgebra.toCoalgebraStruct.comul x) := by
  -- Both sides transport the stored comultiplication through the identity algebra equivalence.
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

private theorem coordinateHopfAlgebra_antipode_transport (x : CoordinateRing R n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      coordinateHopfAlgebraAlgEquiv R n
        (letI : Module R (CoordinateRing R n) := (hopfAlgebra R n).toAlgebra.toModule;
          letI : HopfAlgebra R (CoordinateRing R n) := hopfAlgebra R n;
          HopfAlgebra.antipode R (A := CoordinateRing R n) x) := by
  rfl

/-- The bundled comultiplication agrees with matrix multiplication on the raw coordinate ring. -/
@[simp low]
theorem coordinateHopfAlgebra_comul_apply (x : CoordinateRing R n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).toAlgHom
          (coordinateHopfAlgebraAlgEquiv R n).toAlgHom (comul R n x) := by
  rw [coordinateHopfAlgebra_comul_transport]
  rfl

/-- The bundled counit agrees with evaluation at the identity matrix. -/
@[simp low]
theorem coordinateHopfAlgebra_counit_apply (x : CoordinateRing R n) :
    Coalgebra.counit (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) = counit R n x := by
  rw [coordinateHopfAlgebra_counit_transport]
  rfl

/-- The bundled antipode agrees with inverse-matrix evaluation on the raw coordinate ring. -/
@[simp low]
theorem coordinateHopfAlgebra_antipode_apply (x : CoordinateRing R n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n x) =
      coordinateHopfAlgebraAlgEquiv R n (antipode R n x) := by
  rw [coordinateHopfAlgebra_antipode_transport,
    eq_of_heq (hopfAlgebra_antipode R n), AlgHom.toLinearMap_apply]

/-- The bundled comultiplication formula on a strict-upper coordinate. -/
@[simp]
theorem coordinateHopfAlgebra_comul_X (ij : Index n) :
    Coalgebra.comul (R := R) (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n (MvPolynomial.X ij)) =
      ∑ k : Fin n,
        coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n ij.1.1 k) ⊗ₜ[R]
          coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n k ij.1.2) := by
  rw [coordinateHopfAlgebra_comul_apply, comul_X, map_sum]
  simp

/-- The bundled antipode sends a generic entry to the corresponding inverse-matrix entry. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_genericMatrix_apply (i j : Fin n) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R n)
        (coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n i j)) =
      coordinateHopfAlgebraAlgEquiv R n
        ((↑((genericMatrix_isUpperUnitriangular R n).toGL⁻¹) :
          Matrix (Fin n) (Fin n) (CoordinateRing R n)) i j) := by
  rw [coordinateHopfAlgebra_antipode_apply, antipode_genericMatrix_apply]

/-- The upper-unitriangular coordinate Hopf algebra is of finite type over its base ring. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  ⟨coordinateHopfAlgebra R n,
    Algebra.FiniteType.equiv (inferInstance : Algebra.FiniteType R (CoordinateRing R n))
      (coordinateHopfAlgebraAlgEquiv R n)⟩

/-- The underlying Hopf algebra of the finite-type package is `coordinateHopfAlgebra`. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R n).obj = coordinateHopfAlgebra R n :=
  (rfl)

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluate a point of the coordinate Hopf algebra on the generic matrix. -/
private noncomputable def matrixOfPoint
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) : Matrix (Fin n) (Fin n) A :=
  (genericMatrix R n).map (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)

private theorem matrixOfPoint_isUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (matrixOfPoint R n f).IsUpperUnitriangular :=
  (genericMatrix_isUpperUnitriangular R n).map
    (f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)

@[simp]
private theorem matrixOfPoint_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) (i j : Fin n) :
    matrixOfPoint R n f i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n i j)) := by
  rfl

/-- The upper-unitriangular matrix obtained by evaluating a point on the generic matrix. -/
noncomputable def pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    upperUnitriangularGroup (Fin n) A :=
  let h := matrixOfPoint_isUpperUnitriangular R n f
  ⟨h.toGL, UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup h⟩

@[simp]
private theorem coe_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    (((pointToUpperUnitriangular R n f : upperUnitriangularGroup (Fin n) A) :
      Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
        matrixOfPoint R n f := by
  simp [pointToUpperUnitriangular]

/-- On a strict-upper entry, point evaluation is coordinate evaluation. -/
@[simp]
theorem pointToUpperUnitriangular_apply_of_lt
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) {i j : Fin n} (h : i < j) :
    ((pointToUpperUnitriangular R n f : upperUnitriangularGroup (Fin n) A) :
        Matrix.GeneralLinearGroup (Fin n) A) i j =
      f.ofConv (coordinateHopfAlgebraAlgEquiv R n
        (MvPolynomial.X (show Index n from ⟨(i, j), h⟩))) := by
  simp [pointToUpperUnitriangular, matrixOfPoint, genericMatrix_apply_of_lt, h]

/-- Evaluate the strict-upper polynomial coordinates at an upper-unitriangular matrix. -/
noncomputable def upperUnitriangularToPoint
    (g : upperUnitriangularGroup (Fin n) A) :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  toConv ((MvPolynomial.aeval fun ij : Index n =>
    ((g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)
      ij.1.1 ij.1.2).comp
        (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom)

@[simp]
theorem upperUnitriangularToPoint_apply
    (g : upperUnitriangularGroup (Fin n) A) (ij : Index n) :
    (upperUnitriangularToPoint R n g).ofConv
        (coordinateHopfAlgebraAlgEquiv R n (MvPolynomial.X ij)) =
      ((g : Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)
        ij.1.1 ij.1.2 := by
  simp [upperUnitriangularToPoint]

@[simp]
theorem pointToUpperUnitriangular_upperUnitriangularToPoint
    (g : upperUnitriangularGroup (Fin n) A) :
    pointToUpperUnitriangular R n (upperUnitriangularToPoint R n g) = g := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_pointToUpperUnitriangular]
  by_cases hij : i < j
  · rw [matrixOfPoint_apply, genericMatrix_apply_of_lt R n hij,
      upperUnitriangularToPoint_apply]
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (matrixOfPoint_isUpperUnitriangular R n _).isUpperTriangular hji |>.trans
        (UpperUnitriangularGroup.isUpperTriangular g hji).symm
    · exact (matrixOfPoint_isUpperUnitriangular R n _).apply_diag _ |>.trans
        (UpperUnitriangularGroup.apply_diag g _).symm

@[simp]
theorem upperUnitriangularToPoint_pointToUpperUnitriangular
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    upperUnitriangularToPoint R n (pointToUpperUnitriangular R n f) = f := by
  apply WithConv.ext
  have hcomp :
      (upperUnitriangularToPoint R n (pointToUpperUnitriangular R n f)).ofConv.comp
          (coordinateHopfAlgebraAlgEquiv R n).toAlgHom =
        f.ofConv.comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp [AlgHom.comp_apply, upperUnitriangularToPoint, pointToUpperUnitriangular,
      matrixOfPoint, genericMatrix, ij.2]
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (coordinateHopfAlgebraAlgEquiv R n).surjective x
  exact DFunLike.congr_fun hcomp y

/-- Evaluation on the generic matrix carries convolution to matrix multiplication. -/
@[simp]
theorem pointToUpperUnitriangular_mul
    (f g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointToUpperUnitriangular R n (f * g) =
      pointToUpperUnitriangular R n f * pointToUpperUnitriangular R n g := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i < j
  · simp only [pointToUpperUnitriangular_apply_of_lt R n _ hij]
    rw [AlgHom.convMul_apply, coordinateHopfAlgebra_comul_X]
    simp only [map_sum, lift_tmul, Subgroup.coe_mul, Units.val_mul,
      coe_pointToUpperUnitriangular]
    -- Normalize the subgroup and unit coercions to ordinary matrix multiplication.
    change (∑ k : Fin n,
      f.ofConv (coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n i k)) *
        g.ofConv (coordinateHopfAlgebraAlgEquiv R n (genericMatrix R n k j))) =
      ∑ k : Fin n, matrixOfPoint R n f i k * matrixOfPoint R n g k j
    apply Finset.sum_congr rfl
    intro k _
    rw [← matrixOfPoint_apply R n f, ← matrixOfPoint_apply R n g]
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (UpperUnitriangularGroup.isUpperTriangular
        (pointToUpperUnitriangular R n (f * g)) hji).trans
          ((UpperUnitriangularGroup.isUpperTriangular
            (pointToUpperUnitriangular R n f * pointToUpperUnitriangular R n g)) hji).symm
    · exact (UpperUnitriangularGroup.apply_diag
        (pointToUpperUnitriangular R n (f * g)) _).trans
          (UpperUnitriangularGroup.apply_diag
            (pointToUpperUnitriangular R n f * pointToUpperUnitriangular R n g) _).symm

/-- The convolution group of points of the coordinate Hopf algebra is the ordinary
upper-unitriangular matrix group. -/
noncomputable def pointsMulEquiv :
    WithConv (coordinateHopfAlgebra R n →ₐ[R] A) ≃*
      upperUnitriangularGroup (Fin n) A where
  toFun := pointToUpperUnitriangular R n
  invFun := upperUnitriangularToPoint R n
  left_inv := upperUnitriangularToPoint_pointToUpperUnitriangular R n
  right_inv := pointToUpperUnitriangular_upperUnitriangularToPoint R n
  map_mul' := pointToUpperUnitriangular_mul R n

/-- The forward map of `pointsMulEquiv` is evaluation on the generic matrix. -/
@[simp]
theorem pointsMulEquiv_apply
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv R n f = pointToUpperUnitriangular R n f :=
  (rfl)

/-- The inverse map of `pointsMulEquiv` is polynomial evaluation on strict-upper entries. -/
@[simp]
theorem pointsMulEquiv_symm_apply (g : upperUnitriangularGroup (Fin n) A) :
    (pointsMulEquiv R n).symm g = upperUnitriangularToPoint R n g :=
  (rfl)

/-- Reading a point as an upper-unitriangular matrix commutes with maps of value algebras. -/
theorem pointToUpperUnitriangular_mapValue {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointToUpperUnitriangular R n
        (AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ f) =
      UpperUnitriangularGroup.map φ.toRingHom (pointToUpperUnitriangular R n f) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i < j
  · rw [pointToUpperUnitriangular_apply_of_lt R n _ hij,
      UpperUnitriangularGroup.map_apply,
      pointToUpperUnitriangular_apply_of_lt R n f hij]
    rfl
  · obtain hji | rfl := lt_or_eq_of_le (le_of_not_gt hij)
    · exact (UpperUnitriangularGroup.isUpperTriangular
        (pointToUpperUnitriangular R n
          (AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ f)) hji).trans
          (UpperUnitriangularGroup.isUpperTriangular
            (UpperUnitriangularGroup.map φ.toRingHom
              (pointToUpperUnitriangular R n f)) hji).symm
    · exact (UpperUnitriangularGroup.apply_diag
        (pointToUpperUnitriangular R n
          (AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ f)) _).trans
          (UpperUnitriangularGroup.apply_diag
            (UpperUnitriangularGroup.map φ.toRingHom
              (pointToUpperUnitriangular R n f)) _).symm

end Points

end TauCeti.UpperUnitriangular
