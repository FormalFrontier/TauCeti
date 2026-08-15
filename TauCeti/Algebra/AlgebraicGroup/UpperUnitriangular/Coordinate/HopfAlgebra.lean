/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Coordinate.Bialgebra
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular

/-!
# The upper-unitriangular coordinate Hopf algebra

For a commutative ring `R`, inversion of the generic upper-unitriangular matrix equips its
coordinate bialgebra with an antipode. This file packages that structure as a commutative Hopf
algebra and records that its polynomial coordinate ring is of finite type.

This is the coordinate-Hopf-algebra part of the upper-unitriangular model in Layer 5,
"Unipotent groups", of the ReductiveGroups roadmap. A subsequent closed-immersion module can
identify its map to `GL_m` with the corresponding Hopf-ideal quotient.

## Main declarations

* `TauCeti.UpperUnitriangular.antipode`: inverse-matrix evaluation on the coordinate ring.
* `TauCeti.UpperUnitriangular.coordinateHopfAlgebra`: its bundled commutative Hopf algebra.
* `TauCeti.UpperUnitriangular.finiteTypeCoordinateHopfAlgebra`: its finite-type package.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

The layout follows `TauCeti.GeneralLinear` in `GeneralLinear.Coordinate.HopfAlgebra`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct

universe u v

section HopfAlgebra

variable (R : Type u) [CommRing R] (m : Type v) [Fintype m] [LinearOrder m]

/-- The private bialgebra dictionary assembled from the public coordinate structure maps and
their laws. -/
@[instance_reducible]
private noncomputable def bialgebra : Bialgebra R (CoordinateRing R m) :=
  Bialgebra.ofAlgHom (comul R m) (counit R m)
    (comul_coassoc R m) (comul_rTensor_counit R m) (comul_lTensor_counit R m)

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
      (genericMatrix R m)⁻¹ := by
  have hinv :
      (↑((isUpperUnitriangular_genericMatrix R m).toGL⁻¹) :
        Matrix m m (CoordinateRing R m)).IsUpperUnitriangular :=
    UpperUnitriangularGroup.mem_iff.mp
      ((upperUnitriangularGroup m (CoordinateRing R m)).inv_mem
        (UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup
          (isUpperUnitriangular_genericMatrix R m)))
  rw [antipode]
  simpa using map_aeval_genericMatrix R m _ hinv

/-- The antipode on every generic matrix entry is the corresponding inverse-matrix entry. -/
@[simp]
theorem antipode_genericMatrix_apply (i j : m) :
    antipode R m (genericMatrix R m i j) =
      (genericMatrix R m)⁻¹ i j := by
  exact congrFun (congrFun (map_antipode_genericMatrix R m) i) j

/-- The antipode sends a strict-upper coordinate to the corresponding inverse-matrix entry. -/
@[simp]
theorem antipode_X (ij : Index m) :
    antipode R m (MvPolynomial.X ij) =
      (genericMatrix R m)⁻¹ ij.1.1 ij.1.2 := by
  rw [← genericMatrix_apply_of_lt R m ij.2]
  exact antipode_genericMatrix_apply R m ij.1.1 ij.1.2

private theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R m) (.id R (CoordinateRing R m))
      fun _ _ => Commute.all _ _).comp (comul R m) =
        (Algebra.ofId R (CoordinateRing R m)).comp (counit R m) := by
  apply MvPolynomial.algHom_ext
  rintro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  have hentry := congrFun (congrFun
    (isUpperUnitriangular_genericMatrix R m).toGL.inv_mul ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

private theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (CoordinateRing R m)) (antipode R m)
      fun _ _ => Commute.all _ _).comp (comul R m) =
        (Algebra.ofId R (CoordinateRing R m)).comp (counit R m) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, counit_X]
  have hentry := congrFun (congrFun
    (isUpperUnitriangular_genericMatrix R m).toGL.mul_inv ij.1.1) ij.1.2
  simpa [antipode_genericMatrix_apply, Matrix.mul_apply,
    Matrix.one_apply, ij.2.ne] using hentry

/-- The Hopf-algebra structure dual to the upper-unitriangular group law.

This is intentionally a named value, not an instance. Callers that need typeclass-selected Hopf
operations should use `coordinateHopfAlgebra`, or install this value in a deliberately local
scope. -/
@[instance_reducible]
private noncomputable def hopfAlgebra : HopfAlgebra R (CoordinateRing R m) := by
  letI : Bialgebra R (CoordinateRing R m) := bialgebra R m
  exact HopfAlgebra.ofAlgHom (antipode R m)
    (mul_antipode_rTensor_comul R m) (mul_antipode_lTensor_comul R m)

/-- Selecting `hopfAlgebra R m` makes its comultiplication the explicit map `comul R m`.
The equality is heterogeneous because opacity hides the stored module structure. -/
private theorem hopfAlgebra_comul :
    HEq (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R m) := (hopfAlgebra R m).toCoalgebra
      Coalgebra.comul (R := R) (A := CoordinateRing R m)) (comul R m).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R m` makes its counit the explicit map `counit R m`.
The equality is heterogeneous because opacity hides the stored module structure. -/
private theorem hopfAlgebra_counit :
    HEq (letI : Module R (CoordinateRing R m) := (hopfAlgebra R m).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R m) := (hopfAlgebra R m).toCoalgebra
      Coalgebra.counit (R := R) (A := CoordinateRing R m)) (counit R m).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `hopfAlgebra R m` makes its antipode inverse-matrix evaluation.
The equality is heterogeneous because opacity hides the stored module structure. -/
private theorem hopfAlgebra_antipode :
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
        ((genericMatrix R m)⁻¹ ij.1.1 ij.1.2) := by
  rw [coordinateHopfAlgebra_antipode_apply, antipode_X]

/-- The bundled antipode sends a generic entry to the corresponding inverse-matrix entry. -/
@[simp]
theorem coordinateHopfAlgebra_antipode_genericMatrix_apply (i j : m) :
    HopfAlgebra.antipode R (A := coordinateHopfAlgebra R m)
        (coordinateHopfAlgebraAlgEquiv R m (genericMatrix R m i j)) =
      coordinateHopfAlgebraAlgEquiv R m
        ((genericMatrix R m)⁻¹ i j) := by
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


end HopfAlgebra

end TauCeti.UpperUnitriangular
