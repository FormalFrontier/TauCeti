/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Basic

/-!
# Geometry of weight-unipotent subgroup schemes

For an integer weight `w i` on each coordinate of `GL_N`, the weight-unipotent subgroup has
matrix entries fixed to the identity whenever `w i ≤ w j`. The remaining entries, indexed by
pairs with `w j < w i`, are free polynomial coordinates. This file identifies its coordinate
algebra with the polynomial algebra on those pairs.

The presentation is obtained directly from the determinant localization defining `GL_N`. The
generic weight-unipotent matrix is block triangular with identity diagonal blocks, so its
determinant is one and polynomial evaluation extends across the localization. The defining
quotient relations then give mutually inverse maps.

The polynomial presentation proves that the represented subgroup is smooth over every
commutative base ring and geometrically connected over a field. A forthcoming pointwise
unipotence theorem will supply the remaining property required of the unipotent factor in the
dynamic Levi decomposition.

## Main declarations

* `TauCeti.GeneralLinear.WeightUnipotentIndex`: the free matrix coordinates `w j < w i`.
* `TauCeti.GeneralLinear.weightUnipotentCoordinateAlgEquiv`: the polynomial presentation of the
  weight-unipotent coordinate algebra.
* `TauCeti.GeneralLinear.instSmoothWeightUnipotentCoordinateHopfAlgebra`: smoothness over the
  base ring.
* `geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra`: geometric
  connectedness over a field.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This advances the dynamic approach to parabolics and Levi decomposition in Layer 7 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable (R : Type u) [CommRing R] {N : ℕ}

/-- Pairs indexing the matrix entries not fixed by the weight-unipotent relations. -/
abbrev WeightUnipotentIndex (w : Fin N → ℤ) :=
  {ij : Fin N × Fin N // w ij.2 < w ij.1}

/-- The polynomial matrix whose free entries are precisely those strictly below the weight-block
diagonal, with identity matrices on the diagonal blocks. -/
def weightUnipotentPolynomialGenericMatrix (w : Fin N → ℤ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (WeightUnipotentIndex w) R) :=
  fun i j ↦ if h : w j < w i then MvPolynomial.X ⟨(i, j), h⟩
    else if i = j then 1 else 0

/-- A free entry of the polynomial weight-unipotent matrix is its corresponding variable. -/
@[simp]
theorem weightUnipotentPolynomialGenericMatrix_apply_of_lt (w : Fin N → ℤ)
    {i j : Fin N} (hij : w j < w i) :
    weightUnipotentPolynomialGenericMatrix R w i j =
      MvPolynomial.X ⟨(i, j), hij⟩ := by
  simp [weightUnipotentPolynomialGenericMatrix, hij]

/-- An entry on or above the weight-block diagonal is the corresponding identity entry. -/
@[simp]
theorem weightUnipotentPolynomialGenericMatrix_apply_of_le (w : Fin N → ℤ)
    {i j : Fin N} (hij : w i ≤ w j) :
    weightUnipotentPolynomialGenericMatrix R w i j =
      (1 : Matrix (Fin N) (Fin N) (MvPolynomial (WeightUnipotentIndex w) R)) i j := by
  simp [weightUnipotentPolynomialGenericMatrix, not_lt.mpr hij, Matrix.one_apply]

/-- The polynomial weight-unipotent matrix is block triangular for the decreasing weight
filtration. -/
theorem weightUnipotentPolynomialGenericMatrix_blockTriangular (w : Fin N → ℤ) :
    (weightUnipotentPolynomialGenericMatrix R w).BlockTriangular
      (OrderDual.toDual ∘ w) := by
  intro i j hij
  have hwiwj : w i < w j := OrderDual.toDual_lt_toDual.mp hij
  have hne : i ≠ j := fun h ↦ hwiwj.ne (congrArg w h)
  simpa [Matrix.one_apply, hne] using
    weightUnipotentPolynomialGenericMatrix_apply_of_le R w hwiwj.le

/-- Every diagonal weight block of the polynomial weight-unipotent matrix is the identity. -/
private theorem weightUnipotentPolynomialGenericMatrix_toSquareBlock
    (w : Fin N → ℤ) (a : ℤᵒᵈ) :
    (weightUnipotentPolynomialGenericMatrix R w).toSquareBlock
        (OrderDual.toDual ∘ w) a = 1 := by
  classical
  apply Matrix.ext
  intro i j
  have hweight : w i.1 = w j.1 := by
    exact congrArg OrderDual.ofDual (i.2.trans j.2.symm)
  by_cases hij : i = j
  · subst j
    simp [Matrix.toSquareBlock_def]
  · have hij' : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
    simp [Matrix.toSquareBlock_def,
      weightUnipotentPolynomialGenericMatrix_apply_of_le R w hweight.le, hij, hij']

/-- The determinant of the polynomial weight-unipotent matrix is one. -/
@[simp]
theorem weightUnipotentPolynomialGenericMatrix_det (w : Fin N → ℤ) :
    (weightUnipotentPolynomialGenericMatrix R w).det = 1 := by
  classical
  rw [(weightUnipotentPolynomialGenericMatrix_blockTriangular R w).det]
  apply Finset.prod_eq_one
  intro a _
  rw [weightUnipotentPolynomialGenericMatrix_toSquareBlock R w a, Matrix.det_one]

/-- Evaluate the matrix-monoid polynomial coordinates at the generic weight-unipotent matrix. -/
private def weightUnipotentPolynomialEvaluation (w : Fin N → ℤ) :
    MatrixMonoid.CoordinateRing R N →ₐ[R] MvPolynomial (WeightUnipotentIndex w) R :=
  MvPolynomial.aeval fun ij ↦ weightUnipotentPolynomialGenericMatrix R w ij.1 ij.2

private theorem weightUnipotentPolynomialEvaluation_determinant (w : Fin N → ℤ) :
    weightUnipotentPolynomialEvaluation R w
        (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) R)) = 1 := by
  rw [weightUnipotentPolynomialEvaluation, AlgHom.map_det,
    Matrix.mvPolynomialX_mapMatrix_aeval,
    weightUnipotentPolynomialGenericMatrix_det]

/-- Extend polynomial evaluation across the determinant localization defining `GL_N`. -/
private def weightUnipotentLocalizedEvaluation (w : Fin N → ℤ) :
    CoordinateRing R N →ₐ[R] MvPolynomial (WeightUnipotentIndex w) R :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) R))
    (by rw [weightUnipotentPolynomialEvaluation_determinant R w]; exact isUnit_one)

private theorem weightUnipotentLocalizedEvaluation_coordinateRingMap
    (w : Fin N → ℤ) (x : MatrixMonoid.CoordinateRing R N) :
    weightUnipotentLocalizedEvaluation R w (coordinateRingMap R N x) =
      weightUnipotentPolynomialEvaluation R w x := by
  rw [coordinateRingMap_apply]
  simp [-coordinateRingMap_apply, weightUnipotentLocalizedEvaluation]

/-- Polynomial evaluation extended across the determinant localization and the bundled
coordinate algebra of `GL_N`. -/
private def weightUnipotentAmbientToPolynomial (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N →ₐ[R] MvPolynomial (WeightUnipotentIndex w) R :=
  (weightUnipotentLocalizedEvaluation R w).comp
    (coordinateHopfAlgebraAlgEquiv R N).symm.toAlgHom

private theorem weightUnipotentAmbientToPolynomial_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightUnipotentAmbientToPolynomial R w ((genericMatrix R N) i j) =
      weightUnipotentPolynomialGenericMatrix R w i j := by
  calc
    _ = weightUnipotentLocalizedEvaluation R w
        ((coordinateHopfAlgebraAlgEquiv R N).symm
          (coordinateHopfAlgebraAlgEquiv R N
            (coordinateRingMap R N (MvPolynomial.X (i, j))))) := by
      rw [genericMatrix_apply]
      rfl
    _ = weightUnipotentLocalizedEvaluation R w
        (coordinateRingMap R N (MvPolynomial.X (i, j))) :=
      congrArg (weightUnipotentLocalizedEvaluation R w)
        ((coordinateHopfAlgebraAlgEquiv R N).symm_apply_apply _)
    _ = weightUnipotentPolynomialEvaluation R w (MvPolynomial.X (i, j)) :=
      weightUnipotentLocalizedEvaluation_coordinateRingMap R w _
    _ = _ := by simp [weightUnipotentPolynomialEvaluation]

private theorem weightUnipotentAmbientToPolynomial_eq_zero
    (w : Fin N → ℤ) (x : coordinateHopfAlgebra R N)
    (hx : x ∈ (weightUnipotentDefiningHopfIdeal R w).toIdeal) :
    weightUnipotentAmbientToPolynomial R w x = 0 := by
  apply RingHom.mem_ker.mp
  have hx' : x ∈ Ideal.span (weightUnipotentRelationSet R w) := by
    simpa only [weightUnipotentDefiningHopfIdeal_toIdeal] using hx
  refine Ideal.span_le.2 ?_ hx'
  intro y hy
  rw [mem_weightUnipotentRelationSet_iff] at hy
  obtain ⟨i, j, hij, rfl⟩ := hy
  apply RingHom.mem_ker.mpr
  rw [map_sub, weightUnipotentAmbientToPolynomial_genericMatrix_apply,
    weightUnipotentPolynomialGenericMatrix_apply_of_le R w hij]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- The quotient coordinate algebra maps to its free polynomial coordinates. -/
private def weightUnipotentQuotientToPolynomial (w : Fin N → ℤ) :
    weightUnipotentCoordinateHopfAlgebra R w →ₐ[R]
      MvPolynomial (WeightUnipotentIndex w) R :=
  Ideal.Quotient.liftₐ _ (weightUnipotentAmbientToPolynomial R w)
    (weightUnipotentAmbientToPolynomial_eq_zero R w)

/-- The free polynomial coordinates map back to the corresponding quotient matrix entries. -/
private def weightUnipotentPolynomialToQuotient (w : Fin N → ℤ) :
    MvPolynomial (WeightUnipotentIndex w) R →ₐ[R]
      weightUnipotentCoordinateHopfAlgebra R w :=
  MvPolynomial.aeval fun ij ↦
    Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal
      ((genericMatrix R N) ij.1.1 ij.1.2)

private theorem weightUnipotentQuotientToPolynomial_mk_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightUnipotentQuotientToPolynomial R w
        (Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal
          ((genericMatrix R N) i j)) =
      weightUnipotentPolynomialGenericMatrix R w i j := by
  have hcomp := Ideal.Quotient.liftₐ_comp
    (weightUnipotentDefiningHopfIdeal R w).toIdeal
    (weightUnipotentAmbientToPolynomial R w)
    (weightUnipotentAmbientToPolynomial_eq_zero R w)
  exact (DFunLike.congr_fun hcomp ((genericMatrix R N) i j)).trans
    (weightUnipotentAmbientToPolynomial_genericMatrix_apply R w i j)

private theorem weightUnipotentQuotientToPolynomial_comp_polynomialToQuotient
    (w : Fin N → ℤ) :
    (weightUnipotentQuotientToPolynomial R w).comp
        (weightUnipotentPolynomialToQuotient R w) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro ij
  rw [AlgHom.comp_apply, weightUnipotentPolynomialToQuotient,
    MvPolynomial.aeval_X,
    weightUnipotentQuotientToPolynomial_mk_genericMatrix_apply,
    weightUnipotentPolynomialGenericMatrix_apply_of_lt R w ij.2,
    AlgHom.id_apply]

private theorem weightUnipotentPolynomialToQuotient_comp_quotientToPolynomial
    (w : Fin N → ℤ) :
    (weightUnipotentPolynomialToQuotient R w).comp
        (weightUnipotentQuotientToPolynomial R w) = AlgHom.id R _ := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective R
    (weightUnipotentDefiningHopfIdeal R w).toIdeal x
  have hcomp :
      ((weightUnipotentPolynomialToQuotient R w).comp
        (weightUnipotentQuotientToPolynomial R w)).comp
          (Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal) =
      (AlgHom.id R _).comp
          (Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal) := by
    apply coordinateHopfAlgebra_algHom_ext R N
    intro i j
    rw [← genericMatrix_apply]
    simp only [AlgHom.comp_apply]
    by_cases hij : w j < w i
    · rw [
        weightUnipotentQuotientToPolynomial_mk_genericMatrix_apply,
        weightUnipotentPolynomialGenericMatrix_apply_of_lt R w hij,
        weightUnipotentPolynomialToQuotient, MvPolynomial.aeval_X,
        AlgHom.id_apply]
    · have hle : w i ≤ w j := not_lt.mp hij
      rw [weightUnipotentQuotientToPolynomial_mk_genericMatrix_apply,
        weightUnipotentPolynomialGenericMatrix_apply_of_le R w hle,
        AlgHom.id_apply]
      apply (Ideal.quotientEquivAlgOfEq R
        (weightUnipotentDefiningHopfIdeal_toIdeal R w)).injective
      simpa only [weightUnipotentPolynomialToQuotient, Matrix.one_apply, apply_ite,
        map_one, map_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk] using
        (quotient_genericMatrix_apply_of_le R w hle).symm
  exact DFunLike.congr_fun hcomp y

/-- The weight-unipotent coordinate algebra is a polynomial algebra on the entries `X_ij` for
which `w j < w i`. -/
noncomputable def weightUnipotentCoordinateAlgEquiv (w : Fin N → ℤ) :
    weightUnipotentCoordinateHopfAlgebra R w ≃ₐ[R]
      MvPolynomial (WeightUnipotentIndex w) R :=
  AlgEquiv.ofAlgHom
    (weightUnipotentQuotientToPolynomial R w)
    (weightUnipotentPolynomialToQuotient R w)
    (weightUnipotentQuotientToPolynomial_comp_polynomialToQuotient R w)
    (weightUnipotentPolynomialToQuotient_comp_quotientToPolynomial R w)

/-- The polynomial presentation sends a canonical quotient generic-matrix entry to the
corresponding polynomial weight-unipotent matrix entry. -/
theorem weightUnipotentCoordinateAlgEquiv_mk_genericMatrix_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightUnipotentCoordinateAlgEquiv R w
        (Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal
          ((genericMatrix R N) i j)) =
      weightUnipotentPolynomialGenericMatrix R w i j := by
  unfold weightUnipotentCoordinateAlgEquiv
  exact weightUnipotentQuotientToPolynomial_mk_genericMatrix_apply R w i j

@[simp]
private theorem weightUnipotentCoordinateAlgEquiv_mk_apply
    (w : Fin N → ℤ) (i j : Fin N) :
    weightUnipotentCoordinateAlgEquiv R w
        (Ideal.Quotient.mk (weightUnipotentDefiningHopfIdeal R w).toIdeal
          ((coordinateHopfAlgebraAlgEquiv R N)
            ((coordinateRingMap R N) (MvPolynomial.X (i, j))))) =
      weightUnipotentPolynomialGenericMatrix R w i j := by
  rw [← genericMatrix_apply (R := R) (n := N) i j,
    ← Ideal.Quotient.mkₐ_eq_mk (R₁ := R)]
  exact weightUnipotentCoordinateAlgEquiv_mk_genericMatrix_apply R w i j

/-- The inverse polynomial presentation sends a free variable to its quotient matrix entry. -/
@[simp]
theorem weightUnipotentCoordinateAlgEquiv_symm_X
    (w : Fin N → ℤ) (ij : WeightUnipotentIndex w) :
    (weightUnipotentCoordinateAlgEquiv R w).symm (MvPolynomial.X ij) =
      Ideal.Quotient.mkₐ R (weightUnipotentDefiningHopfIdeal R w).toIdeal
        ((genericMatrix R N) ij.1.1 ij.1.2) := by
  apply (weightUnipotentCoordinateAlgEquiv R w).injective
  rw [AlgEquiv.apply_symm_apply,
    weightUnipotentCoordinateAlgEquiv_mk_genericMatrix_apply,
    weightUnipotentPolynomialGenericMatrix_apply_of_lt R w ij.2]

/-- The weight-unipotent coordinate algebra is smooth over its base ring. -/
instance instSmoothWeightUnipotentCoordinateHopfAlgebra (w : Fin N → ℤ) :
    Algebra.Smooth R (weightUnipotentCoordinateHopfAlgebra R w) := by
  let _ : Algebra.Smooth R (MvPolynomial (WeightUnipotentIndex w) R) :=
    ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (weightUnipotentCoordinateAlgEquiv R w).symm

/-- Over an integral domain, the weight-unipotent coordinate algebra is an integral domain. -/
instance instIsDomainWeightUnipotentCoordinateHopfAlgebra
    [IsDomain R] (w : Fin N → ℤ) :
    IsDomain (weightUnipotentCoordinateHopfAlgebra R w) :=
  (weightUnipotentCoordinateAlgEquiv R w).toRingEquiv.isDomain_iff.mpr inferInstance

/-- The weight-unipotent subgroup is geometrically connected over every field. -/
theorem geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightUnipotentCoordinateHopfAlgebra k w) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let e : weightUnipotentCoordinateHopfAlgebra k w ⊗[k] K ≃+*
      MvPolynomial (WeightUnipotentIndex w) K :=
    (Algebra.TensorProduct.congr (weightUnipotentCoordinateAlgEquiv k w)
        (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv.trans <|
      (Algebra.TensorProduct.comm k
        (MvPolynomial (WeightUnipotentIndex w) k) K).toRingEquiv.trans <|
        (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr inferInstance

end

end TauCeti.GeneralLinear
