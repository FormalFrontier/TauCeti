/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.WeightTorus
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Dynamic subgroups of the general linear group from weights

An integer weight `w i` on each coordinate of `GL_N` defines the cocharacter

```text
lambda_w(t) = diag(t ^ w(0), ..., t ^ w(N - 1)).
```

Conjugation multiplies the `(i,j)` matrix entry by `t ^ (w i - w j)`. Consequently its
dynamic parabolic consists exactly of matrices that are block triangular for the weight
filtration: an entry vanishes whenever `w i < w j`. The dynamic limit deletes the entries
between distinct weight spaces. This also identifies the Levi subgroup with the block diagonal
matrices and the dynamic unipotent subgroup with the matrices acting trivially on every
associated-graded weight space.

The results hold over every commutative base ring and every commutative value algebra. In
particular they do not infer the vanishing of a negative Laurent coefficient by cancellation;
the coefficient is read directly, so zero divisors cause no problem.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.weightCocharacter`: the cocharacter attached to integer weights.
* `TauCeti.GeneralLinear.Dynamic.mem_weightCocharacter_parabolic_iff`: its dynamic parabolic is
  the block-triangular subgroup for the weight filtration.
* `TauCeti.GeneralLinear.Dynamic.pointsMulEquiv_limit_weightCocharacter_apply`: its limit keeps
  exactly the entries between equal-weight coordinates.
* `TauCeti.GeneralLinear.Dynamic.mem_weightCocharacter_levi_iff`: its Levi is block diagonal.
* `TauCeti.GeneralLinear.Dynamic.mem_weightCocharacter_unipotent_iff`: its unipotent subgroup
  acts trivially on the associated graded.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This supplies the higher-rank block-cocharacter calculation requested by the dynamic-parabolic
route in Layer 7, "Structure theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v

variable {R : Type u} [CommRing R] {N : ℕ}

/-- The diagonal unit family `i ↦ t ^ w i` attached to integer weights. -/
def weightDiagonalUnits {A : Type v} [CommMonoid A] (w : Fin N → ℤ) :
    Aˣ →* (Fin N → Aˣ) where
  toFun t i := t ^ w i
  map_one' := by ext i; simp
  map_mul' t s := by ext i; simp [mul_zpow]

/-- The `i`-th diagonal coordinate of the weight cocharacter is `t ^ w i`. -/
@[simp]
theorem weightDiagonalUnits_apply {A : Type v} [CommMonoid A] (w : Fin N → ℤ)
    (t : Aˣ) (i : Fin N) : weightDiagonalUnits w t i = t ^ w i :=
  (rfl)

/-- The rank-one character group algebra, presented as Laurent polynomials. -/
private noncomputable def rankOneCharacterBialgEquiv :
    MonoidAlgebra R (Multiplicative (ULift.{u} Unit →₀ ℤ)) ≃ₐc[R]
      LaurentPolynomial R :=
  (MonoidAlgebra.domCongrBialgEquiv R R
      (AddEquiv.toMultiplicative (Finsupp.uniqueAddEquiv (ULift.up ())))).trans
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).symm

/-- The coordinate Hopf-algebra morphism of the cocharacter with weights `w`. -/
private noncomputable def weightCocharacterCoordinateMap (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N ⟶ _root_.CommHopfAlgCat.of R (LaurentPolynomial R) :=
  weightTorusCoordinateMap (R := R) (fun i _ ↦ w i) ≫
    _root_.CommHopfAlgCat.ofHom (rankOneCharacterBialgEquiv (R := R)).toBialgHom

/-- The cocharacter of `GL_N` acting on the `i`-th coordinate with integer weight `w i`. -/
noncomputable def weightCocharacter (w : Fin N → ℤ) :
    coordinateHopfAlgebra R N →ₐc[R] LaurentPolynomial R :=
  (weightCocharacterCoordinateMap (R := R) w).hom

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- Applying the inclusion `A[X] → A[T;T⁻¹]` to a general-linear point applies that
inclusion entrywise to its matrix. -/
theorem pointsMulEquiv_ofPolyPoint
    (F : WithConv (coordinateHopfAlgebra R N →ₐ[R] Polynomial A)) :
    pointsMulEquiv N (Cocharacter.ofPolyPoint A F) =
      Matrix.GeneralLinearGroup.map
        (Polynomial.toLaurentAlg.restrictScalars R).toRingHom (pointsMulEquiv N F) := by
  rw [Cocharacter.ofPolyPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

/-- Evaluating a polynomial-valued general-linear point at zero evaluates every matrix entry
at zero. -/
theorem pointsMulEquiv_evalZeroPoint
    (F : WithConv (coordinateHopfAlgebra R N →ₐ[R] Polynomial A)) :
    pointsMulEquiv N (Cocharacter.evalZeroPoint A F) =
      Matrix.GeneralLinearGroup.map
        ((Polynomial.aeval (0 : A)).restrictScalars R).toRingHom (pointsMulEquiv N F) := by
  rw [Cocharacter.evalZeroPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

/-- The weight cocharacter on algebra-valued points. -/
noncomputable def weightCocharacterPoints (w : Fin N → ℤ) :
    WithConv (LaurentPolynomial R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp <|
    (diagGL (k := A)).comp <|
      (weightDiagonalUnits w).comp
        (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).toMonoidHom

/-- Reading the weight cocharacter as a matrix gives `diag(t ^ w i)`. -/
theorem pointsMulEquiv_weightCocharacterPoints (w : Fin N → ℤ)
    (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    pointsMulEquiv N (weightCocharacterPoints w f) =
      diagGL (weightDiagonalUnits w (MultiplicativeGroup.pointsMulEquiv f)) := by
  simp [weightCocharacterPoints]

private theorem mapPointsFunctor_weightCocharacterCoordinateMap_app (w : Fin N → ℤ)
    (A : CommAlgCat.{v} R) (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    (CommHopfAlgCat.mapPointsFunctor
      (weightCocharacterCoordinateMap (R := R) w)).app A f =
      weightCocharacterPoints w f := by
  let q : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} Unit →₀ ℤ)) →ₐ[R] A) :=
    (CommHopfAlgCat.mapPointsFunctor
      (_root_.CommHopfAlgCat.ofHom
        (rankOneCharacterBialgEquiv (R := R)).toBialgHom)).app A f
  rw [weightCocharacterCoordinateMap,
    CommHopfAlgCat.mapPointsFunctor_comp_app_apply]
  -- The composition lemma leaves the intermediate rank-one torus point definitionally equal
  -- to `q`, but supplies no rewrite lemma for that local point.
  change (CommHopfAlgCat.mapPointsFunctor
    (weightTorusCoordinateMap (R := R) (fun i (_ : ULift.{u} Unit) ↦ w i))).app A q = _
  rw [mapPointsFunctor_weightTorusCoordinateMap_app]
  have hq : SplitTorus.pointsMulEquiv q (ULift.up ()) =
      MultiplicativeGroup.pointsMulEquiv f := by
    ext
    rw [SplitTorus.pointsMulEquiv_apply_coe,
      MultiplicativeGroup.pointsMulEquiv_apply,
      MultiplicativeGroup.unitOfPoint_val]
    simp only [q, CommHopfAlgCat.mapPointsFunctor_app_apply,
      WithConv.ofConv_toConv, AlgHom.comp_apply]
    congr 1
    rw [rankOneCharacterBialgEquiv]
    simp only [CommHopfAlgCat.hom_ofHom]
    apply (AlgEquiv.symm_apply_eq
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toAlgEquiv).mpr
    -- `simp` does not unfold `domCongrBialgEquiv`, so expose its underlying `domCongr`.
    change MonoidAlgebra.domCongr R R
        (AddEquiv.toMultiplicative (Finsupp.uniqueAddEquiv (ULift.up ())))
          (MonoidAlgebra.single
            (Multiplicative.ofAdd (Finsupp.single (ULift.up ()) 1)) 1) =
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ).toAlgEquiv (LaurentPolynomial.T 1)
    simpa using
      (AddMonoidAlgebra.toMultiplicativeBialgEquiv_single (R := R) (A := R) (M := ℤ) 1 1).symm
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_weightCocharacterPoints]
  congr 1
  funext i
  rw [diagonalTorusCoordinates_pointsMap_weightCharacterMap]
  simp [torusCharacter_def, weightDiagonalUnits, hq]

/-- The abstract cocharacter action agrees with the concrete weight cocharacter on points. -/
theorem pointsHom_weightCocharacter (w : Fin N → ℤ) (t : Aˣ) :
    Cocharacter.pointsHom A (weightCocharacter (R := R) w) t =
      weightCocharacterPoints w
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) := by
  rw [Cocharacter.pointsHom_apply]
  -- Unfold only the public cocharacter wrapper to expose the coordinate morphism used above.
  change (CommHopfAlgCat.mapPointsFunctor
      (weightCocharacterCoordinateMap (R := R) w)).app (CommAlgCat.of R A)
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) = _
  rw [mapPointsFunctor_weightCocharacterCoordinateMap_app]

/-- The cocharacter with weights `w` sends `t` to `diag(t ^ w i)`. -/
theorem pointsMulEquiv_pointsHom_weightCocharacter (w : Fin N → ℤ) (t : Aˣ) :
    pointsMulEquiv N (Cocharacter.pointsHom A (weightCocharacter (R := R) w) t) =
      diagGL (weightDiagonalUnits w t) := by
  rw [pointsHom_weightCocharacter, pointsMulEquiv_weightCocharacterPoints,
    MulEquiv.apply_symm_apply]

/-- Conjugation by the weight cocharacter is conjugation by the diagonal matrix
`diag(T ^ w i)`. -/
theorem pointsMulEquiv_conjugate_weightCocharacter (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) :
    pointsMulEquiv N (Cocharacter.conjugate A (weightCocharacter (R := R) w) g) =
      diagGL (weightDiagonalUnits w (Cocharacter.genericUnit A)) *
        Matrix.GeneralLinearGroup.map
          (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toRingHom
          (pointsMulEquiv N g) *
        (diagGL (weightDiagonalUnits w (Cocharacter.genericUnit A)))⁻¹ := by
  rw [Cocharacter.conjugate_apply, map_mul, map_mul, map_inv,
    Cocharacter.genericPoint_eq_pointsHom,
    pointsMulEquiv_pointsHom_weightCocharacter, Cocharacter.constPoint_apply,
    ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

private theorem genericUnit_zpow_val (n : ℤ) :
    ((Cocharacter.genericUnit A ^ n : (LaurentPolynomial A)ˣ) : LaurentPolynomial A) =
      LaurentPolynomial.T n := by
  let f : LaurentPolynomial A →ₐ[A] LaurentPolynomial A := AlgHom.id A _
  have hunit : Cocharacter.genericUnit A = MultiplicativeGroup.unitOfPoint f := by
    apply Units.ext
    simp [f]
  rw [hunit, ← MultiplicativeGroup.point_T (R := A)]
  exact DFunLike.congr_fun (MultiplicativeGroup.point_unitOfPoint f) (LaurentPolynomial.T n)

/-- The `(i,j)` entry of conjugation by the weight cocharacter is
`g_ij * T ^ (w i - w j)`. -/
theorem pointsMulEquiv_conjugate_weightCocharacter_apply (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) (i j : Fin N) :
    (pointsMulEquiv N (Cocharacter.conjugate A (weightCocharacter (R := R) w) g) :
      Matrix (Fin N) (Fin N) (LaurentPolynomial A)) i j =
      LaurentPolynomial.C ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
        LaurentPolynomial.T (w i - w j) := by
  rw [pointsMulEquiv_conjugate_weightCocharacter]
  simp only [Units.val_mul, ← map_inv diagGL, diagGL_coe,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.GeneralLinearGroup.map_apply,
    weightDiagonalUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  have hinv :
      (((Cocharacter.genericUnit A ^ w j)⁻¹ : (LaurentPolynomial A)ˣ) :
          LaurentPolynomial A) = LaurentPolynomial.T (-w j) := by
    rw [← zpow_neg, genericUnit_zpow_val]
  rw [genericUnit_zpow_val]
  -- Normalize the pointwise inverse of the diagonal function and the scalar-extension map;
  -- neither wrapper has an application lemma at this expression.
  change LaurentPolynomial.T (w i) *
      LaurentPolynomial.C ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
        (((Cocharacter.genericUnit A ^ w j)⁻¹ : (LaurentPolynomial A)ˣ) :
          LaurentPolynomial A) = _
  rw [hinv]
  rw [LaurentPolynomial.T_mul, LaurentPolynomial.mul_T_assoc]
  congr 2

/-- The polynomial matrix obtained by removing the forbidden negative-weight entries and
replacing a nonnegative weight difference by the corresponding power of `X`. -/
private noncomputable def weightPolynomialMatrix (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) :
    Matrix (Fin N) (Fin N) (Polynomial A) := fun i j ↦
  if w j ≤ w i then
    Polynomial.C ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
      Polynomial.X ^ (w i - w j).toNat
  else 0

private theorem toLaurent_weightPolynomialMatrix_apply (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) (i j : Fin N) :
    Polynomial.toLaurent (weightPolynomialMatrix w g i j) =
      LaurentPolynomial.C ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
        LaurentPolynomial.T (w i - w j) := by
  by_cases hji : w j ≤ w i
  · simp only [weightPolynomialMatrix, hji, ↓reduceIte, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow]
    congr 2
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hji)
  · have hij : w i < w j := lt_of_not_ge hji
    have hzero :
        (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j = 0 :=
      hg hij
    have hzeroC := congrArg (LaurentPolynomial.C (R := A)) hzero
    simp only [weightPolynomialMatrix, hji, ↓reduceIte, map_zero]
    rw [hzeroC, map_zero, zero_mul]

private theorem map_weightPolynomialMatrix (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) :
    (weightPolynomialMatrix w g).map Polynomial.toLaurent =
      (pointsMulEquiv N
        (Cocharacter.conjugate A (weightCocharacter (R := R) w) g) :
          Matrix (Fin N) (Fin N) (LaurentPolynomial A)) := by
  ext i j
  rw [Matrix.map_apply, toLaurent_weightPolynomialMatrix_apply w g hg,
    pointsMulEquiv_conjugate_weightCocharacter_apply]

private theorem det_weightPolynomialMatrix (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) :
    (weightPolynomialMatrix w g).det =
      Polynomial.C (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).det := by
  apply Polynomial.toLaurent_injective
  rw [RingHom.map_det]
  -- `RingHom.map_det` uses `mapMatrix`, while the entrywise comparison is stated with the
  -- definitionally equal `Matrix.map`; Mathlib has no bridge lemma in this direction.
  change ((weightPolynomialMatrix w g).map Polynomial.toLaurent).det = _
  rw [map_weightPolynomialMatrix w g hg, Polynomial.toLaurent_C]
  rw [pointsMulEquiv_conjugate_weightCocharacter]
  let d : GL (Fin N) (LaurentPolynomial A) :=
    diagGL (weightDiagonalUnits w (Cocharacter.genericUnit A))
  let m : GL (Fin N) (LaurentPolynomial A) :=
    Matrix.GeneralLinearGroup.map
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toRingHom
      (pointsMulEquiv N g)
  change (d * m * d⁻¹ : Matrix (Fin N) (Fin N) (LaurentPolynomial A)).det = _
  calc
    _ = (d : Matrix (Fin N) (Fin N) (LaurentPolynomial A)).det *
          (m : Matrix (Fin N) (Fin N) (LaurentPolynomial A)).det *
          ((d⁻¹ : GL (Fin N) (LaurentPolynomial A)) :
            Matrix (Fin N) (Fin N) (LaurentPolynomial A)).det := by
        rw [Matrix.det_mul, Matrix.det_mul]
    _ = (m : Matrix (Fin N) (Fin N) (LaurentPolynomial A)).det := by
        have hdet : Matrix.GeneralLinearGroup.det d *
            Matrix.GeneralLinearGroup.det m *
              (Matrix.GeneralLinearGroup.det d)⁻¹ =
            Matrix.GeneralLinearGroup.det m := by
          rw [mul_comm (Matrix.GeneralLinearGroup.det d), mul_assoc,
            mul_inv_cancel, mul_one]
        rw [← Matrix.GeneralLinearGroup.val_det_apply,
          ← Matrix.GeneralLinearGroup.val_det_apply,
          ← Matrix.GeneralLinearGroup.val_det_apply]
        rw [show Matrix.GeneralLinearGroup.det (d⁻¹) =
          (Matrix.GeneralLinearGroup.det d)⁻¹ by exact map_inv _ d]
        exact congrArg Units.val hdet
    _ = _ := (RingHom.map_det
      (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toRingHom
      (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A)).symm

/-- The polynomial-valued general-linear point extending weight conjugation. -/
private noncomputable def weightPolynomialExtension (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) :
    WithConv (coordinateHopfAlgebra R N →ₐ[R] Polynomial A) :=
  (pointsMulEquiv (R := R) (A := Polynomial A) N).symm <|
    Matrix.GeneralLinearGroup.mk'' (weightPolynomialMatrix w g) (by
      rw [det_weightPolynomialMatrix w g hg]
      exact IsUnit.map Polynomial.C.toMonoidHom
        (Matrix.GeneralLinearGroup.det (pointsMulEquiv N g)).isUnit)

private theorem pointsMulEquiv_weightPolynomialExtension (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) :
    (pointsMulEquiv N (weightPolynomialExtension (R := R) w g hg) :
      Matrix (Fin N) (Fin N) (Polynomial A)) = weightPolynomialMatrix w g := by
  rw [weightPolynomialExtension, MulEquiv.apply_symm_apply]
  rfl

private theorem ofPolyPoint_weightPolynomialExtension (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
      (OrderDual.toDual ∘ w)) :
    Cocharacter.ofPolyPoint A (weightPolynomialExtension (R := R) w g hg) =
      Cocharacter.conjugate A (weightCocharacter (R := R) w) g := by
  apply (pointsMulEquiv (R := R) (A := LaurentPolynomial A) N).injective
  rw [pointsMulEquiv_ofPolyPoint]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply,
    pointsMulEquiv_weightPolynomialExtension]
  exact congrFun (congrFun (map_weightPolynomialMatrix w g hg) i) j

/-- Membership in the dynamic parabolic for the weight cocharacter is exactly block
triangularity for the decreasing weight filtration. Equivalently, `g_ij = 0` whenever
`w i < w j`. -/
@[simp]
theorem mem_weightCocharacter_parabolic_iff (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) :
    g ∈ Cocharacter.parabolic A (weightCocharacter (R := R) w) ↔
      (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
        (OrderDual.toDual ∘ w) := by
  constructor
  · rw [Cocharacter.mem_parabolic_iff]
    rintro ⟨F, hF⟩ i j hij
    change w i < w j at hij
    have hmat := congrArg (pointsMulEquiv (R := R) (A := LaurentPolynomial A) N) hF
    have hentry := congrArg
      (fun M : GL (Fin N) (LaurentPolynomial A) ↦
        (M : Matrix (Fin N) (Fin N) (LaurentPolynomial A)) i j) hmat
    rw [pointsMulEquiv_ofPolyPoint,
      pointsMulEquiv_conjugate_weightCocharacter_apply] at hentry
    simp only [Matrix.GeneralLinearGroup.map_apply] at hentry
    -- Normalize the scalar-restriction map in this one matrix entry to the polynomial
    -- inclusion; there is no application lemma for the wrapper.
    change Polynomial.toLaurent
        ((pointsMulEquiv N F : Matrix (Fin N) (Fin N) (Polynomial A)) i j) =
      LaurentPolynomial.C
          ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
        LaurentPolynomial.T (w i - w j) at hentry
    have hcoeff := congrArg
      (fun q : LaurentPolynomial A ↦ q.coeff (w i - w j)) hentry
    have hleft :
        (Polynomial.toLaurent
          ((pointsMulEquiv N F : Matrix (Fin N) (Fin N) (Polynomial A)) i j)).coeff
            (w i - w j) = 0 := by
      rw [LaurentPolynomial.coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨n, hn⟩
      change (n : ℤ) = w i - w j at hn
      omega
    have hright :
        (LaurentPolynomial.C
              ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
            LaurentPolynomial.T (w i - w j)).coeff (w i - w j) =
          (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact Finsupp.single_eq_same
    rw [hleft, hright] at hcoeff
    exact hcoeff.symm
  · intro hg
    exact Cocharacter.mem_parabolic_of_eq
      (ofPolyPoint_weightPolynomialExtension w g hg)

private theorem evalZero_weightPolynomialMatrix_apply (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) (i j : Fin N) :
    Polynomial.eval 0 (weightPolynomialMatrix w g i j) =
      if w i = w j then
        (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j
      else 0 := by
  by_cases hij : w i = w j
  · simp [weightPolynomialMatrix, hij]
  · by_cases hji : w j ≤ w i
    · have hlt : w j < w i := lt_of_le_of_ne hji (Ne.symm hij)
      have hpos : 0 < (w i - w j).toNat := by omega
      simp [weightPolynomialMatrix, hji, hij, ne_of_gt hpos]
    · simp [weightPolynomialMatrix, hji, hij]

/-- The dynamic limit for a weight cocharacter keeps an entry exactly when its row and column
have equal weight. -/
theorem pointsMulEquiv_limit_weightCocharacter_apply (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A))
    (hg : g ∈ Cocharacter.parabolic A (weightCocharacter (R := R) w)) (i j : Fin N) :
    (pointsMulEquiv N
        (Cocharacter.limit A (weightCocharacter (R := R) w) ⟨g, hg⟩) :
      Matrix (Fin N) (Fin N) A) i j =
      if w i = w j then
        (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j
      else 0 := by
  have hblock := (mem_weightCocharacter_parabolic_iff w g).mp hg
  have hext :
      Cocharacter.extend A (weightCocharacter (R := R) w) ⟨g, hg⟩ =
        weightPolynomialExtension (R := R) w g hblock :=
    Cocharacter.extend_unique (ofPolyPoint_weightPolynomialExtension w g hblock)
  rw [Cocharacter.limit_apply, hext, pointsMulEquiv_evalZeroPoint,
    Matrix.GeneralLinearGroup.map_apply, pointsMulEquiv_weightPolynomialExtension]
  exact evalZero_weightPolynomialMatrix_apply w g i j

/-- Membership in the dynamic Levi subgroup for a weight cocharacter means preserving every
weight space: matrix entries between distinct weights vanish. -/
@[simp]
theorem mem_weightCocharacter_levi_iff (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) :
    g ∈ Cocharacter.levi A (weightCocharacter (R := R) w) ↔
      ∀ i j, w i ≠ w j →
        (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j = 0 := by
  constructor
  · intro hg i j hij
    have hgP := Cocharacter.levi_le_parabolic hg
    have hlimit := Cocharacter.limit_of_mem_levi hg
    have hmat := congrArg (pointsMulEquiv (R := R) (A := A) N) hlimit
    have hentry := congrArg
      (fun M : GL (Fin N) A ↦ (M : Matrix (Fin N) (Fin N) A) i j) hmat
    rw [pointsMulEquiv_limit_weightCocharacter_apply w g hgP i j] at hentry
    simp only [hij, ↓reduceIte] at hentry
    exact hentry.symm
  · intro h
    rw [Cocharacter.mem_levi_iff]
    apply (pointsMulEquiv (R := R) (A := LaurentPolynomial A) N).injective
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [pointsMulEquiv_conjugate_weightCocharacter_apply,
      Cocharacter.constPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue,
      Matrix.GeneralLinearGroup.map_apply]
    -- Normalize the scalar-extension map in the constant matrix entry.
    change LaurentPolynomial.C
        ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j) *
          LaurentPolynomial.T (w i - w j) =
      LaurentPolynomial.C
        ((pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j)
    by_cases hij : w i = w j
    · rw [hij, sub_self, LaurentPolynomial.T_zero, mul_one]
    · rw [h i j hij]
      simp

/-- Membership in the dynamic unipotent subgroup for a weight cocharacter means block
triangularity together with identity action on each associated-graded weight space. -/
@[simp]
theorem mem_weightCocharacter_unipotent_iff (w : Fin N → ℤ)
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] A)) :
    g ∈ Cocharacter.unipotent A (weightCocharacter (R := R) w) ↔
      (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A).BlockTriangular
          (OrderDual.toDual ∘ w) ∧
        ∀ i j, w i = w j →
          (pointsMulEquiv N g : Matrix (Fin N) (Fin N) A) i j =
            (1 : Matrix (Fin N) (Fin N) A) i j := by
  constructor
  · intro hg
    obtain ⟨hgP, hlimit⟩ := Cocharacter.mem_unipotent_iff.mp hg
    refine ⟨(mem_weightCocharacter_parabolic_iff w g).mp hgP, fun i j hij ↦ ?_⟩
    have hmat := congrArg (pointsMulEquiv (R := R) (A := A) N) hlimit
    have hentry := congrArg
      (fun M : GL (Fin N) A ↦ (M : Matrix (Fin N) (Fin N) A) i j) hmat
    rw [pointsMulEquiv_limit_weightCocharacter_apply w g hgP i j,
      map_one, Matrix.GeneralLinearGroup.coe_one] at hentry
    simp only [hij, ↓reduceIte] at hentry
    exact hentry
  · rintro ⟨hblock, hgraded⟩
    have hgP : g ∈ Cocharacter.parabolic A (weightCocharacter (R := R) w) :=
      (mem_weightCocharacter_parabolic_iff w g).mpr hblock
    apply Cocharacter.mem_unipotent_iff.mpr
    refine ⟨hgP, ?_⟩
    apply (pointsMulEquiv (R := R) (A := A) N).injective
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [pointsMulEquiv_limit_weightCocharacter_apply w g hgP i j, map_one,
      Matrix.GeneralLinearGroup.coe_one]
    by_cases hij : w i = w j
    · simpa only [hij, ↓reduceIte] using hgraded i j hij
    · have hne : i ≠ j := fun hEq ↦ hij (congrArg w hEq)
      simp [hij, hne]

end Points

end TauCeti.GeneralLinear.Dynamic
