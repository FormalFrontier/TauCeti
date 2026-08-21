/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel

/-!
# The upper-triangular Borel as a dynamic parabolic of `GL₂`

For the cocharacter

```text
lambda(t) = diag(t, 1)
```

of `GL₂`, conjugation sends a matrix `!![a, b; c, d]` to
`!![a, tb; t⁻¹c, d]`. Consequently the conjugate extends from the punctured affine line across
the origin exactly when `c = 0`: the dynamic parabolic `P(lambda)` is the upper-triangular Borel.
For such a matrix the limit at the origin is its diagonal part.

The construction is made on convolution points and then recovered as a bialgebra morphism by
the full faithfulness of the functor of points. The extension over the origin is exhibited by the
polynomial matrix `!![a, Xb; 0, d]`; the converse reads the coefficient of `T⁻¹` in the lower-left
entry. Thus the result holds over every commutative base ring and every commutative value algebra,
including rings with zero divisors.

## Main declarations

* `TauCeti.GeneralLinear.dynamicCocharacter`: the coordinate bialgebra morphism of
  `t ↦ diag(t, 1)`.
* `TauCeti.GeneralLinear.mem_dynamicParabolic_iff`: its dynamic parabolic consists exactly of
  upper-triangular invertible matrices.
* `TauCeti.GeneralLinear.pointsMulEquiv_limit_dynamicCocharacter`: its dynamic limit is the
  diagonal part of an upper-triangular matrix.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This supplies the explicit `GL₂` check for the dynamic-parabolic route in Layer 7, "Structure
theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear

universe u v w

variable {R : Type u} [CommRing R]

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The diagonal unit family `(t, 1)` used by the standard dynamic cocharacter of `GL₂`. -/
def dynamicDiagonalUnits : Aˣ →* (Fin 2 → Aˣ) where
  toFun t i := if i = 0 then t else 1
  map_one' := by
    funext i
    split_ifs <;> rfl
  map_mul' t s := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

/-- The standard dynamic cocharacter `t ↦ diag(t, 1)` on algebra-valued points. -/
noncomputable def dynamicCocharacterPoints :
    WithConv (LaurentPolynomial R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) 2).symm.toMonoidHom.comp <|
    (diagGL (k := A)).comp <|
      (dynamicDiagonalUnits (A := A)).comp
        (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).toMonoidHom

/-- Reading the standard dynamic cocharacter as a matrix gives `diag(t, 1)`. -/
theorem pointsMulEquiv_dynamicCocharacterPoints
    (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    pointsMulEquiv 2 (dynamicCocharacterPoints f) =
      diagGL (dynamicDiagonalUnits (MultiplicativeGroup.pointsMulEquiv f)) := by
  simp [dynamicCocharacterPoints]

variable {B : Type w} [CommRing B] [Algebra R B]

/-- The standard dynamic cocharacter on points is natural in the value algebra. -/
theorem mapValue_dynamicCocharacterPoints (phi : A →ₐ[R] B)
    (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    AlgHom.mapValue phi (dynamicCocharacterPoints f) =
      dynamicCocharacterPoints (AlgHom.mapValue phi f) := by
  apply (pointsMulEquiv (R := R) (A := B) 2).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_dynamicCocharacterPoints,
    pointsMulEquiv_dynamicCocharacterPoints]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, ite_eq_left]
    fin_cases i
    · exact congrArg Units.val
        (MultiplicativeGroup.pointsMulEquiv_mapValue phi f)
    · simp [dynamicDiagonalUnits]
  · simp [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, hij]

end Points

section Coordinate

/-- The natural transformation on points given by `t ↦ diag(t, 1)`. -/
noncomputable def dynamicCocharacterPointsMap :
    HopfAlgebra.pointsFunctor (R := R) (H := LaurentPolynomial R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R 2) where
  app A := GrpCat.ofHom (dynamicCocharacterPoints (R := R) (A := A))
  naturality _ _ phi := by
    ext f
    exact (mapValue_dynamicCocharacterPoints phi.hom f).symm

/-- The coordinate Hopf-algebra morphism of the cocharacter `t ↦ diag(t, 1)`. -/
noncomputable def dynamicCocharacterCoordinateMap :
    coordinateHopfAlgebra R 2 ⟶ _root_.CommHopfAlgCat.of R (LaurentPolynomial R) :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (X := Opposite.op (_root_.CommHopfAlgCat.of R (LaurentPolynomial R)))
    (Y := Opposite.op (coordinateHopfAlgebra R 2))
    (dynamicCocharacterPointsMap.{u, u} (R := R))).unop

/-- Precomposition by the coordinate morphism is the constructed cocharacter on points. -/
theorem mapPointsFunctor_dynamicCocharacterCoordinateMap :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (dynamicCocharacterCoordinateMap (R := R)) :
      HopfAlgebra.pointsFunctor (R := R) (H := LaurentPolynomial R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R 2)) =
      (dynamicCocharacterPointsMap.{u, u} (R := R)) := by
  unfold dynamicCocharacterCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On every value algebra, the coordinate cocharacter induces `t ↦ diag(t, 1)` on points. -/
@[simp]
theorem mapPointsFunctor_dynamicCocharacterCoordinateMap_app
    (A : CommAlgCat.{v} R) (f : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    (CommHopfAlgCat.mapPointsFunctor
      (dynamicCocharacterCoordinateMap (R := R))).app A f =
      dynamicCocharacterPoints f := by
  let K := LaurentPolynomial R
  let p : WithConv (K →ₐ[R] K) :=
    toConv (AlgHom.id R _)
  have hp :
      (CommHopfAlgCat.mapPointsFunctor
        (dynamicCocharacterCoordinateMap (R := R))).app
          (CommAlgCat.of R K) p = dynamicCocharacterPoints p := by
    rw [mapPointsFunctor_dynamicCocharacterCoordinateMap, dynamicCocharacterPointsMap]
    exact GrpCat.ofHom_apply dynamicCocharacterPoints p
  have hfp : AlgHom.mapValue (H := K) f.ofConv p = f := by
    simp only [AlgHom.mapValue_apply, p, AlgHom.comp_id, WithConv.toConv_ofConv]
  have hnat :
      AlgHom.mapValue (H := coordinateHopfAlgebra R 2) f.ofConv
          ((CommHopfAlgCat.mapPointsFunctor
            (dynamicCocharacterCoordinateMap (R := R))).app (CommAlgCat.of R K) p) =
        (CommHopfAlgCat.mapPointsFunctor
          (dynamicCocharacterCoordinateMap (R := R))).app A
            (AlgHom.mapValue (H := K) f.ofConv p) := by
    exact DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain
        (dynamicCocharacterCoordinateMap (R := R)).hom f.ofConv) p
  rw [← hfp, ← hnat, hp, mapValue_dynamicCocharacterPoints]

/-- The bialgebra morphism representing the standard cocharacter `t ↦ diag(t, 1)`. -/
noncomputable def dynamicCocharacter :
    coordinateHopfAlgebra R 2 →ₐc[R] LaurentPolynomial R :=
  (dynamicCocharacterCoordinateMap (R := R)).hom

end Coordinate

section Dynamic

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The abstract cocharacter action agrees with the concrete point map `t ↦ diag(t, 1)`. -/
theorem pointsHom_dynamicCocharacter (t : Aˣ) :
    Cocharacter.pointsHom A (dynamicCocharacter (R := R)) t =
      dynamicCocharacterPoints
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) := by
  rw [Cocharacter.pointsHom_apply]
  -- Expose the component of the recovered natural transformation so its pointwise API applies.
  change (CommHopfAlgCat.mapPointsFunctor
      (dynamicCocharacterCoordinateMap (R := R))).app (CommAlgCat.of R A)
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) = _
  rw [mapPointsFunctor_dynamicCocharacterCoordinateMap_app]

/-- The standard cocharacter sends `t` to the diagonal matrix `diag(t, 1)`. -/
theorem pointsMulEquiv_pointsHom_dynamicCocharacter (t : Aˣ) :
    pointsMulEquiv 2 (Cocharacter.pointsHom A (dynamicCocharacter (R := R)) t) =
      diagGL (dynamicDiagonalUnits t) := by
  rw [pointsHom_dynamicCocharacter, pointsMulEquiv_dynamicCocharacterPoints,
    MulEquiv.apply_symm_apply]

/-- Conjugation by the standard cocharacter has matrix formula
`diag(T, 1) * g * diag(T⁻¹, 1)`. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) =
      diagGL (dynamicDiagonalUnits (Cocharacter.genericUnit A)) *
        Matrix.GeneralLinearGroup.map
          (IsScalarTower.toAlgHom R A (LaurentPolynomial A)).toRingHom
          (pointsMulEquiv 2 g) *
        (diagGL (dynamicDiagonalUnits (Cocharacter.genericUnit A)))⁻¹ := by
  rw [Cocharacter.conjugate_apply, map_mul, map_mul, map_inv,
    Cocharacter.genericPoint_eq_pointsHom,
    pointsMulEquiv_pointsHom_dynamicCocharacter, Cocharacter.constPoint_apply,
    ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

private theorem coe_dynamicDiagonalUnits_genericUnit_inv :
    ((((diagGL (dynamicDiagonalUnits (Cocharacter.genericUnit A)))⁻¹ :
        GL (Fin 2) (LaurentPolynomial A))) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) =
      Matrix.diagonal fun i =>
        ((((dynamicDiagonalUnits (Cocharacter.genericUnit A)) i)⁻¹ :
          (LaurentPolynomial A)ˣ) : LaurentPolynomial A) := by
  rw [← map_inv diagGL, diagGL_coe]
  rfl

private theorem genericUnit_inv_val :
    (((Cocharacter.genericUnit A)⁻¹ : (LaurentPolynomial A)ˣ) : LaurentPolynomial A) =
      LaurentPolynomial.T (-1) := by
  apply (mul_right_inj_of_invertible (LaurentPolynomial.T 1)).mp
  calc
    LaurentPolynomial.T 1 *
          (((Cocharacter.genericUnit A)⁻¹ : (LaurentPolynomial A)ˣ) : LaurentPolynomial A) =
        (Cocharacter.genericUnit A : LaurentPolynomial A) *
          (((Cocharacter.genericUnit A)⁻¹ : (LaurentPolynomial A)ˣ) :
            LaurentPolynomial A) := by rw [Cocharacter.genericUnit_val]
    _ = 1 := Units.val_inv _
    _ = LaurentPolynomial.T 1 * LaurentPolynomial.T (-1) := by
      rw [← LaurentPolynomial.T_add]
      norm_num

/-- Conjugation by `diag(T, 1)` fixes the upper-left matrix entry. -/
-- Not `@[simp]`: `pointsMulEquiv_apply` already simplifies the left-hand side, so `simpNF`
-- rejects entrywise formulas stated through the point equivalence.
theorem pointsMulEquiv_conjugate_dynamicCocharacter_zero_zero
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 0 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 0 0) := by
  rw [pointsMulEquiv_conjugate_dynamicCocharacter]
  rw [Units.val_mul, Units.val_mul]
  rw [coe_dynamicDiagonalUnits_genericUnit_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, dynamicDiagonalUnits,
    Cocharacter.genericUnit_val, genericUnit_inv_val]

/-- Conjugation by `diag(T, 1)` multiplies the upper-right entry by `T`. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_zero_one
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 1 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 0 1) *
        LaurentPolynomial.T 1 := by
  rw [pointsMulEquiv_conjugate_dynamicCocharacter]
  rw [Units.val_mul, Units.val_mul]
  rw [coe_dynamicDiagonalUnits_genericUnit_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, dynamicDiagonalUnits,
    Cocharacter.genericUnit_val, mul_assoc]

/-- Conjugation by `diag(T, 1)` multiplies the lower-left entry by `T⁻¹`. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_one_zero
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 0 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0) *
        LaurentPolynomial.T (-1) := by
  rw [pointsMulEquiv_conjugate_dynamicCocharacter]
  rw [Units.val_mul, Units.val_mul]
  rw [coe_dynamicDiagonalUnits_genericUnit_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, dynamicDiagonalUnits,
    genericUnit_inv_val]

/-- Conjugation by `diag(T, 1)` fixes the lower-right matrix entry. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_one_one
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 1 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 1) := by
  rw [pointsMulEquiv_conjugate_dynamicCocharacter]
  rw [Units.val_mul, Units.val_mul]
  rw [coe_dynamicDiagonalUnits_genericUnit_inv]
  simp [Matrix.mul_apply, Fin.sum_univ_two, dynamicDiagonalUnits]

/-- Applying the inclusion `A[X] → A[T;T⁻¹]` to a general-linear point applies that
inclusion entrywise to its matrix. -/
theorem pointsMulEquiv_ofPolyPoint
    {n : ℕ} (F : WithConv (coordinateHopfAlgebra R n →ₐ[R] Polynomial A)) :
    pointsMulEquiv n (Cocharacter.ofPolyPoint A F) =
      Matrix.GeneralLinearGroup.map
        (Polynomial.toLaurentAlg.restrictScalars R).toRingHom (pointsMulEquiv n F) := by
  rw [Cocharacter.ofPolyPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

/-- Evaluating a polynomial-valued point at zero evaluates every matrix entry at zero. -/
theorem pointsMulEquiv_evalZeroPoint
    {n : ℕ} (F : WithConv (coordinateHopfAlgebra R n →ₐ[R] Polynomial A)) :
    pointsMulEquiv n (Cocharacter.evalZeroPoint A F) =
      Matrix.GeneralLinearGroup.map
        ((Polynomial.aeval (0 : A)).restrictScalars R).toRingHom (pointsMulEquiv n F) := by
  rw [Cocharacter.evalZeroPoint_apply, ← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]

/-- The polynomial matrix `!![a, bX; 0, d]`, regarded as a polynomial-valued `GL₂` point. -/
private noncomputable def dynamicPolynomialExtension (a d : Aˣ) (b : A) :
    WithConv (coordinateHopfAlgebra R 2 →ₐ[R] Polynomial A) :=
  (pointsMulEquiv (R := R) (A := Polynomial A) 2).symm <|
    GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
      (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X)

/-- The matrix of `dynamicPolynomialExtension` is `!![a, bX; 0, d]`. -/
-- Not `@[simp]`: `pointsMulEquiv_apply` already supplies the simp-normal left-hand side.
private theorem pointsMulEquiv_dynamicPolynomialExtension (a d : Aˣ) (b : A) :
    pointsMulEquiv 2 (dynamicPolynomialExtension (R := R) a d b) =
      GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
        (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X) := by
  exact MulEquiv.apply_symm_apply _ _

/-- The polynomial matrix `!![a, bX; 0, d]` extends the conjugate of
`!![a, b; 0, d]` by `diag(T, 1)`. -/
private theorem ofPolyPoint_dynamicPolynomialExtension
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) (a d : Aˣ) (b : A)
    (hmatrix : pointsMulEquiv 2 g = GL2Borel.mk a d b) :
    Cocharacter.ofPolyPoint A (dynamicPolynomialExtension (R := R) a d b) =
      Cocharacter.conjugate A (dynamicCocharacter (R := R)) g := by
  apply (pointsMulEquiv (R := R) (A := LaurentPolynomial A) 2).injective
  rw [pointsMulEquiv_ofPolyPoint, pointsMulEquiv_dynamicPolynomialExtension]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  -- The four `change`s remove the entrywise `GL.map` wrapper and normalize the `Fin 2` indices.
  · change Polynomial.toLaurent
        (((GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
          (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X) :
            GL (Fin 2) (Polynomial A)) : Matrix (Fin 2) (Fin 2) (Polynomial A)) 0 0) =
      (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 0
    rw [pointsMulEquiv_conjugate_dynamicCocharacter_zero_zero, hmatrix]
    simp [GL2Borel.coe_mk]
  · change Polynomial.toLaurent
        (((GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
          (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X) :
            GL (Fin 2) (Polynomial A)) : Matrix (Fin 2) (Fin 2) (Polynomial A)) 0 1) =
      (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 1
    rw [pointsMulEquiv_conjugate_dynamicCocharacter_zero_one, hmatrix]
    simp [GL2Borel.coe_mk]
  · change Polynomial.toLaurent
        (((GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
          (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X) :
            GL (Fin 2) (Polynomial A)) : Matrix (Fin 2) (Fin 2) (Polynomial A)) 1 0) =
      (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 0
    rw [pointsMulEquiv_conjugate_dynamicCocharacter_one_zero, hmatrix]
    simp [GL2Borel.coe_mk]
  · change Polynomial.toLaurent
        (((GL2Borel.mk (Units.map Polynomial.C.toMonoidHom a)
          (Units.map Polynomial.C.toMonoidHom d) (Polynomial.C b * Polynomial.X) :
            GL (Fin 2) (Polynomial A)) : Matrix (Fin 2) (Fin 2) (Polynomial A)) 1 1) =
      (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
        Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 1
    rw [pointsMulEquiv_conjugate_dynamicCocharacter_one_one, hmatrix]
    simp [GL2Borel.coe_mk]

/-- Evaluating `!![a, bX; 0, d]` at zero gives its diagonal part. -/
private theorem pointsMulEquiv_evalZero_dynamicPolynomialExtension (a d : Aˣ) (b : A) :
    pointsMulEquiv 2
        (Cocharacter.evalZeroPoint A (dynamicPolynomialExtension (R := R) a d b)) =
      GL2Borel.mk a d 0 := by
  rw [pointsMulEquiv_evalZeroPoint, pointsMulEquiv_dynamicPolynomialExtension]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp [GL2Borel.coe_mk]

/-- Membership in the dynamic parabolic for `t ↦ diag(t, 1)` is exactly upper triangularity. -/
@[simp]
theorem mem_dynamicParabolic_iff
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.parabolic A (dynamicCocharacter (R := R)) ↔
      pointsMulEquiv 2 g ∈ GL2Borel A := by
  constructor
  · rw [Cocharacter.mem_parabolic_iff]
    rintro ⟨F, hF⟩
    apply GL2Borel.mem_iff.mpr
    have hmat := congrArg (pointsMulEquiv (R := R) (A := LaurentPolynomial A) 2) hF
    have hentry := congrArg
      (fun M : GL (Fin 2) (LaurentPolynomial A) =>
        (M : Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 0) hmat
    rw [pointsMulEquiv_ofPolyPoint,
      pointsMulEquiv_conjugate_dynamicCocharacter_one_zero] at hentry
    simp only [Matrix.GeneralLinearGroup.map_apply] at hentry
    -- Expose the underlying polynomial inclusion in the lower-left matrix entry.
    change Polynomial.toLaurent
        ((pointsMulEquiv 2 F : Matrix (Fin 2) (Fin 2) (Polynomial A)) 1 0) =
      LaurentPolynomial.C
          ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0) *
        LaurentPolynomial.T (-1) at hentry
    have hcoeff := congrArg
      (fun q : LaurentPolynomial A => q.coeff (-1)) hentry
    have hleft :
        (Polynomial.toLaurent
          ((pointsMulEquiv 2 F : Matrix (Fin 2) (Fin 2) (Polynomial A)) 1 0)).coeff (-1) = 0 := by
      rw [LaurentPolynomial.coeff_toLaurent]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨n, hn⟩
      -- The support map is the natural-number inclusion into the integers.
      change (n : ℤ) = -1 at hn
      omega
    have hright :
        (LaurentPolynomial.C
              ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0) *
            LaurentPolynomial.T (-1)).coeff (-1) =
          (pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0 := by
      rw [← LaurentPolynomial.single_eq_C_mul_T]
      exact Finsupp.single_eq_same
    rw [hleft, hright] at hcoeff
    exact hcoeff.symm
  · intro hg
    obtain ⟨a, d, b, hmatrix⟩ := GL2Borel.mem_iff_exists_mk.mp hg
    exact Cocharacter.mem_parabolic_of_eq
      (ofPolyPoint_dynamicPolynomialExtension g a d b hmatrix)

/-- The dynamic limit of an upper-triangular matrix is its diagonal part. -/
theorem pointsMulEquiv_limit_dynamicCocharacter
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A))
    (hg : g ∈ Cocharacter.parabolic A (dynamicCocharacter (R := R))) :
    pointsMulEquiv 2
        (Cocharacter.limit A (dynamicCocharacter (R := R)) ⟨g, hg⟩) =
      ((GL2Borel.torusHom
          (GL2Borel.diag
            (⟨pointsMulEquiv 2 g, (mem_dynamicParabolic_iff g).mp hg⟩ : GL2Borel A)) :
        GL2Borel A) : GL (Fin 2) A) := by
  have hb : pointsMulEquiv 2 g ∈ GL2Borel A := (mem_dynamicParabolic_iff g).mp hg
  obtain ⟨a, d, b, hmatrix⟩ := GL2Borel.mem_iff_exists_mk.mp hb
  have hext :
      Cocharacter.extend A (dynamicCocharacter (R := R)) ⟨g, hg⟩ =
        dynamicPolynomialExtension (R := R) a d b :=
    Cocharacter.extend_unique (ofPolyPoint_dynamicPolynomialExtension g a d b hmatrix)
  have hdiag :
      GL2Borel.diag (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) = (a, d) := by
    have hB : (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) =
        ⟨GL2Borel.mk a d b, GL2Borel.mk_mem a d b⟩ := Subtype.ext hmatrix
    rw [hB, GL2Borel.diag_mk]
  rw [Cocharacter.limit_apply, hext, pointsMulEquiv_evalZero_dynamicPolynomialExtension,
    GL2Borel.coe_torusHom, hdiag]

/-- As subgroups of convolution points, the dynamic parabolic for `t ↦ diag(t, 1)` is the
preimage of the upper-triangular Borel under the general-linear point equivalence. -/
theorem dynamicParabolic_eq_borelComap :
    Cocharacter.parabolic A (dynamicCocharacter (R := R)) =
      (GL2Borel A).comap (pointsMulEquiv (R := R) (A := A) 2).toMonoidHom := by
  ext g
  exact mem_dynamicParabolic_iff g

end Dynamic

end TauCeti.GeneralLinear
