/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weights

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

The cocharacter is the rank-one specialization of the general weight-torus construction. The
extension over the origin is exhibited by the polynomial matrix `!![a, Xb; 0, d]`; the converse
reads the coefficient of `T⁻¹` in the lower-left entry. Thus the result holds over every
commutative base ring and every commutative value algebra, including rings with zero divisors.

## Main declarations

* `TauCeti.GeneralLinear.Dynamic.GL2.dynamicCocharacter`: the coordinate bialgebra morphism of
  `t ↦ diag(t, 1)`.
* `TauCeti.GeneralLinear.Dynamic.GL2.mem_dynamicParabolic_iff`: its dynamic parabolic consists
  exactly of upper-triangular invertible matrices.
* `TauCeti.GeneralLinear.Dynamic.GL2.pointsMulEquiv_limit_dynamicCocharacter`: its dynamic limit is
  the diagonal part of an upper-triangular matrix.

## References

* G. R. Kempf, *Instability in invariant theory*, Annals of Mathematics 108 (1978), §2.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.

This supplies the explicit `GL₂` check for the dynamic-parabolic route in Layer 7, "Structure
theory", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.GeneralLinear.Dynamic

universe u v w

variable {R : Type u} [CommRing R]

namespace GL2

/-- The diagonal unit family `(t, 1)` used by the standard dynamic cocharacter of `GL₂`. -/
def dynamicDiagonalUnits {A : Type v} [Monoid A] : Aˣ →* (Fin 2 → Aˣ) where
  toFun t i := if i = 0 then t else 1
  map_one' := by
    funext i
    split_ifs <;> rfl
  map_mul' t s := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

section Points

variable {A : Type v} [CommRing A] [Algebra R A]

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

end Points

section Coordinate

/-- The rank-one weights `(1, 0)` defining the standard dynamic cocharacter of `GL₂`. -/
private def dynamicWeights : Fin 2 → ℤ :=
  fun i => if i = 0 then 1 else 0

/-- The bialgebra morphism representing the standard cocharacter `t ↦ diag(t, 1)`. -/
noncomputable def dynamicCocharacter :
    coordinateHopfAlgebra R 2 →ₐc[R] LaurentPolynomial R :=
  weightCocharacter (R := R) dynamicWeights

end Coordinate

section Dynamic

variable {A : Type v} [CommRing A] [Algebra R A]

/-- The abstract cocharacter action agrees with the concrete point map `t ↦ diag(t, 1)`. -/
theorem pointsHom_dynamicCocharacter (t : Aˣ) :
    Cocharacter.pointsHom A (dynamicCocharacter (R := R)) t =
      dynamicCocharacterPoints
        ((MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).symm t) := by
  rw [dynamicCocharacter, pointsHom_weightCocharacter]
  apply (pointsMulEquiv (R := R) (A := A) 2).injective
  rw [pointsMulEquiv_weightCocharacterPoints, pointsMulEquiv_dynamicCocharacterPoints]
  congr 1
  funext i
  fin_cases i <;> simp [dynamicWeights, dynamicDiagonalUnits]

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
  rw [dynamicCocharacter, pointsMulEquiv_conjugate_weightCocharacter]
  congr 2 <;> apply congrArg diagGL <;> funext i <;>
    fin_cases i <;> simp [dynamicWeights, dynamicDiagonalUnits]

/-- Conjugation by `diag(T, 1)` fixes the upper-left matrix entry. -/
-- Not `@[simp]`: `pointsMulEquiv_apply` already simplifies the left-hand side, so `simpNF`
-- rejects entrywise formulas stated through the point equivalence.
theorem pointsMulEquiv_conjugate_dynamicCocharacter_zero_zero
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 0 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 0 0) := by
  rw [dynamicCocharacter, pointsMulEquiv_conjugate_weightCocharacter_apply]
  simp [dynamicWeights]

/-- Conjugation by `diag(T, 1)` multiplies the upper-right entry by `T`. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_zero_one
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 0 1 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 0 1) *
        LaurentPolynomial.T 1 := by
  rw [dynamicCocharacter, pointsMulEquiv_conjugate_weightCocharacter_apply]
  simp [dynamicWeights]

/-- Conjugation by `diag(T, 1)` multiplies the lower-left entry by `T⁻¹`. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_one_zero
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 0 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0) *
        LaurentPolynomial.T (-1) := by
  rw [dynamicCocharacter, pointsMulEquiv_conjugate_weightCocharacter_apply]
  simp [dynamicWeights]

/-- Conjugation by `diag(T, 1)` fixes the lower-right matrix entry. -/
theorem pointsMulEquiv_conjugate_dynamicCocharacter_one_one
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    (pointsMulEquiv 2 (Cocharacter.conjugate A (dynamicCocharacter (R := R)) g) :
      Matrix (Fin 2) (Fin 2) (LaurentPolynomial A)) 1 1 =
      LaurentPolynomial.C ((pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 1) := by
  rw [dynamicCocharacter, pointsMulEquiv_conjugate_weightCocharacter_apply]
  simp [dynamicWeights]

/-- Membership in the dynamic parabolic for `t ↦ diag(t, 1)` is exactly upper triangularity. -/
@[simp]
theorem mem_dynamicParabolic_iff
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.parabolic A (dynamicCocharacter (R := R)) ↔
      pointsMulEquiv 2 g ∈ GL2Borel A := by
  rw [dynamicCocharacter, mem_parabolic_weightCocharacter_iff]
  constructor
  · intro h
    apply GL2Borel.mem_iff.mpr
    exact @h 1 0 (by
      change dynamicWeights 1 < dynamicWeights 0
      simp [dynamicWeights])
  · intro h i j hij
    have hzero : (pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
      exact GL2Borel.mem_iff.mp h
    change dynamicWeights i < dynamicWeights j at hij
    fin_cases i <;> fin_cases j
    · simp [dynamicWeights] at hij
    · simp [dynamicWeights] at hij
    · exact hzero
    · simp [dynamicWeights] at hij

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
  unfold dynamicCocharacter at hg ⊢
  have hb : pointsMulEquiv 2 g ∈ GL2Borel A := (mem_dynamicParabolic_iff g).mp hg
  obtain ⟨a, d, b, hmatrix⟩ := GL2Borel.mem_iff_exists_mk.mp hb
  have hdiag :
      GL2Borel.diag (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) = (a, d) := by
    have hB : (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) =
        ⟨GL2Borel.mk a d b, GL2Borel.mk_mem a d b⟩ := Subtype.ext hmatrix
    rw [hB, GL2Borel.diag_mk]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [pointsMulEquiv_limit_weightCocharacter_apply dynamicWeights g hg i j]
  rw [GL2Borel.coe_torusHom, hdiag]
  fin_cases i <;> fin_cases j <;>
    simp [dynamicWeights, hmatrix, GL2Borel.coe_mk]

/-- As subgroups of convolution points, the dynamic parabolic for `t ↦ diag(t, 1)` is the
preimage of the upper-triangular Borel under the general-linear point equivalence. -/
theorem dynamicParabolic_eq_borelComap :
    Cocharacter.parabolic A (dynamicCocharacter (R := R)) =
      (GL2Borel A).comap (pointsMulEquiv (R := R) (A := A) 2).toMonoidHom := by
  ext g
  exact mem_dynamicParabolic_iff g

end Dynamic

end GL2

end TauCeti.GeneralLinear.Dynamic
