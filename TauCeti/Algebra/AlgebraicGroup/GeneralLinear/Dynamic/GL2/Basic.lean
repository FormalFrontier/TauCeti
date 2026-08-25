/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Borel
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Basic

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

The file specializes `TauCeti.GeneralLinear.weightCocharacter` at the weights `(1, 0)`. Thus the
result holds over every commutative base ring and every commutative value algebra, including rings
with zero divisors.

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

section Coordinate

/-- The bialgebra morphism representing the standard cocharacter `t ↦ diag(t, 1)`. -/
noncomputable def dynamicCocharacter :
    coordinateHopfAlgebra R 2 →ₐc[R] LaurentPolynomial R :=
  weightCocharacter (R := R) Borel.weights

/-- The standard dynamic cocharacter is the weight cocharacter for weights `(1, 0)`. -/
theorem dynamicCocharacter_eq_weightCocharacter :
    dynamicCocharacter (R := R) = weightCocharacter (R := R) Borel.weights := by
  rfl

end Coordinate

section Dynamic

variable {A : Type v} [CommRing A] [Algebra R A]

/-- Membership in the dynamic parabolic for `t ↦ diag(t, 1)` is exactly upper triangularity. -/
@[simp]
theorem mem_dynamicParabolic_iff
    (g : WithConv (coordinateHopfAlgebra R 2 →ₐ[R] A)) :
    g ∈ Cocharacter.parabolic A (dynamicCocharacter (R := R)) ↔
      pointsMulEquiv 2 g ∈ GL2Borel A := by
  rw [dynamicCocharacter_eq_weightCocharacter, mem_parabolic_weightCocharacter_iff]
  simp only [Matrix.BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual]
  constructor
  · intro h
    apply GL2Borel.mem_iff.mpr
    exact h (i := 1) (j := 0) (by simp)
  · intro h i j hij
    have hzero : (pointsMulEquiv 2 g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
      exact GL2Borel.mem_iff.mp h
    fin_cases i <;> fin_cases j
    · simp at hij
    · simp at hij
    · exact hzero
    · simp at hij

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
  have hdiag :
      GL2Borel.diag (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) = (a, d) := by
    have hB : (⟨pointsMulEquiv 2 g, hb⟩ : GL2Borel A) =
        ⟨GL2Borel.mk a d b, GL2Borel.mk_mem a d b⟩ := Subtype.ext hmatrix
    rw [hB, GL2Borel.diag_mk]
  have hnormalized : ∀ hg' : g ∈ Cocharacter.parabolic A
      (weightCocharacter (R := R) Borel.weights),
      pointsMulEquiv 2
          (Cocharacter.limit A (weightCocharacter (R := R) Borel.weights) ⟨g, hg'⟩) =
        ((GL2Borel.torusHom
            (GL2Borel.diag ⟨pointsMulEquiv 2 g, hb⟩) : GL2Borel A) : GL (Fin 2) A) := by
    intro hg'
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [pointsMulEquiv_limit_weightCocharacter_apply Borel.weights g hg' i j]
    rw [GL2Borel.coe_torusHom, hdiag]
    fin_cases i <;> fin_cases j <;>
      simp [hmatrix, GL2Borel.coe_mk]
  have hdynamic : ∀ hg' : g ∈ Cocharacter.parabolic A
      (dynamicCocharacter (R := R)),
      pointsMulEquiv 2 (Cocharacter.limit A (dynamicCocharacter (R := R)) ⟨g, hg'⟩) =
        ((GL2Borel.torusHom
            (GL2Borel.diag ⟨pointsMulEquiv 2 g, hb⟩) : GL2Borel A) : GL (Fin 2) A) := by
    rw [dynamicCocharacter_eq_weightCocharacter]
    exact hnormalized
  exact hdynamic hg

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
