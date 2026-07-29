/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.ResidueDegree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic

/-!
# Relative degrees of scheme-theoretic Weil divisors

This file specializes `WeilDivisor.weightedDegree` to the residue-degree weights associated to a
scheme morphism. For a curve over a field, applied to its structure morphism, this is the divisor
degree `Σ_x [κ(x) : k] · ord_x`.

The composition formula records how these weights change through successive scheme morphisms.
This supplies the residue-field-weighted divisor degree required in Layer A of the Jacobian
challenge roadmap.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X Y Z : Scheme.{u}}

noncomputable section

/-- The degree of a scheme-theoretic Weil divisor weighted by the residue degrees of `f`. -/
def relativeDegree (f : X ⟶ Y) : SchemeWeilDivisor X →+ ℤ :=
  WeilDivisor.weightedDegree fun x : CodimensionOnePoint X ↦ (f.residueDegree x : ℤ)

/-- The relative degree is the finite sum of coefficients times residue degrees. -/
lemma relativeDegree_apply (f : X ⟶ Y) (D : SchemeWeilDivisor X) :
    relativeDegree f D = D.sum fun x n ↦ n * (f.residueDegree x : ℤ) := by
  rw [relativeDegree, WeilDivisor.weightedDegree_apply]

/-- A prime divisor has relative degree equal to the residue degree of its generic point. -/
@[simp]
lemma relativeDegree_ofPoint (f : X ⟶ Y) (x : CodimensionOnePoint X) :
    relativeDegree f (WeilDivisor.ofPoint x) = (f.residueDegree x : ℤ) := by
  simp [relativeDegree]

/-- Relative degree along a composite uses the product of the successive residue degrees. -/
@[simp]
lemma relativeDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (D : SchemeWeilDivisor X) :
    relativeDegree (f ≫ g) D =
      WeilDivisor.weightedDegree
        (fun x : CodimensionOnePoint X ↦
          (g.residueDegree (f x) : ℤ) * f.residueDegree x) D := by
  simp only [relativeDegree, residueDegree_comp, Nat.cast_mul]

/-- Along an isomorphism, relative degree is the ordinary unweighted degree. -/
@[simp]
lemma relativeDegree_eq_degree_of_isIso (f : X ⟶ Y) [IsIso f]
    (D : SchemeWeilDivisor X) :
    relativeDegree f D = WeilDivisor.degree D := by
  rw [relativeDegree]
  simpa only [residueDegree_eq_one_of_isIso, Nat.cast_one] using
    WeilDivisor.weightedDegree_one_eq_degree D

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
