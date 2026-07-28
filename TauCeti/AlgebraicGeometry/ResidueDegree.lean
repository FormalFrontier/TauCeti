/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Residue degrees of scheme morphisms

This file develops the elementary functorial API for Mathlib's
`AlgebraicGeometry.Scheme.Hom.residueDegree`. For a scheme morphism `f : X ⟶ Y` and a point
`x : X`, this is the degree `[κ(x) : κ(f(x))]`, with value zero when the field extension is
infinite.

The main result is the tower law `residueDegree_comp`. It identifies the residue degree of a
composite with the product of the two successive residue degrees. We also characterize when a
residue degree is positive and when it is one. These facts supply the residue-field weights used
in the degree and pushforward parts of Layer A of the Jacobian challenge roadmap.

The construction follows the residue-degree convention for pushforward of cycles in the
[Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4). The proofs reuse
Mathlib's residue-field maps and the field-extension tower law `Module.finrank_mul_finrank`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- The residue degree of a composite is the product of the successive residue degrees:
`[κ(x) : κ(g(f(x)))] = [κ(f(x)) : κ(g(f(x)))] [κ(x) : κ(f(x))]`. -/
@[simp]
theorem residueDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  letI : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  letI : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)
  rw [Scheme.Hom.residueDegree]
  exact (Module.finrank_mul_finrank (Z.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)).symm

/-- A residue degree is positive exactly when the associated residue-field extension is finite. -/
theorem residueDegree_pos_iff (f : X ⟶ Y) (x : X) :
    0 < f.residueDegree x ↔
      (f.residueFieldMap x).hom.Finite := by
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [Scheme.Hom.residueDegree, RingHom.Finite]
  constructor
  · exact Module.finite_of_finrank_pos
  · intro h
    letI : Module.Finite (Y.residueField (f x)) (X.residueField x) := h
    exact Module.finrank_pos

/-- A residue degree is nonzero exactly when the associated residue-field extension is finite. -/
theorem residueDegree_ne_zero_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔
      (f.residueFieldMap x).hom.Finite := by
  rw [← residueDegree_pos_iff f x, Nat.pos_iff_ne_zero]

/-- A residue-field map is bijective exactly when its residue degree is one. -/
theorem residueDegree_eq_one_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x = 1 ↔ Function.Bijective (f.residueFieldMap x) := by
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [Scheme.Hom.residueDegree, Algebra.finrank_eq_one_iff_bijective_algebraMap,
    RingHom.algebraMap_toAlgebra]

/-- An isomorphism of schemes has residue degree one at every point. -/
@[simp]
theorem residueDegree_eq_one_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) :
    f.residueDegree x = 1 :=
  (residueDegree_eq_one_iff f x).mpr (ConcreteCategory.bijective_of_isIso _)

end AlgebraicGeometry

end TauCeti
