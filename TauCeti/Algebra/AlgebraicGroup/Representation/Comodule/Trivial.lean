/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Trivial point representations

This file synchronizes the trivial operations across the fixed-object correspondence between
point representations of an affine group and comodules over its commutative Hopf algebra.

Every module has a trivial point representation, in which every point acts by the identity on
scalar extension. This construction agrees with the point representation induced by the trivial
comodule. No finiteness, freeness, projectivity, flatness, or nontriviality hypothesis is used.

## Main declarations

* `HopfAlgebra.PointRepresentation.trivial`: the identity action on scalar extensions of an
  arbitrary module.
* `HopfAlgebra.PointRepresentation.ofComodule_trivial` and
  `HopfAlgebra.PointRepresentation.toComodule_trivial`: compatibility with the trivial
  comodule in both directions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a), Remark 4.1.
* J. S. Milne, *Reductive Groups*, §§5.1--5.4.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V : Type w} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

namespace PointRepresentation

/-- The trivial point representation on an arbitrary module. Every point acts by the identity
linear automorphism after scalar extension. -/
noncomputable def trivial : PointRepresentation (R := R) (H := H) (V := V) :=
  ofComodule (Comodule.trivial (R := R) (C := H) (M := V))

/-- Every point acts as the identity in the trivial point representation. -/
@[simp]
theorem trivial_action (A : CommAlgCat.{max u v w} R) (x : points (H := H) A) :
    (trivial (H := H) (V := V)).action A x = 1 := by
  apply Units.ext
  rw [trivial, ofComodule_action_val_eq_endOfPoint]
  exact Comodule.endOfPoint_trivial x.ofConv

/-- The point representation induced by the trivial comodule is the trivial point
representation. -/
@[simp]
theorem ofComodule_trivial :
    ofComodule (Comodule.trivial (R := R) (C := H) (M := V)) =
      trivial (H := H) (V := V) := by
  rfl

/-- Recovering the comodule of the trivial point representation gives the trivial comodule. -/
@[simp]
theorem toComodule_trivial :
    toComodule (trivial (H := H) (V := V)) =
      Comodule.trivial (R := R) (C := H) (M := V) := by
  rw [trivial, toComodule_ofComodule]

end PointRepresentation

end HopfAlgebra

end TauCeti
