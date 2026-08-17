/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive

/-!
# Linearly reductive commutative Hopf algebras

An affine group over a field is linearly reductive when every finite-dimensional rational
representation is completely reducible. This file packages the existing comodule formulation as
an isomorphism-invariant object property on commutative Hopf algebras. It also records that the
coordinate Hopf algebra of every finite-type diagonalizable group has the property.

The property is deliberately separate from smoothness, connectedness, and finite type. In
positive characteristic a torus is linearly reductive, while a general reductive group need not
be. The comparison with geometric reductivity therefore requires characteristic hypotheses and
belongs later in the theory.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty`: linear reductivity as an object property.
* `TauCeti.LinearlyReductiveCommHopfAlgCat`: the corresponding full subcategory.
* `TauCeti.DiagonalizableGroup.linearlyReductiveCommHopfAlgProperty_coordinateRing`: every
  diagonalizable coordinate Hopf algebra is linearly reductive.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 3.2.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.

This is the complete-reducibility side of Layer 6, "Reductive and semisimple groups", in the
ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- The object property selecting commutative Hopf algebras for which every finite-dimensional
comodule is completely reducible. On coordinate rings, this is linear reductivity of the
represented affine group. -/
def linearlyReductiveCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ Coalgebra.IsLinearlyReductive.{u, v, w} k H

/-- Membership in the linearly reductive commutative-Hopf-algebra property means that every
finite-dimensional comodule is completely reducible. -/
@[simp]
theorem linearlyReductiveCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : CommHopfAlgCat.{v} k) :
    linearlyReductiveCommHopfAlgProperty.{u, v, w} k H ↔
      Coalgebra.IsLinearlyReductive.{u, v, w} k H :=
  Iff.rfl

/-- Linear reductivity is invariant under isomorphism of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (linearlyReductiveCommHopfAlgProperty.{u, v, w} k).IsClosedUnderIsomorphisms where
  of_iso e hH :=
    (Coalgebra.isLinearlyReductive_iff_of_coalgEquiv
      k (CommHopfAlgCat.ofIso e).toCoalgEquiv).mp hH

/-- The category of linearly reductive commutative Hopf algebras over a field. -/
abbrev LinearlyReductiveCommHopfAlgCat (k : Type u) [Field k] :=
  (linearlyReductiveCommHopfAlgProperty.{u, v, w} k).FullSubcategory

namespace DiagonalizableGroup

/-- The coordinate Hopf algebra of a finite-type diagonalizable group is linearly reductive.
Equivalently, every finite-dimensional representation of `D(G)` splits as a direct sum of
weight spaces. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateRing
    (k : Type u) [Field k] (G : FGCommGrpCat.{v}) :
    linearlyReductiveCommHopfAlgProperty.{u, max u v, w} k (coordinateRing k G).obj :=
  Coalgebra.isLinearlyReductive_monoidAlgebra k G

end DiagonalizableGroup

end TauCeti
