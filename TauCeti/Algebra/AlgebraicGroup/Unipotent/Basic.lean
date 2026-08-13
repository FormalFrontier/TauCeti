/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat

/-!
# Smooth unipotent affine groups

A smooth finite-type affine group over a field is unipotent when every point over an algebraic
closure is a unipotent element. On coordinate Hopf algebras, a geometric point is an algebra map
`H →ₐ[k] AlgebraicClosure k`, and its action on every finite-dimensional comodule supplies the
representation-theoretic test for unipotence. Smoothness is included explicitly because geometric
points alone do not detect infinitesimal structure in nonreduced group schemes.

This file packages that definition as an object property on finite-type commutative Hopf
algebras. The equivalent nilpotence and Jordan-factor characterizations make the property usable
without unfolding it.

This pointwise criterion is not offered as a definition for nonreduced group schemes: for example,
both `αₚ` and `μₚ` have only the identity as an algebraic-closure-valued point in characteristic
`p`, although only `αₚ` is unipotent scheme-theoretically. A future scheme-theoretic definition
must instead detect infinitesimal points.

## Main declarations

* `TauCeti.smoothUnipotentCommHopfAlgProperty`: the geometric unipotence property for smooth
  finite-type commutative Hopf algebras over a field.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_iff_forall_isNilpotent`: the criterion that every
  geometric point acts with nilpotent difference from the identity in every finite comodule.
* `TauCeti.smoothUnipotentCommHopfAlgProperty_iff_unipotentPart_eq_self`: the characterization by
  pointwise Jordan decomposition.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This supplies the smooth case of the geometric definition required by Layer 5, "Unipotent
groups", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

/-- The object property selecting smooth finite-type affine groups whose every geometric point is
unipotent.

The point predicate tests the action on every finitely generated comodule, which over a field is
the finite-dimensional representation-theoretic definition. The smoothness condition ensures that
the algebraic-closure-valued points detect the group scheme. -/
def smoothUnipotentCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ Algebra.Smooth k H ∧
    ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k), HopfAlgebra.IsUnipotentPoint g

/-- Membership in the smooth unipotent property means smoothness together with every
algebraic-closure-valued point acting unipotently in every finite-dimensional representation. -/
@[simp]
theorem smoothUnipotentCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.IsUnipotentPoint g :=
  Iff.rfl

/-- A smooth finite-type affine group is unipotent exactly when every geometric point acts on
every finite-dimensional comodule with nilpotent difference from the identity. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_forall_isNilpotent
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
          (M : FGComoduleCat.{u, u, u} k H),
            _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine and_congr_right fun _ ↦ ?_
  apply forall_congr'
  exact HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one

/-- A smooth finite-type affine group is unipotent exactly when the unipotent part of every
geometric point is the point itself. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_unipotentPart_eq_self
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = g := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h g
    exact HopfAlgebra.Point.unipotentPart_eq_self k H (AlgebraicClosure k) (h g)
  · intro h g
    rw [HopfAlgebra.isUnipotentPoint_def]
    intro M
    rw [← h g]
    exact HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart
      k H (AlgebraicClosure k) g M

/-- A smooth finite-type affine group is unipotent exactly when the semisimple part of every
geometric point is the identity. -/
theorem smoothUnipotentCommHopfAlgProperty_iff_semisimplePart_eq_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    smoothUnipotentCommHopfAlgProperty k H ↔
      Algebra.Smooth k H ∧
        ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
          HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = 1 := by
  rw [smoothUnipotentCommHopfAlgProperty_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h g
    exact HopfAlgebra.Point.semisimplePart_eq_one_of_isUnipotent
      k H (AlgebraicClosure k) (h g)
  · intro h g
    rw [HopfAlgebra.isUnipotentPoint_def]
    intro M
    have hg : g = HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g := by
      calc
        g = HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g *
            HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g :=
          (HopfAlgebra.Point.semisimplePart_mul_unipotentPart
            k H (AlgebraicClosure k) g).symm
        _ = 1 * HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g := by
          rw [h g]
        _ = HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g := one_mul _
    rw [hg]
    exact HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart
      k H (AlgebraicClosure k) g M

/-- The category of smooth finite-type unipotent coordinate Hopf algebras over a field. -/
abbrev SmoothUnipotentCommHopfAlgCat (k : Type u) [Field k] :=
  (smoothUnipotentCommHopfAlgProperty k).FullSubcategory

end TauCeti
