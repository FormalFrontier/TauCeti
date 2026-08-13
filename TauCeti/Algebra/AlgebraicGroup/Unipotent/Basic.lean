/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.ReducedPoints
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition

/-!
# Unipotent affine groups

A finite-type affine group over a field is unipotent when every point over an algebraic closure
is a unipotent element. On coordinate Hopf algebras, a geometric point is an algebra map
`H →ₐ[k] AlgebraicClosure k`, and its action on every finite-dimensional comodule supplies the
representation-theoretic test for unipotence.

This file packages that definition as an object property on finite-type commutative Hopf
algebras. The equivalent nilpotence and Jordan-factor characterizations make the property usable
without unfolding it.

The definition deliberately does not assume smoothness or reducedness. In particular, the
nonreduced Frobenius kernel `αₚ` is unipotent: its algebraic-closure-valued points are all the
identity even though its coordinate ring is nonreduced.

## Main declarations

* `TauCeti.unipotentCommHopfAlgProperty`: the geometric unipotence property for finite-type
  commutative Hopf algebras over a field.
* `TauCeti.unipotentCommHopfAlgProperty_iff_forall_isNilpotent`: the criterion that every
  geometric point acts with nilpotent difference from the identity in every finite comodule.
* `TauCeti.unipotentCommHopfAlgProperty_iff_unipotentPart_eq_self`: the characterization by
  pointwise Jordan decomposition.
* `TauCeti.AlphaP.unipotent_coordinateRing`: the nonreduced group scheme `αₚ` is unipotent.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.

This is the group-level geometric definition required by Layer 5, "Unipotent groups", of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

/-- The object property selecting finite-type affine groups whose every geometric point is
unipotent.

The point predicate tests the action on every finitely generated comodule, which over a field is
the finite-dimensional representation-theoretic definition. Taking values in
`AlgebraicClosure k` makes the resulting group property geometric. -/
def unipotentCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
    HopfAlgebra.IsUnipotentPoint g

/-- Membership in the unipotent property means that every algebraic-closure-valued point acts
unipotently in every finite-dimensional representation. -/
@[simp]
theorem unipotentCommHopfAlgProperty_iff (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.IsUnipotentPoint g :=
  Iff.rfl

/-- A finite-type affine group is unipotent exactly when every geometric point acts on every
finite-dimensional comodule with nilpotent difference from the identity. -/
theorem unipotentCommHopfAlgProperty_iff_forall_isNilpotent
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentCommHopfAlgProperty k H ↔
      ∀ (g : WithConv (H →ₐ[k] AlgebraicClosure k))
        (M : FGComoduleCat.{u, u, u} k H),
          _root_.IsNilpotent (Comodule.endOfPoint M g.ofConv - 1) := by
  rw [unipotentCommHopfAlgProperty_iff]
  apply forall_congr'
  exact HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one

/-- A finite-type affine group is unipotent exactly when the unipotent part of every geometric
point is the point itself. -/
theorem unipotentCommHopfAlgProperty_iff_unipotentPart_eq_self
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.unipotentPart k H (AlgebraicClosure k) g = g := by
  rw [unipotentCommHopfAlgProperty_iff]
  constructor
  · intro h g
    exact HopfAlgebra.Point.unipotentPart_eq_self k H (AlgebraicClosure k) (h g)
  · intro h g
    rw [HopfAlgebra.isUnipotentPoint_def]
    intro M
    rw [← h g]
    exact HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart
      k H (AlgebraicClosure k) g M

/-- A finite-type affine group is unipotent exactly when the semisimple part of every geometric
point is the identity. -/
theorem unipotentCommHopfAlgProperty_iff_semisimplePart_eq_one
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentCommHopfAlgProperty k H ↔
      ∀ g : WithConv (H →ₐ[k] AlgebraicClosure k),
        HopfAlgebra.Point.semisimplePart k H (AlgebraicClosure k) g = 1 := by
  rw [unipotentCommHopfAlgProperty_iff]
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

/-- The category of finite-type unipotent coordinate Hopf algebras over a field. -/
abbrev UnipotentCommHopfAlgCat (k : Type u) [Field k] :=
  (unipotentCommHopfAlgProperty k).FullSubcategory

namespace AlphaP

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The Frobenius kernel `αₚ` is unipotent. This is a genuinely nonreduced example: the
coordinate ring is nonreduced, but every point over the algebraic closure is the identity. -/
@[grind =>]
theorem unipotent_coordinateRing :
    unipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (CoordinateRing (R := k) p)) := by
  rw [unipotentCommHopfAlgProperty_iff]
  intro g
  rw [points_eq_one_of_isReduced p g]
  exact HopfAlgebra.isUnipotentPoint_one

end AlphaP

end TauCeti
