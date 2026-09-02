/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Borel subgroups in Hopf coordinates

A closed subgroup of a finite-type affine group over a field is encoded contravariantly by a
Hopf ideal in its coordinate algebra. This file defines a Borel subgroup to be a smooth,
geometrically connected, geometrically solvable closed subgroup whose base change to an
algebraic closure is maximal among closed subgroups with those properties.

Smoothness remains explicit: the ambient affine group need not be smooth, and geometric
connectedness and solvability alone do not exclude nonreduced subgroup schemes. Because Hopf
ideals reverse subgroup inclusion, maximality of the represented subgroup is minimality of its
defining ideal among ideals satisfying the three geometric properties after base change to an
algebraic closure. This geometric maximality is essential over a non-algebraically-closed field:
maximality only among subgroups defined over the ground field is not the Borel condition.

## Main declarations

* `TauCeti.HopfIdeal.IsBorel`: the Borel-subgroup predicate in Hopf coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 17.a.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.

This supplies the Borel-subgroup predicate required by Layer 7, "Borel subgroups, maximal tori,
and their conjugacy", of the ReductiveGroups roadmap. Existence and conjugacy for general
reductive groups remain downstream.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace HopfIdeal

/-- A Hopf ideal defines a Borel subgroup when, after base change to an algebraic closure, its
quotient coordinate algebra is smooth, geometrically connected, and geometrically solvable, and
no strictly larger closed subgroup has all three properties.

The order is contravariant: `J ≤ I` says that the subgroup cut out by `I` is contained in the
subgroup cut out by `J`. -/
def IsBorel (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) : Prop :=
  let K := AlgebraicClosure k
  let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
    ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
  let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
  Minimal (fun J : HopfIdeal K H'.obj ↦
    smoothCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.quotient
          H' J).obj ∧
      geometricallyConnectedCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.quotient
          H' J).obj ∧
      geometricallySolvablePointsCommHopfAlgProperty K
        (FiniteTypeCommHopfAlgCat.quotient
          H' J).obj) I'

/-- The Hopf-ideal criterion for a Borel subgroup: after algebraic-closure base change, its
quotient is smooth, geometrically connected, and geometrically solvable, and it is maximal among
such closed subgroups. -/
@[simp]
theorem isBorel_iff (k : Type u) [Field k] (H : _root_.CommHopfAlgCat.{u} k)
    [Algebra.FiniteType k H] (I : HopfIdeal k H) :
    let K := AlgebraicClosure k
    let H' := FiniteTypeCommHopfAlgCat.baseChange (K := K)
      ⟨H, (finiteTypeCommHopfAlgProperty_iff H).2 inferInstance⟩
    let I' := CommHopfAlgCat.baseChangeHopfIdeal (K := K) I
    IsBorel k H I ↔
      smoothCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        geometricallyConnectedCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        geometricallySolvablePointsCommHopfAlgProperty K
          (FiniteTypeCommHopfAlgCat.quotient
            H' I').obj ∧
        ∀ J : HopfIdeal K H'.obj,
          smoothCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            geometricallyConnectedCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            geometricallySolvablePointsCommHopfAlgProperty K
              (FiniteTypeCommHopfAlgCat.quotient
                H' J).obj →
            J ≤ I' → I' ≤ J := by
  constructor
  · rintro ⟨⟨hsmooth, hconnected, hsolvable⟩, hmax⟩
    exact ⟨hsmooth, hconnected, hsolvable,
      fun J hJsmooth hJconnected hJsolvable hJI ↦
        hmax ⟨hJsmooth, hJconnected, hJsolvable⟩ hJI⟩
  · rintro ⟨hsmooth, hconnected, hsolvable, hmax⟩
    exact ⟨⟨hsmooth, hconnected, hsolvable⟩,
      fun J hJ hJI ↦ hmax J hJ.1 hJ.2.1 hJ.2.2 hJI⟩

end HopfIdeal

end TauCeti
