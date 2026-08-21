/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
import Mathlib.Algebra.Field.ULift

/-!
# Geometric reducedness of commutative Hopf algebras

For a commutative Hopf algebra `H` over a field `k`, geometric reducedness means that every
field extension `K / k` in their common universe gives a reduced coordinate ring `H ⊗[k] K`.
The base field and Hopf algebra may live in independent universes.

Mathlib's `Algebra.IsGeometricallyReduced` tests the base change to algebraic closures of residue
fields. Its source currently lists equivalence with reducedness after arbitrary field extension
as a TODO. The all-extension condition used here implies Mathlib's existing algebra predicate.

## Main declarations

* `TauCeti.geometricallyReducedCommHopfAlgProperty`: geometric reducedness after every field
  extension.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.isGeometricallyReduced`: comparison with
  Mathlib's algebra predicate.
* `TauCeti.geometricallyReducedCommHopfAlgProperty.isReduced`: reducedness over the base field.
* The `ObjectProperty.IsClosedUnderIsomorphisms` instance records invariance under Hopf-algebra
  isomorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), for the geometric-reducedness terminology.

The object-property organization follows
`TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat` with reducedness replacing
connectedness.

This advances Layer 2, "Smoothness and dimension tools via `Lie(G)`", of the ReductiveGroups
roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v

noncomputable section

/-- A commutative Hopf algebra over a field is geometrically reduced when its coordinate ring
remains reduced after every extension of the base field. -/
def geometricallyReducedCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{v} k) :=
  fun H ↦ ∀ (K : Type (max u v)) [Field K] [Algebra k K],
    IsReduced ((H : Type v) ⊗[k] K)

/-- Membership in the geometrically reduced commutative-Hopf-algebra object property. -/
@[simp]
theorem geometricallyReducedCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{v} k) :
    geometricallyReducedCommHopfAlgProperty k H ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K],
        IsReduced ((H : Type v) ⊗[k] K) :=
  Iff.rfl

/-- The all-extension coordinate condition implies Mathlib's algebraic geometric-reducedness
predicate, which over a field tests the base change to an algebraic closure. -/
theorem geometricallyReducedCommHopfAlgProperty.isGeometricallyReduced
    {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k}
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    Algebra.IsGeometricallyReduced k H := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let _ : IsReduced ((H : Type v) ⊗[k] ULift.{v} (AlgebraicClosure k)) :=
    hH (ULift.{v} (AlgebraicClosure k))
  let e := (Algebra.TensorProduct.comm k H (ULift.{v} (AlgebraicClosure k))).trans
    (Algebra.TensorProduct.congr ULift.algEquiv (AlgEquiv.refl : H ≃ₐ[k] H))
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- A geometrically reduced commutative Hopf algebra has reduced coordinate ring over its base
field. -/
theorem geometricallyReducedCommHopfAlgProperty.isReduced
    {k : Type u} [Field k] {H : CommHopfAlgCat.{v} k}
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    IsReduced H := by
  let _ : Algebra.IsGeometricallyReduced k H := hH.isGeometricallyReduced
  exact Algebra.isReduced_of_isGeometricallyReduced k

/-- Geometric reducedness is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallyReducedCommHopfAlgProperty k :
      ObjectProperty (CommHopfAlgCat.{v} k)).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    rw [geometricallyReducedCommHopfAlgProperty_iff] at hH ⊢
    intro K _ _
    let _ := hH K
    let eK := Algebra.TensorProduct.congr
      (CommHopfAlgCat.ofIso e).toAlgEquiv (AlgEquiv.refl : K ≃ₐ[k] K)
    exact isReduced_of_injective eK.symm.toRingHom eK.symm.injective

end

end TauCeti
