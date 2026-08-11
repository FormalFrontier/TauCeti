/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
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

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.26 and Corollary 1.27.

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

/-- Geometric reducedness is preserved by extension of the base field. -/
theorem geometricallyReducedCommHopfAlgProperty.baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{u} k)
    (hH : geometricallyReducedCommHopfAlgProperty k H) :
    geometricallyReducedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H) := by
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro L _ _
  let _ : Algebra k L := Algebra.compHom L (algebraMap k K)
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  let e := (Algebra.TensorProduct.comm K (K ⊗[k] H) L).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k K L L H).toRingEquiv.trans
      (Algebra.TensorProduct.comm k L H).toRingEquiv)
  rw [geometricallyReducedCommHopfAlgProperty_iff] at hH
  let _ := hH L
  exact isReduced_of_injective e.toRingHom e.injective

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
