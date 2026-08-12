/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.RingTheory.Flat.Basic

/-!
# Geometric connectedness of commutative Hopf algebras

For a commutative Hopf algebra `H` over a field `k`, geometric connectedness means that after
every extension `K / k` of the base field, the base-changed coordinate ring `H ⊗[k] K` has
connected prime spectrum. This is equivalent to saying that every such base change has no
idempotents other than zero and one.

The condition is exposed as an `ObjectProperty` on the ambient Hopf-algebra category; consumers
can impose it without introducing a separate bundled category of connected objects.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty`: the coordinate-ring predicate.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff`: its connected-spectrum form.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one`: its
  idempotent form.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the geometric-connectedness prerequisite for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

/-- A Hopf algebra remains nontrivial after extension of its base field. -/
private theorem nontrivial_tensorProduct
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial ((H : Type u) ⊗[k] K) := by
  let : Nontrivial (H : Type u) := Bialgebra.nontrivial k
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
    k H K (algebraMap k K).injective

/-- A commutative Hopf algebra over a field is geometrically connected when the spectrum of its
coordinate ring remains connected after every extension of the base field. -/
def geometricallyConnectedCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{u} k) :=
  fun H ↦ ∀ (K : Type u) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K))

/-- Membership in the geometrically connected commutative-Hopf-algebra object property. -/
@[simp]
theorem geometricallyConnectedCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K)) :=
  Iff.rfl

/-- A geometrically connected commutative Hopf algebra has connected prime spectrum. -/
theorem geometricallyConnectedCommHopfAlgProperty.connectedSpace
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    (h : geometricallyConnectedCommHopfAlgProperty k H) :
    ConnectedSpace (PrimeSpectrum (H : Type u)) :=
  (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.rid k k H).toRingEquiv).connectedSpace_iff.mp (h k)

/-- Geometric connectedness is invariant under isomorphisms of commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (geometricallyConnectedCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso e hH := by
    rw [geometricallyConnectedCommHopfAlgProperty_iff] at hH ⊢
    intro K _ _
    let eK := Algebra.TensorProduct.congr
      (CommHopfAlgCat.ofIso e).toAlgEquiv (AlgEquiv.refl : K ≃ₐ[k] K)
    exact (PrimeSpectrum.homeomorphOfRingEquiv eK.toRingEquiv).connectedSpace_iff.mp (hH K)

/-- **A commutative Hopf algebra is geometrically connected exactly when, after every extension
`K / k` of the base field, every idempotent of `H ⊗[k] K` is zero or one.** -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  constructor
  · intro h K _ _
    let := nontrivial_tensorProduct k H K
    exact connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mp (h K)
  · intro h K _ _
    let := nontrivial_tensorProduct k H K
    exact connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr (h K)

end TauCeti
