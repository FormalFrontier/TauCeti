/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.RingTheory.Idempotents.ConnectedSpectrum
import Mathlib.RingTheory.Flat.Basic

/-!
# Geometric connectedness of affine group schemes

For a commutative Hopf algebra `H` over a field `k`, the affine group scheme `Spec H` is
geometrically connected precisely when every field extension has connected coordinate-ring
spectrum.  Since the base change to a field `K` has coordinate ring `H ⊗[k] K`, this is
equivalent to saying that `H ⊗[k] K` has no idempotents other than zero and one for every
extension field `K / k`.

The quantification over extensions is essential: connectedness of `Spec H` over `k` alone is
strictly weaker than geometric connectedness.  This file keeps geometric connectedness as an
explicit predicate, in parallel with the finite-type and smoothness predicates already used for
affine group schemes.

## Main declarations

* `TauCeti.geometricallyConnectedCommHopfAlgProperty`: the coordinate-ring predicate.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff`: its connected-spectrum form.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_idempotents`: its idempotent form.
* `TauCeti.geometricallyConnected_hopfSpec_iff`: compatibility with Mathlib's scheme-theoretic
  `GeometricallyConnected` predicate.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.a.

This is the geometric-connectedness prerequisite for Layer 3, "Identity component and component
group", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

/-- A Hopf algebra remains nontrivial after extension of its base field. -/
private theorem nontrivial_tensorField
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial ((H : Type u) ⊗[k] K) := by
  have hinjective : Function.Injective (algebraMap k H) := by
    intro x y hxy
    have h := congrArg (Coalgebra.counit (R := k)) hxy
    simpa only [Bialgebra.counit_algebraMap] using h
  let : Nontrivial (H : Type u) := hinjective.nontrivial
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
    k H K (algebraMap k K).injective

/-- A commutative Hopf algebra over a field is geometrically connected when the spectrum of its
coordinate ring remains connected after every extension of the base field. -/
def geometricallyConnectedCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (CommHopfAlgCat.{u} k) :=
  fun H ↦ ∀ (K : Type u) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K))

/-- The coordinate-ring geometric-connectedness predicate unfolds to connectedness of every
base-changed prime spectrum. -/
theorem geometricallyConnectedCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (PrimeSpectrum ((H : Type u) ⊗[k] K)) :=
  Iff.rfl

/-- **A commutative Hopf algebra is geometrically connected exactly when every field extension
of its coordinate ring has only the trivial idempotents.** -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_idempotents
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  constructor
  · intro h K _ _
    let := nontrivial_tensorField k H K
    exact connectedSpace_primeSpectrum_iff.mp (h K)
  · intro h K _ _
    let := nontrivial_tensorField k H K
    exact connectedSpace_primeSpectrum_iff.mpr (h K)

/-- **Geometric connectedness agrees across the coordinate-ring and affine-group-scheme
models.** A commutative Hopf algebra is geometrically connected after every field extension if
and only if the structural morphism of its Hopf spectrum is geometrically connected. -/
theorem geometricallyConnected_hopfSpec_iff
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) := by
  let : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [geometricallyConnectedCommHopfAlgProperty_iff, hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @GeometricallyConnected) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mpr (h K)
  · intro h K _ _
    exact (pullbackSpecIso k H K).hom.homeomorph.connectedSpace_iff.mp (h K)

/-- The structural morphism of a Hopf spectrum is geometrically connected exactly when every
field extension of its coordinate ring has only zero and one as idempotents. -/
theorem geometricallyConnected_hopfSpec_iff_idempotents
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    GeometricallyConnected
        (((hopfSpec (CommRingCat.of k)).obj (Opposite.op H)).X.hom) ↔
      ∀ (K : Type u) [Field K] [Algebra k K] (e : (H : Type u) ⊗[k] K),
        IsIdempotentElem e → e = 0 ∨ e = 1 := by
  rw [← geometricallyConnected_hopfSpec_iff,
    geometricallyConnectedCommHopfAlgProperty_iff_idempotents]

end TauCeti
