/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Geometric connectedness and reducedness of split tori

The coordinate ring of a split torus is the group algebra of a finite-rank free abelian group.
Over a field this group algebra is a domain, so it is reduced and has connected prime spectrum.
The same argument survives every field extension, proving that split tori are geometrically
reduced and geometrically connected.

## Main declarations

* `TauCeti.SplitTorus.geometricallyConnected_coordinateRing`: a finite-rank split torus is
  geometrically connected.
* `TauCeti.SplitTorus.geometricallyReduced_coordinateRing`: a finite-rank split torus is
  geometrically reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This establishes the geometric connectedness and reducedness of the split case in Layer 4,
"Tori: split and non-split", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

namespace SplitTorus

/-- Scalar extension identifies a split torus coordinate ring with the corresponding group
algebra over the extension field. -/
private noncomputable def coordinateRingBaseChangeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (K : Type u) [Field K] [Algebra k K] :
    MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) ⊗[k] K ≃+*
      MonoidAlgebra K (Multiplicative (σ →₀ ℤ)) := by
  let ψ := _root_.CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (DiagonalizableGroup.baseChangeCoordinateRingIso k K (characterGroup σ)))
  exact (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans ψ.toAlgEquiv.toRingEquiv

/-- **The coordinate Hopf algebra of a finite-rank split torus is geometrically connected.** -/
@[grind =>]
theorem geometricallyConnected_coordinateRing
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    geometricallyConnectedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one]
  intro K _ _ e he
  let φ := coordinateRingBaseChangeEquiv k σ K
  have he' : IsIdempotentElem (φ e) := he.map φ.toRingHom
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he' with h | h
  · left
    exact φ.injective (by simpa using h)
  · right
    exact φ.injective (by simpa using h)

/-- **The coordinate Hopf algebra of a finite-rank split torus is geometrically reduced.** -/
@[grind =>]
theorem geometricallyReduced_coordinateRing
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    geometricallyReducedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj := by
  rw [geometricallyReducedCommHopfAlgProperty_iff]
  intro K _ _
  let φ := coordinateRingBaseChangeEquiv k σ K
  exact isReduced_of_injective φ.toRingHom φ.injective

end SplitTorus

end TauCeti
