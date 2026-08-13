/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.BaseChange

/-!
# Smoothness and connectedness of tori

The coordinate ring of a split torus is the group algebra of a finite-rank free abelian group.
Over a field this group algebra is a domain, so it is reduced and has connected prime spectrum.
The same argument survives every field extension, proving that split tori are geometrically
reduced and geometrically connected.

A torus becomes split over an algebraic closure. The base-change descent theorems transport both
geometric properties back to the ground field. Finally, geometric reducedness of a finite-type
affine group over a field implies smoothness, so every torus is smooth.

## Main declarations

* `TauCeti.SplitTorus.geometricallyConnected_coordinateRing`: a finite-rank split torus is
  geometrically connected.
* `TauCeti.SplitTorus.geometricallyReduced_coordinateRing`: a finite-rank split torus is
  geometrically reduced.
* `TauCeti.torusCommHopfAlgProperty.geometricallyConnected`: every torus is geometrically
  connected.
* `TauCeti.torusCommHopfAlgProperty.geometricallyReduced`: every torus is geometrically reduced.
* `TauCeti.torusCommHopfAlgProperty.smooth`: every torus is smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This completes the smoothness and geometric-connectedness part of Layer 4, "Tori: split and
non-split", of the ReductiveGroups roadmap. The character lattice of a non-split torus with its
Galois action remains to be constructed.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

namespace SplitTorus

/-- **The coordinate Hopf algebra of a finite-rank split torus is geometrically connected.** -/
@[grind =>]
theorem geometricallyConnected_coordinateRing
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    geometricallyConnectedCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff_idempotent_eq_zero_or_one]
  intro K _ _ e he
  let ψ := _root_.CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (DiagonalizableGroup.baseChangeCoordinateRingIso k K (characterGroup σ)))
  let φ : MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) ⊗[k] K ≃+*
      MonoidAlgebra K (Multiplicative (σ →₀ ℤ)) :=
    (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans ψ.toAlgEquiv.toRingEquiv
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
  let ψ := _root_.CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat K) (_root_.CommHopfAlgCat K)).mapIso
      (DiagonalizableGroup.baseChangeCoordinateRingIso k K (characterGroup σ)))
  let φ : MonoidAlgebra k (Multiplicative (σ →₀ ℤ)) ⊗[k] K ≃+*
      MonoidAlgebra K (Multiplicative (σ →₀ ℤ)) :=
    (Algebra.TensorProduct.comm k _ K).toRingEquiv.trans ψ.toAlgEquiv.toRingEquiv
  exact isReduced_of_injective φ.toRingHom φ.injective

end SplitTorus

/-- **Every torus over a field is geometrically connected.** -/
@[grind →]
theorem torusCommHopfAlgProperty.geometricallyConnected
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  apply geometricallyConnectedCommHopfAlgProperty.of_baseChange
    k (AlgebraicClosure k) H.obj
  exact (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
    (SplitTorus.geometricallyConnected_coordinateRing
      (AlgebraicClosure k) (ULift.{u} (Fin n)))

/-- **Every torus over a field is geometrically reduced.** -/
@[grind →]
theorem torusCommHopfAlgProperty.geometricallyReduced
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    geometricallyReducedCommHopfAlgProperty k H.obj := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  apply geometricallyReducedCommHopfAlgProperty.of_baseChange
    (AlgebraicClosure k) H.obj
  exact (geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i)
    (SplitTorus.geometricallyReduced_coordinateRing
      (AlgebraicClosure k) (ULift.{u} (Fin n)))

/-- **Every torus over a field is smooth.** -/
@[grind →]
theorem torusCommHopfAlgProperty.smooth
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    smoothCommHopfAlgProperty k H.obj :=
  smoothCommHopfAlgProperty_of_geometricallyReduced k H.obj hH.geometricallyReduced

end TauCeti
