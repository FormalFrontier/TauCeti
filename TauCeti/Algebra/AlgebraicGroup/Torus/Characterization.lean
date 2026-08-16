/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Torsion
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange

/-!
# Characterization of tori among groups of multiplicative type

A finite-type group of multiplicative type is a torus exactly when it is geometrically connected
and geometrically reduced. After passing to an algebraic closure, its coordinate ring is a group
algebra. Reducedness and connectedness force the character group to be torsion-free, while finite
generation then identifies it with a finite-rank free abelian group.

## Main declaration

* `iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced`: a finite-type
  commutative Hopf algebra over a field is a torus exactly when it is of multiplicative type,
  geometrically connected, and geometrically reduced.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This completes the intrinsic characterization of tori required by Layer 4, "Tori: split and
non-split", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

private theorem exists_mulEquiv_finsupp_int
    (G : Type u) [CommGroup G] [Group.FG G] [IsMulTorsionFree G] :
    ∃ n : ℕ, Nonempty (G ≃* Multiplicative (Fin n →₀ ℤ)) := by
  let _ : Module.Finite ℤ (Additive G) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive G))
  let _ : Module.IsTorsionFree ℤ (Additive G) := inferInstance
  let _ : Module.Free ℤ (Additive G) := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ (Additive G)
  let _ : Finite (Module.Free.ChooseBasisIndex ℤ (Additive G)) :=
    Module.Finite.finite_basis b
  let eι := Finite.equivFin (Module.Free.ChooseBasisIndex ℤ (Additive G))
  let e : Additive G ≃+ (Fin (Nat.card (Module.Free.ChooseBasisIndex ℤ (Additive G))) →₀ ℤ) :=
    b.repr.toAddEquiv.trans (Finsupp.domCongr eι)
  exact ⟨_, ⟨AddEquiv.toMultiplicative e⟩⟩

namespace torusCommHopfAlgProperty

/-- **A finite-type commutative Hopf algebra over a field is a torus if and only if it is a
group of multiplicative type, geometrically connected, and geometrically reduced.** -/
theorem iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k H ↔
      multiplicativeTypeCommHopfAlgProperty k H ∧
      geometricallyConnectedCommHopfAlgProperty k H.obj ∧
      geometricallyReducedCommHopfAlgProperty k H.obj := by
  constructor
  · intro hH
    exact ⟨hH.multiplicativeType, hH.geometricallyConnected, hH.geometricallyReduced⟩
  · rintro ⟨hmt, hconnected, hreduced⟩
    rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing] at hmt
    obtain ⟨G, ⟨i⟩⟩ := hmt
    let i' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} (AlgebraicClosure k))
      (CommHopfAlgCat.{u} (AlgebraicClosure k))).mapIso i
    have hconnected' : geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G).obj :=
      (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso i'.symm
        (geometricallyConnectedCommHopfAlgProperty.baseChange
          k (AlgebraicClosure k) H.obj hconnected)
    have hreduced' : geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G).obj :=
      (geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso i'.symm
        (geometricallyReducedCommHopfAlgProperty.baseChange (AlgebraicClosure k) hreduced)
    let coordinateRingObjIso :
        _root_.CommHopfAlgCat.of (AlgebraicClosure k)
            (MonoidAlgebra (AlgebraicClosure k) G) ≅
          (DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G).obj :=
      Iso.refl _
    have hconnectedMonoid :=
      (geometricallyConnectedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
        coordinateRingObjIso hconnected'
    have hreducedMonoid :=
      (geometricallyReducedCommHopfAlgProperty (AlgebraicClosure k)).prop_of_iso
        coordinateRingObjIso hreduced'
    let _ : ConnectedSpace
        (PrimeSpectrum (MonoidAlgebra (AlgebraicClosure k) G)) :=
      hconnectedMonoid.connectedSpace (AlgebraicClosure k)
        (_root_.CommHopfAlgCat.of (AlgebraicClosure k)
          (MonoidAlgebra (AlgebraicClosure k) G))
    let _ : IsReduced (MonoidAlgebra (AlgebraicClosure k) G) := hreducedMonoid.isReduced
    let _ : IsMulTorsionFree G :=
      isMulTorsionFree_of_isReduced_monoidAlgebra_of_connectedSpace
        (AlgebraicClosure k) G
    obtain ⟨n, ⟨e⟩⟩ := exists_mulEquiv_finsupp_int G
    let e' : SplitTorus.characterGroup (ULift.{u} (Fin n)) ≃* G :=
      (AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift)).trans e.symm
    let j : DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
          (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅
        DiagonalizableGroup.coordinateRing (AlgebraicClosure k) G :=
      ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk
        (MonoidAlgebra.domCongrBialgEquiv (AlgebraicClosure k) (AlgebraicClosure k) e')
    rw [torusCommHopfAlgProperty_iff]
    exact ⟨n, ⟨j ≪≫ i⟩⟩

end torusCommHopfAlgProperty

end TauCeti
