/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic

/-!
# Tori over a field

A finite-type affine group over a field is a torus when it becomes a finite-rank split torus
after extending scalars to an algebraic closure. On coordinate Hopf algebras, the rank-`n` split
torus has coordinate ring

```text
k[Multiplicative (Fin n →₀ ℤ)].
```

This file records both the split and geometric forms of that definition as object properties on
finite-type commutative Hopf algebras. Keeping them as properties, rather than building them into
the ambient category, leaves finite, non-smooth groups such as `μ_p` in the general theory.

Every split torus is a torus: after base change, the standard coordinate-ring comparison
identifies `K ⊗[k] k[ℤⁿ]` with `K[ℤⁿ]`. Every torus is of multiplicative type, since its
base change is a diagonalizable coordinate Hopf algebra. Thus this definition extends the
existing multiplicative-type theory while imposing the free finite-rank character lattice that
distinguishes tori from general groups of multiplicative type.

## Main declarations

* `TauCeti.splitTorusCommHopfAlgProperty`: finite-type coordinate Hopf algebras isomorphic over
  the base ring to the coordinate ring of a finite-rank split torus.
* `TauCeti.torusCommHopfAlgProperty`: finite-type coordinate Hopf algebras that become a
  finite-rank split torus over `AlgebraicClosure k`.
* `TauCeti.splitTorusCommHopfAlgProperty.torus`: every split torus is a torus.
* `TauCeti.torusCommHopfAlgProperty.multiplicativeType`: every torus is of multiplicative type.
* `TauCeti.SplitTorus.splitTorus_coordinateRing`: the standard finite-rank split tori satisfy the
  split predicate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.

This is the coordinate-algebra definition required by Layer 4, "Tori: split and non-split", of
the ReductiveGroups roadmap. Smoothness and geometric connectedness are proved in
`TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected`; the next step is the character lattice
with its Galois action.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- The object property selecting finite-type commutative Hopf algebras that are coordinate
rings of split tori of finite rank.

The witness `n` is the rank. The finite index type is universe-lifted so that its character group
lives in the same universe as `k`; this does not change the represented rank-`n` torus. -/
def splitTorusCommHopfAlgProperty (k : Type u) [CommRing k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ ∃ n : ℕ, Nonempty
    (DiagonalizableGroup.coordinateRing k
        (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅ H)

/-- Membership in the split-torus property means being isomorphic to the coordinate Hopf algebra
of a finite-rank split torus. -/
@[simp]
theorem splitTorusCommHopfAlgProperty_iff
    (k : Type u) [CommRing k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    splitTorusCommHopfAlgProperty k H ↔
      ∃ n : ℕ, Nonempty
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅ H) :=
  Iff.rfl

/-- Being a split torus is invariant under isomorphisms of finite-type commutative Hopf
algebras. -/
instance (k : Type u) [CommRing k] :
    (splitTorusCommHopfAlgProperty k).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨n, ⟨i⟩⟩
    exact ⟨n, ⟨i ≪≫ e⟩⟩

/-- The category of finite-type split-torus coordinate Hopf algebras over a commutative ring. -/
abbrev SplitTorusCommHopfAlgCat (k : Type u) [CommRing k] :=
  (splitTorusCommHopfAlgProperty k).FullSubcategory

/-- The object property selecting finite-type commutative Hopf algebras that become coordinate
rings of split tori of finite rank after base change to an algebraic closure.

This is the coordinate-Hopf-algebra definition of a not-necessarily-split torus over `k`. -/
def torusCommHopfAlgProperty (k : Type u) [Field k] :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  (splitTorusCommHopfAlgProperty (AlgebraicClosure k)).inverseImage
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k))

/-- Membership in the torus property means becoming a finite-rank split torus after base change
to an algebraic closure. -/
@[simp]
theorem torusCommHopfAlgProperty_iff
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    torusCommHopfAlgProperty k H ↔
      ∃ n : ℕ, Nonempty
        (DiagonalizableGroup.coordinateRing (AlgebraicClosure k)
            (SplitTorus.characterGroup (ULift.{u} (Fin n))) ≅
          FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
  Iff.rfl

/-- Being a torus is invariant under isomorphisms of finite-type commutative Hopf algebras. -/
instance (k : Type u) [Field k] :
    (torusCommHopfAlgProperty k).IsClosedUnderIsomorphisms := by
  unfold torusCommHopfAlgProperty
  infer_instance

/-- The category of finite-type torus coordinate Hopf algebras over a field.

Objects need not be split over the base field; they become split after extension to an algebraic
closure. -/
abbrev TorusCommHopfAlgCat (k : Type u) [Field k] :=
  (torusCommHopfAlgProperty k).FullSubcategory

/-- Every split torus is a torus. -/
@[grind →]
theorem splitTorusCommHopfAlgProperty.torus
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : splitTorusCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty k H := by
  rw [splitTorusCommHopfAlgProperty_iff] at hH
  rw [torusCommHopfAlgProperty_iff]
  obtain ⟨n, ⟨i⟩⟩ := hH
  exact ⟨n, ⟨
    (DiagonalizableGroup.baseChangeCoordinateRingIso k (AlgebraicClosure k)
      (SplitTorus.characterGroup (ULift.{u} (Fin n)))).symm ≪≫
    (FiniteTypeCommHopfAlgCat.baseChangeFunctor (K := AlgebraicClosure k)).mapIso i⟩⟩

/-- Every torus is a group of multiplicative type. -/
@[grind →]
theorem torusCommHopfAlgProperty.multiplicativeType
    (k : Type u) [Field k] (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    multiplicativeTypeCommHopfAlgProperty k H := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff_exists_iso_coordinateRing]
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, hn⟩ := hH
  exact ⟨SplitTorus.characterGroup (ULift.{u} (Fin n)), hn⟩

namespace SplitTorus

/-- The coordinate Hopf algebra of a finite-rank split torus satisfies the split-torus property. -/
@[grind =>]
theorem splitTorus_coordinateRing (k : Type u) [CommRing k] (σ : Type u) [Finite σ] :
    splitTorusCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let eσ : σ ≃ ULift.{u} (Fin (Nat.card σ)) :=
    (Finite.equivFin σ).trans Equiv.ulift.symm
  let e : Multiplicative (σ →₀ ℤ) ≃*
      Multiplicative (ULift.{u} (Fin (Nat.card σ)) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr eσ)
  let i : DiagonalizableGroup.coordinateRing k (characterGroup σ) ≅
      DiagonalizableGroup.coordinateRing k
        (characterGroup (ULift.{u} (Fin (Nat.card σ)))) :=
    ObjectProperty.isoMk _ <|
      _root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k e)
  exact ⟨Nat.card σ, ⟨i.symm⟩⟩

end SplitTorus

end TauCeti
