/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# The character lattice of a torus

The geometric characters of a torus are the group-like elements of its coordinate algebra after
extension to an algebraic closure. The generic construction and its absolute-Galois action are in
`TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice`.

The defining splitting over the algebraic closure identifies this character group,
noncanonically, with a finite-rank free abelian group. Thus its additive form is the character
lattice equipped with the standard absolute-Galois action used in the classification of
non-split tori.

## Main declarations

* `TauCeti.CommHopfAlgCat.geometricCharacterGroup_fg_of_torus`: the geometric character group of
  a torus is finitely generated.
* `TauCeti.splitTorusCharacterLatticeEquiv`: the intrinsic character lattice of a split
  presentation is its defining free abelian group.
* `TauCeti.exists_characterLattice_addEquiv_of_torus`: the character lattice of any torus is
  finite-rank free.

## References

See J. S. Milne, *Algebraic Groups* (2017), §§12.14--12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- The geometric character group of a torus is finitely generated. -/
theorem geometricCharacterGroup_fg_of_torus
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : torusCommHopfAlgProperty k H) :
    Group.FG (geometricCharacterGroup H.obj) :=
  geometricCharacterGroup_fg_of_multiplicativeType H
    (torusCommHopfAlgProperty.multiplicativeType k H hH)

end CommHopfAlgCat

/-- The additive character lattice of a split-torus presentation is its defining finite-rank
free `ℤ`-module. -/
noncomputable def splitTorusCharacterLatticeEquiv
    (k : Type u) [Field k] (n : ℕ) :
    CommHopfAlgCat.characterLattice
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup (ULift.{u} (Fin n)))).obj ≃+
      (ULift.{u} (Fin n) →₀ ℤ) :=
  (MulEquiv.toAdditive (DiagonalizableGroup.geometricCharacterGroupEquiv k
    (SplitTorus.characterGroup (ULift.{u} (Fin n))))).trans
    (AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ))

/-- The character lattice of a torus is a finite-rank free abelian group. The equivalence is
noncanonical: it uses the splitting over the chosen algebraic closure from the torus predicate. -/
theorem exists_characterLattice_addEquiv_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    ∃ n : ℕ, Nonempty
      (CommHopfAlgCat.characterLattice H.obj ≃+ (ULift.{u} (Fin n) →₀ ℤ)) := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  let i' : _root_.CommHopfAlgCat.of (AlgebraicClosure k)
        (MonoidAlgebra (AlgebraicClosure k)
          (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) ≅
      _root_.CommHopfAlgCat.of (AlgebraicClosure k)
        (AlgebraicClosure k ⊗[k] H) :=
    (finiteTypeCommHopfAlgProperty (AlgebraicClosure k)).ι.mapIso i
  let e : CommHopfAlgCat.geometricCharacterGroup H.obj ≃*
      Multiplicative (ULift.{u} (Fin n) →₀ ℤ) :=
    (TauCeti.GroupLike.mapEquiv (_root_.CommHopfAlgCat.ofIso i')).symm.trans
      (MonoidAlgebra.groupLikeEquiv (R := AlgebraicClosure k)
        (H := Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
  exact ⟨n, ⟨(MulEquiv.toAdditive e).trans
    (AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ))⟩⟩

end TauCeti
