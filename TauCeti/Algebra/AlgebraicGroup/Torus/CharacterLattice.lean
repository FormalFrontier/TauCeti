/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic

/-!
# The character lattice of a torus

The geometric characters of a torus are the group-like elements of its coordinate algebra after
extension to an algebraic closure. The generic construction and its absolute-Galois action are in
`TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice`.

The defining splitting over the algebraic closure identifies the underlying additive character
group, noncanonically, with a finite-rank free abelian group. The absolute-Galois action is
constructed in the generic character-group module, but its continuity and an equivariant
classification of non-split tori are not formalized here.

## Main declarations

* `TauCeti.exists_characterLattice_addEquiv_of_torus`: the character lattice of any torus is
  finite-rank free.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti

universe u

/-- The character lattice of a torus is a finite-rank free abelian group. The equivalence is
noncanonical: it uses the splitting over the chosen algebraic closure from the torus predicate. -/
theorem exists_characterLattice_addEquiv_of_torus (k : Type u) [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (hH : torusCommHopfAlgProperty k H) :
    ∃ n : ℕ, Nonempty
      (CommHopfAlgCat.additiveCharacterGroup H.obj ≃+ (ULift.{u} (Fin n) →₀ ℤ)) := by
  rw [torusCommHopfAlgProperty_iff] at hH
  obtain ⟨n, ⟨i⟩⟩ := hH
  exact ⟨n, ⟨(CommHopfAlgCat.additiveCharacterGroupEquivOfIso k H
    (SplitTorus.characterGroup (ULift.{u} (Fin n))) i).trans
      (AddEquiv.additiveMultiplicative (ULift.{u} (Fin n) →₀ ℤ))⟩⟩

end TauCeti
