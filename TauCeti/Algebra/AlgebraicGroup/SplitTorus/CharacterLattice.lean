/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic

/-!
# Character lattices of split tori

The intrinsic character lattice of a split torus is its defining finite-rank free abelian group.

## Main declarations

* `TauCeti.splitTorusCharacterLatticeEquiv`: the intrinsic character lattice of a split
  presentation is its defining free abelian group.

## References

See J. S. Milne, *Algebraic Groups* (2017), §§12.14--12.17, and W. C. Waterhouse,
*Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

namespace TauCeti

universe u

/-- The additive character lattice of a split-torus presentation is its defining finite-rank
free `ℤ`-module. -/
noncomputable def splitTorusCharacterLatticeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    CommHopfAlgCat.characterLattice
        (DiagonalizableGroup.coordinateRing k
          (SplitTorus.characterGroup σ)).obj ≃+ (σ →₀ ℤ) :=
  (MulEquiv.toAdditive (DiagonalizableGroup.geometricCharacterGroupEquiv k
    (SplitTorus.characterGroup σ))).trans
    (AddEquiv.additiveMultiplicative (σ →₀ ℤ))

end TauCeti
