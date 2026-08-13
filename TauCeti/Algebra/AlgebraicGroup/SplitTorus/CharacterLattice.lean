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

/-- The split-torus lattice equivalence sends a character to the additive form of its
diagonalizable-group character. -/
@[simp]
theorem splitTorusCharacterLatticeEquiv_apply_ofAdd
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.characterLattice
      (DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup σ)).obj) :
    Multiplicative.ofAdd (splitTorusCharacterLatticeEquiv k σ x) =
      DiagonalizableGroup.geometricCharacterGroupEquiv k
        (SplitTorus.characterGroup σ) x.toMul := by
  rfl

/-- A split-torus character corresponds to `m` exactly when its underlying group-like element is
the standard monomial indexed by `Multiplicative.ofAdd m`. -/
@[simp]
theorem splitTorusCharacterLatticeEquiv_apply_eq_iff
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.characterLattice
      (DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup σ)).obj)
    (m : σ →₀ ℤ) :
    splitTorusCharacterLatticeEquiv k σ x = m ↔
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x.toMul.val =
        _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  rw [← (Multiplicative.ofAdd (α := σ →₀ ℤ)).apply_eq_iff_eq]
  rw [splitTorusCharacterLatticeEquiv_apply_ofAdd]
  exact DiagonalizableGroup.geometricCharacterGroupEquiv_apply_eq_iff k
    (SplitTorus.characterGroup σ) x.toMul (Multiplicative.ofAdd m)

/-- The inverse split-torus character corresponding to `m` is the standard monomial indexed by
`Multiplicative.ofAdd m` in the scalar-extended coordinate ring. -/
@[simp]
theorem splitTorusCharacterLatticeEquiv_symm_apply_toMul_val
    (k : Type u) [Field k] (σ : Type u) [Finite σ] (m : σ →₀ ℤ) :
    ((splitTorusCharacterLatticeEquiv k σ).symm m).toMul.val =
      1 ⊗ₜ[k] _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  change
    ((DiagonalizableGroup.geometricCharacterGroupEquiv k
      (SplitTorus.characterGroup σ)).symm (Multiplicative.ofAdd m)).val = _
  exact DiagonalizableGroup.geometricCharacterGroupEquiv_symm_apply_val k
    (SplitTorus.characterGroup σ) (Multiplicative.ofAdd m)

end TauCeti
