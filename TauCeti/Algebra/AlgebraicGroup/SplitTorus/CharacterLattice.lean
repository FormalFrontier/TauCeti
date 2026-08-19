/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic

/-!
# Character lattices of split tori

The intrinsic character lattice of a split torus is its defining finite-rank free abelian group,
and its absolute-Galois action is trivial.

## Main declarations

* `TauCeti.SplitTorus.characterLatticeEquiv`: the intrinsic character lattice of a split
  presentation is its defining free abelian group.
* `TauCeti.SplitTorus.smul_characterLattice_eq_self`: the absolute-Galois action on a split
  torus's character lattice is trivial.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definition 12.17.
-/

public section

namespace TauCeti

universe u

namespace SplitTorus

/-- The additive character lattice of a split-torus presentation is its defining finite-rank
free `ℤ`-module. -/
noncomputable def characterLatticeEquiv
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    CommHopfAlgCat.additiveCharacterGroup
        (DiagonalizableGroup.coordinateRing k
          (characterGroup σ)).obj ≃+ (σ →₀ ℤ) :=
  (MulEquiv.toAdditive (DiagonalizableGroup.geometricCharacterGroupEquiv k
    (characterGroup σ))).trans
    (AddEquiv.additiveMultiplicative (σ →₀ ℤ))

/-- The split-torus lattice equivalence sends a character to the additive form of its
diagonalizable-group character. -/
@[simp]
theorem ofAdd_characterLatticeEquiv_apply
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj) :
    Multiplicative.ofAdd (characterLatticeEquiv k σ x) =
      DiagonalizableGroup.geometricCharacterGroupEquiv k
        (characterGroup σ) x.toMul := by
  rfl

/-- A split-torus character corresponds to `m` exactly when base change identifies its underlying
group-like element with the standard monomial indexed by `Multiplicative.ofAdd m`. -/
@[simp]
theorem characterLatticeEquiv_apply_eq_iff
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj)
    (m : σ →₀ ℤ) :
    characterLatticeEquiv k σ x = m ↔
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k) x.toMul.val =
        _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  rw [← (Multiplicative.ofAdd (α := σ →₀ ℤ)).apply_eq_iff_eq]
  rw [ofAdd_characterLatticeEquiv_apply]
  exact DiagonalizableGroup.geometricCharacterGroupEquiv_apply_eq_iff k
    (characterGroup σ) x.toMul (Multiplicative.ofAdd m)

/-- The inverse split-torus character corresponding to `m` is the standard monomial indexed by
`Multiplicative.ofAdd m` in the scalar-extended coordinate ring. -/
@[simp]
theorem characterLatticeEquiv_symm_apply_toMul_val
    (k : Type u) [Field k] (σ : Type u) [Finite σ] (m : σ →₀ ℤ) :
    ((characterLatticeEquiv k σ).symm m).toMul.val =
      1 ⊗ₜ[k] _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  exact DiagonalizableGroup.geometricCharacterGroupEquiv_symm_apply_val k
    (characterGroup σ) (Multiplicative.ofAdd m)

/-- The absolute-Galois action on the character lattice of a split torus is trivial. -/
@[simp]
theorem smul_characterLattice_eq_self (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (γ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj) :
    γ • x = x := by
  apply Additive.toMul.injective
  rw [CommHopfAlgCat.toMul_smul]
  exact DiagonalizableGroup.smul_geometricCharacterGroup_eq_self k (characterGroup σ) γ x.toMul

end SplitTorus

end TauCeti
