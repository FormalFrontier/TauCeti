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

* `TauCeti.SplitTorus.characterLatticeEquiv`: the intrinsic character lattice of a split
  presentation is its defining free abelian group.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definition 12.17.
-/

public section

namespace TauCeti

universe u

namespace SplitTorus

/-- The absolute-Galois action specialized to the additive character group of a split torus. -/
noncomputable instance instAdditiveCharacterGroupGaloisAction
    (k : Type u) [Field k] (σ : Type u) [Finite σ] :
    DistribMulAction (Field.absoluteGaloisGroup k)
      (CommHopfAlgCat.additiveCharacterGroup
        (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj) :=
  CommHopfAlgCat.instAdditiveCharacterGroupGaloisAction
    (H := (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj)

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
theorem characterLatticeEquiv_apply_ofAdd
    (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj) :
    Multiplicative.ofAdd (characterLatticeEquiv k σ x) =
      DiagonalizableGroup.geometricCharacterGroupEquiv k
        (characterGroup σ) x.toMul := by
  rfl

/-- A split-torus character corresponds to `m` exactly when its underlying group-like element is
the standard monomial indexed by `Multiplicative.ofAdd m`. -/
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
  rw [characterLatticeEquiv_apply_ofAdd]
  exact DiagonalizableGroup.geometricCharacterGroupEquiv_apply_eq_iff k
    (characterGroup σ) x.toMul (Multiplicative.ofAdd m)

/-- The inverse split-torus character corresponding to `m` is the standard monomial indexed by
`Multiplicative.ofAdd m` in the scalar-extended coordinate ring. -/
@[simp]
theorem characterLatticeEquiv_symm_apply_toMul_val
    (k : Type u) [Field k] (σ : Type u) [Finite σ] (m : σ →₀ ℤ) :
    ((characterLatticeEquiv k σ).symm m).toMul.val =
      1 ⊗ₜ[k] _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 := by
  let e := TauCeti.MonoidAlgebra.scalarTensorBialgEquiv k (AlgebraicClosure k)
    (G := characterGroup σ)
  have h := (characterLatticeEquiv_apply_eq_iff k σ
    ((characterLatticeEquiv k σ).symm m) m).mp
      ((characterLatticeEquiv k σ).apply_symm_apply m)
  calc
    ((characterLatticeEquiv k σ).symm m).toMul.val =
        e.symm (e ((characterLatticeEquiv k σ).symm m).toMul.val) :=
      (e.symm_apply_apply _).symm
    _ = e.symm (_root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1) :=
      congrArg e.symm h
    _ = 1 ⊗ₜ[k] _root_.MonoidAlgebra.single (Multiplicative.ofAdd m) 1 :=
      TauCeti.MonoidAlgebra.scalarTensorBialgEquiv_symm_single k
        (AlgebraicClosure k) (Multiplicative.ofAdd m) 1

/-- The absolute-Galois action on the character lattice of a split torus is trivial. -/
@[simp]
theorem smul_eq_self (k : Type u) [Field k] (σ : Type u) [Finite σ]
    (γ : Field.absoluteGaloisGroup k)
    (x : CommHopfAlgCat.additiveCharacterGroup
      (DiagonalizableGroup.coordinateRing k (characterGroup σ)).obj) :
    γ • x = x := by
  apply Additive.toMul.injective
  -- Expose the generic additive action beneath the split-torus instance bridge.
  change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from γ) • x.toMul = x.toMul
  exact DiagonalizableGroup.smul_eq_self k (characterGroup σ) γ x.toMul

end SplitTorus

end TauCeti
