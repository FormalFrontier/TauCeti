/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Basic

/-!
# Continuity of the absolute-Galois action on geometric characters

For a commutative Hopf algebra `H` over a field `k`, the geometric character group
`X*(H)` carries the discrete topology. Its absolute-Galois action is continuous for the Krull
topology. Indeed, every element of the scalar extension `k̄ ⊗[k] H` is a finite sum of pure
tensors. The finitely many scalar coefficients lie in finite extensions of `k`, so their common
fixing subgroup is open and fixes the tensor. The same is therefore true for each group-like
element.

For tori, this makes the finite free character lattice constructed in
`TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice` a continuous discrete Galois module.

## Main declarations

* `TauCeti.CommHopfAlgCat.instGeometricCharacterGroupTopologicalSpace`: the discrete topology on
  geometric characters.
* `TauCeti.CommHopfAlgCat.isOpen_stabilizer_geometricCharacterGroup`: every character stabilizer
  is open.
* `TauCeti.CommHopfAlgCat.instGeometricCharacterGroupContinuousSMul`: continuity of the
  absolute-Galois action.
* `TauCeti.CommHopfAlgCat.isOpen_stabilizer_additiveCharacterGroup`: every additive-character
  stabilizer is open.
* `TauCeti.CommHopfAlgCat.instAdditiveCharacterGroupContinuousSMul`: continuity of the additive
  character-lattice action.

## References

See J. S. Milne, *Algebraic Groups* (2017), Definitions 12.14 and 12.17, for the character
lattice of a torus as a continuous Galois module.
-/

public section

open TensorProduct

namespace TauCeti

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

/-- The evaluation action of the opaque absolute-Galois-group wrapper on its algebraic closure. -/
private noncomputable local instance instGaloisAlgebraicClosureMulAction :
    MulAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k) where
  smul σ a := (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a
  one_smul a := by
    unfold Field.absoluteGaloisGroup
    rfl
  mul_smul σ τ a := by
    unfold Field.absoluteGaloisGroup at σ τ ⊢
    rfl

/-- The geometric character group carries its natural discrete topology. -/
noncomputable instance instGeometricCharacterGroupTopologicalSpace :
    TopologicalSpace (geometricCharacterGroup H) := ⊥

/-- The topology on the geometric character group is discrete. -/
instance instGeometricCharacterGroupDiscreteTopology :
    DiscreteTopology (geometricCharacterGroup H) := ⟨rfl⟩

private theorem isOpen_stabilizer_algebraicClosure (a : AlgebraicClosure k) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) a :
      Set (Field.absoluteGaloisGroup k)) := by
  change @IsOpen (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (Field.instTopologicalSpaceAbsoluteGaloisGroup k)
    (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) a : Set _)
  rw [show Field.instTopologicalSpaceAbsoluteGaloisGroup k =
    krullTopology k (AlgebraicClosure k) from rfl]
  exact stabilizer_isOpen_of_isIntegral a

private theorem isOpen_stabilizer_scalarExtension {A : Type u} [Semiring A] [Bialgebra k A]
    (x : AlgebraicClosure k ⊗[k] A) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      convert isOpen_univ
      ext σ
      simp only [Set.mem_univ, SetLike.mem_coe, MulAction.mem_stabilizer_iff, smul_zero]
  | tmul a x =>
      apply Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) a)
        (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) (a ⊗ₜ[k] x))
        ?_ (isOpen_stabilizer_algebraicClosure a)
      intro σ hσ
      rw [MulAction.mem_stabilizer_iff] at hσ ⊢
      change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a = a at hσ
      change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) •
        (a ⊗ₜ[k] x) = a ⊗ₜ[k] x
      rw [ScalarAut.smul_tmul, hσ]
  | add x y hx hy =>
      apply Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x ⊓
          MulAction.stabilizer (Field.absoluteGaloisGroup k) y)
        (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) (x + y))
        ?_ (hx.inter hy)
      intro σ hσ
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
        MulAction.mem_stabilizer_iff] at hσ
      rw [MulAction.mem_stabilizer_iff, smul_add, hσ.1, hσ.2]

/-- The stabilizer of every geometric character is open in the absolute Galois group. -/
theorem isOpen_stabilizer_geometricCharacterGroup (x : geometricCharacterGroup H) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x.val)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x)
    ?_ (isOpen_stabilizer_scalarExtension x.val)
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  apply _root_.GroupLike.val_injective
  rw [val_smul]
  change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) • x.val = x.val at hσ
  exact hσ

/-- The absolute-Galois action on geometric characters is continuous for the Krull topology and
the discrete topology on the character group. -/
noncomputable instance instGeometricCharacterGroupContinuousSMul :
    ContinuousSMul (Field.absoluteGaloisGroup k) (geometricCharacterGroup H) :=
  continuousSMul_iff_stabilizer_isOpen.mpr
    (isOpen_stabilizer_geometricCharacterGroup H)

/-- The stabilizer of every additive character is open in the absolute Galois group. -/
theorem isOpen_stabilizer_additiveCharacterGroup (x : additiveCharacterGroup H) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x.toMul)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x)
    ?_ (isOpen_stabilizer_geometricCharacterGroup H x.toMul)
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  change (σ • x).toMul = x.toMul
  rw [toMul_smul, hσ]

/-- The additive character group carries the continuous action transported from geometric
characters. -/
noncomputable instance instAdditiveCharacterGroupContinuousSMul :
    ContinuousSMul (Field.absoluteGaloisGroup k) (additiveCharacterGroup H) := by
  exact continuousSMul_iff_stabilizer_isOpen.mpr
    (isOpen_stabilizer_additiveCharacterGroup H)

end CommHopfAlgCat

end TauCeti
