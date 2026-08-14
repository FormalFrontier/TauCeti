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

* `TauCeti.CommHopfAlgCat.instTopologicalSpaceGeometricCharacterGroup`: the discrete topology on
  geometric characters.
* `TauCeti.CommHopfAlgCat.stabilizer_geometricCharacterGroup_isOpen`: every character stabilizer
  is open.
* `TauCeti.CommHopfAlgCat.instContinuousSMulGeometricCharacterGroup`: continuity of the
  absolute-Galois action.
* `TauCeti.CommHopfAlgCat.stabilizer_additiveCharacterGroup_isOpen`: every additive-character
  stabilizer is open.
* `TauCeti.CommHopfAlgCat.instContinuousSMulAdditiveCharacterGroup`: continuity of the additive
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

/-- Bridge the opaque absolute-Galois-group wrapper to Mathlib's evaluation action. -/
private noncomputable local instance instGaloisAlgebraicClosureMulAction :
    MulAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k) := by
  unfold Field.absoluteGaloisGroup
  exact AlgEquiv.applyMulSemiringAction.toDistribMulAction.toMulAction

/-- The geometric character group carries its natural discrete topology. -/
noncomputable instance instTopologicalSpaceGeometricCharacterGroup :
    TopologicalSpace (geometricCharacterGroup H) := ⊥

/-- The topology on the geometric character group is discrete. -/
instance instDiscreteTopologyGeometricCharacterGroup :
    DiscreteTopology (geometricCharacterGroup H) := ⟨rfl⟩

/-- Evaluation through the absolute-Galois wrapper agrees with the underlying algebra
equivalence. -/
private theorem smul_algebraicClosure (σ : Field.absoluteGaloisGroup k)
    (a : AlgebraicClosure k) :
    σ • a = (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a := by
  unfold Field.absoluteGaloisGroup at σ ⊢
  exact AlgEquiv.smul_def σ a

/-- The scalar-extension action crosses the absolute-Galois wrapper on pure tensors. -/
private theorem smul_tmul_absoluteGalois {A : Type u} [Semiring A] [Algebra k A]
    (σ : Field.absoluteGaloisGroup k) (a : AlgebraicClosure k) (x : A) :
    σ • (a ⊗ₜ[k] x) =
      (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) a ⊗ₜ[k] x := by
  unfold Field.absoluteGaloisGroup at σ ⊢
  exact ScalarAut.smul_tmul σ a x

/-- Taking the value of a group-like element crosses the absolute-Galois wrapper. -/
private theorem val_smul_groupLike {A : Type u} [Semiring A] [Bialgebra k A]
    (σ : Field.absoluteGaloisGroup k)
    (x : _root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    (σ • x).val = σ • x.val := by
  unfold Field.absoluteGaloisGroup at σ ⊢
  exact ScalarAut.val_smul σ x

/-- Taking `toMul` of an additive group-like element crosses the absolute-Galois wrapper. -/
private theorem toMul_smul_additiveGroupLike {A : Type u} [Semiring A] [Bialgebra k A]
    (σ : Field.absoluteGaloisGroup k)
    (x : Additive (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))) :
    (σ • x).toMul = σ • x.toMul := by
  unfold Field.absoluteGaloisGroup at σ ⊢
  exact ScalarAut.toMul_smul σ x

private theorem stabilizer_algebraicClosure_isOpen (a : AlgebraicClosure k) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) a :
      Set (Field.absoluteGaloisGroup k)) := by
  -- The wrapper's derived topology is definitionally the Krull topology, but Mathlib exposes no
  -- propositional bridge lemma, so isolate that conversion here.
  change @IsOpen (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (krullTopology k (AlgebraicClosure k))
    (MulAction.stabilizer (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) a : Set _)
  exact stabilizer_isOpen_of_isIntegral a

private theorem stabilizer_scalarExtension_isOpen {A : Type u} [Semiring A] [Algebra k A]
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
        ?_ (stabilizer_algebraicClosure_isOpen a)
      intro σ hσ
      rw [MulAction.mem_stabilizer_iff] at hσ ⊢
      rw [smul_algebraicClosure] at hσ
      rw [smul_tmul_absoluteGalois, hσ]
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

/-- The stabilizer of every group-like element after scalar extension is open. -/
theorem stabilizer_groupLike_isOpen {A : Type u} [Semiring A] [Bialgebra k A]
    (x : _root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x.val)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x)
    ?_ (stabilizer_scalarExtension_isOpen x.val)
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  apply _root_.GroupLike.val_injective
  rw [val_smul_groupLike, hσ]

/-- The stabilizer of every geometric character is open in the absolute Galois group. -/
theorem stabilizer_geometricCharacterGroup_isOpen (x : geometricCharacterGroup H) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) :=
  stabilizer_groupLike_isOpen x

/-- The absolute-Galois action on scalar-extended group-like elements is continuous whenever
they carry the discrete topology. -/
theorem continuousSMul_groupLike {A : Type u} [Semiring A] [Bialgebra k A]
    [TopologicalSpace (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))]
    [DiscreteTopology (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))] :
    ContinuousSMul (Field.absoluteGaloisGroup k)
      (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :=
  continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_groupLike_isOpen

/-- The absolute-Galois action on geometric characters is continuous for the Krull topology and
the discrete topology on the character group. -/
noncomputable instance instContinuousSMulGeometricCharacterGroup :
    ContinuousSMul (Field.absoluteGaloisGroup k) (geometricCharacterGroup H) :=
  continuousSMul_groupLike

/-- The stabilizer of every additive group-like element after scalar extension is open. -/
theorem stabilizer_additiveGroupLike_isOpen {A : Type u} [Semiring A] [Bialgebra k A]
    (x : Additive (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x.toMul)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x)
    ?_ (stabilizer_groupLike_isOpen x.toMul)
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  apply Additive.toMul.injective
  rw [toMul_smul_additiveGroupLike, hσ]

/-- The stabilizer of every additive character is open in the absolute Galois group. -/
theorem stabilizer_additiveCharacterGroup_isOpen (x : additiveCharacterGroup H) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) :=
  stabilizer_additiveGroupLike_isOpen x

/-- The absolute-Galois action on additive scalar-extended group-like elements is continuous
whenever they carry the discrete topology. -/
theorem continuousSMul_additiveGroupLike {A : Type u} [Semiring A] [Bialgebra k A]
    [TopologicalSpace (Additive (_root_.GroupLike (AlgebraicClosure k)
      (AlgebraicClosure k ⊗[k] A)))]
    [DiscreteTopology (Additive (_root_.GroupLike (AlgebraicClosure k)
      (AlgebraicClosure k ⊗[k] A)))] :
    ContinuousSMul (Field.absoluteGaloisGroup k)
      (Additive (_root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A))) :=
  continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_additiveGroupLike_isOpen

/-- The additive character group carries the continuous action transported from geometric
characters. -/
noncomputable instance instContinuousSMulAdditiveCharacterGroup :
    ContinuousSMul (Field.absoluteGaloisGroup k) (additiveCharacterGroup H) :=
  continuousSMul_additiveGroupLike

end CommHopfAlgCat

end TauCeti
