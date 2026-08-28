/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus
public import TauCeti.Algebra.Lie.UniversalEnveloping.MatrixRepresentation
public import TauCeti.Algebra.Module.Rat
public import TauCeti.LinearAlgebra.Eigenspace.Binomial
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
public import TauCeti.RingTheory.Binomial
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan

/-!
# The full-weight Chevalley carrier of type `C`

For positive rank `n + 1`, the symplectic Lie algebra `sp₂ₙ₊₂` acts on its standard module
`(Fin (n + 1) ⊕ Fin (n + 1)) → ℚ`. This file records its Bourbaki-numbered simple Chevalley
generators, the standard integral lattice, and the standard weights, then feeds those data into
the Kostant toral-closure construction. The result is an explicit affine group scheme over `ℤ`
whose split torus has the full weight lattice of type `C`.

For a nonfinal node `i`, the raising generator is

```text
E_{i,i+1} - E_{-(i+1),-i},
```

and the final raising generator is `E_{n,-n}`. The lowering generators are their transposed
counterparts. All of these square to zero in the standard representation. Their divided powers
therefore preserve the coordinate `ℤ`-lattice, while the Cartan binomial operators preserve it
because the coordinate vectors have integral weights.

The weights of the upper coordinates are `ε_i` and those of the lower coordinates are `-ε_i`.
In simple-coroot coordinates, the map

```text
(x₀, ..., xₙ) ↦ (x₀ - x₁, ..., xₙ₋₁ - xₙ, xₙ)
```

is unimodular. Thus the standard weights generate the whole character lattice, unlike the roots
of the adjoint carrier. This makes the rank-`n + 1` split torus a closed subgroup of the carrier.

This file does not prove reductivity or maximality of the torus, and it does not identify this
carrier with the separately constructed symplectic group scheme. Those root-datum and generation
statements remain part of Layer 9 of the reductive-groups roadmap. No finite or simple group is
asserted here.

## Main definitions

* `TauCeti.SpStd.rootGenerator` and `TauCeti.SpStd.cartanGenerator`: the numbered type-`C`
  Chevalley generators in the symplectic Lie algebra.
* `TauCeti.SpStd.rep`: the standard representation, extended to the enveloping algebra.
* `TauCeti.SpStd.lattice`, `TauCeti.SpStd.latticeBasis`, and `TauCeti.SpStd.weight`: the standard
  admissible lattice and its weights.
* `TauCeti.SpStd.groupScheme`, `TauCeti.SpStd.rootSubgroup`, and `TauCeti.SpStd.weightTorus`: the
  full-weight Kostant carrier and its pinned generating morphisms.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4, 7.1, and 11.3.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27, and
  *Linear Algebraic Groups*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.

The organization of the carrier API and its applications of the generic Kostant infrastructure
follow the type-`A` standard-carrier implementation in
[TauCetiProject/TauCeti#4603](https://github.com/TauCetiProject/TauCeti/pull/4603), commits
`998d5984` and `f4239801`; the symplectic matrices, doubled coordinate action, type-`C` weight
calculation, and their proofs are specific to this file.

This advances the Chevalley--Demazure construction, pinning, and root-subgroup targets of Layer 9
of `TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, which needs a simply connected pinned carrier for every
valid Lie-type family.
-/

public section

open scoped Matrix

namespace TauCeti.SpStd

open LieAlgebra.Symplectic
open scoped TensorProduct
open scoped CategoryTheory.MonObj

attribute [local instance] TauCeti.moduleNNRat

variable (n : ℕ)

private theorem fromBlocks_mem_sp (P Q S : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hQ : Qᵀ = Q) (hS : Sᵀ = S) :
    _root_.Matrix.fromBlocks P Q S (-Pᵀ) ∈ sp (Fin (n + 1)) ℚ := by
  rw [sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  simp only [_root_.Matrix.IsSkewAdjoint, _root_.Matrix.IsAdjointPair, _root_.Matrix.J,
    _root_.Matrix.fromBlocks_transpose, _root_.Matrix.transpose_neg,
    _root_.Matrix.transpose_transpose, _root_.Matrix.fromBlocks_multiply,
    _root_.Matrix.mul_zero, _root_.Matrix.mul_one, _root_.Matrix.zero_mul,
    _root_.Matrix.one_mul, add_zero, zero_add, _root_.Matrix.neg_mul, _root_.Matrix.mul_neg]
  rw [hQ, hS]
  ext i j
  cases i <;> cases j <;> simp [_root_.Matrix.fromBlocks]

/-- The successor of a nonfinal simple-root index. -/
def next (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : Fin (n + 1) :=
  (i.castPred hi).succ

/-- The value of the successor of a nonfinal simple-root index. -/
@[simp] theorem val_next (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    (next n i hi).val = i.val + 1 := (rfl)

/-- A nonfinal index precedes its successor. -/
theorem lt_next (i : Fin (n + 1)) (hi : i ≠ Fin.last n) : i < next n i hi := by
  exact Fin.lt_succ_castPred hi

/-- The upper-left matrix unit for a nonfinal raising generator. -/
private def shortPositiveBlock (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  _root_.Matrix.single i (next n i hi) 1

/-- The upper-left matrix unit for a nonfinal lowering generator. -/
private def shortNegativeBlock (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  _root_.Matrix.single (next n i hi) i 1

/-- The matrix of the raising generator attached to a simple root of type `C_(n+1)`. -/
def positiveRootMatrix (i : Fin (n + 1)) :
    _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ :=
  if hi : i = Fin.last n then
    _root_.Matrix.fromBlocks 0 (_root_.Matrix.single i i 1) 0 0
  else
    _root_.Matrix.fromBlocks (shortPositiveBlock n i hi) 0 0 (-(shortPositiveBlock n i hi)ᵀ)

/-- The matrix of the lowering generator attached to a simple root of type `C_(n+1)`. -/
def negativeRootMatrix (i : Fin (n + 1)) :
    _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ :=
  if hi : i = Fin.last n then
    _root_.Matrix.fromBlocks 0 0 (_root_.Matrix.single i i 1) 0
  else
    _root_.Matrix.fromBlocks (shortNegativeBlock n i hi) 0 0 (-(shortNegativeBlock n i hi)ᵀ)

theorem positiveRootMatrix_mem_sp (i : Fin (n + 1)) :
    positiveRootMatrix n i ∈ sp (Fin (n + 1)) ℚ := by
  rw [positiveRootMatrix]
  split_ifs with hi
  · apply fromBlocks_mem_sp <;> simp
  · apply fromBlocks_mem_sp <;> simp

theorem negativeRootMatrix_mem_sp (i : Fin (n + 1)) :
    negativeRootMatrix n i ∈ sp (Fin (n + 1)) ℚ := by
  rw [negativeRootMatrix]
  split_ifs with hi
  · apply fromBlocks_mem_sp <;> simp
  · apply fromBlocks_mem_sp <;> simp

/-! ## Weights and Cartan generators -/

/-- The integral weight of a standard coordinate vector. Upper coordinates have weight `ε_a`
and lower coordinates have weight `-ε_a`. -/
def weight (a : Fin (n + 1) ⊕ Fin (n + 1)) : Fin (n + 1) → ℤ :=
  let x := (Equiv.boolProdEquivSum (Fin (n + 1))).symm a
  DynkinType.TypeC.signedWeight (x.2, x.1)

@[simp] theorem weight_inl (a i : Fin (n + 1)) :
    weight n (.inl a) i = DynkinType.TypeC.weight (n + 1) a i := by
  simp only [weight, Equiv.boolProdEquivSum_symm_apply, Sum.elim_inl,
    DynkinType.TypeC.signedWeight_false]

@[simp] theorem weight_inr (a i : Fin (n + 1)) :
    weight n (.inr a) i = -DynkinType.TypeC.weight (n + 1) a i := by
  simp only [weight, Equiv.boolProdEquivSum_symm_apply, Sum.elim_inr,
    DynkinType.TypeC.signedWeight_true, Pi.neg_apply]

/-- The diagonal matrix of the `i`-th simple coroot in the standard symplectic representation. -/
def cartanMatrix (i : Fin (n + 1)) :
    _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ :=
  _root_.Matrix.diagonal fun k => (weight n k i : ℚ)

theorem cartanMatrix_mem_sp (i : Fin (n + 1)) :
    cartanMatrix n i ∈ sp (Fin (n + 1)) ℚ := by
  have hblocks : cartanMatrix n i =
      _root_.Matrix.fromBlocks
        (_root_.Matrix.diagonal fun a : Fin (n + 1) =>
          (DynkinType.TypeC.weight (n + 1) a i : ℚ)) 0 0
        (-_root_.Matrix.diagonal fun a : Fin (n + 1) =>
          (DynkinType.TypeC.weight (n + 1) a i : ℚ)) := by
    ext a b
    cases a <;> cases b <;>
      simp [cartanMatrix, _root_.Matrix.fromBlocks, _root_.Matrix.diagonal_apply]
  rw [hblocks]
  simpa using fromBlocks_mem_sp n
    (_root_.Matrix.diagonal fun a : Fin (n + 1) => (DynkinType.TypeC.weight (n + 1) a i : ℚ)) 0 0
    (by simp) (by simp)

/-- The Bourbaki-numbered raising and lowering generators of `sp₂ₙ₊₂`. -/
def rootGenerator : Fin (n + 1) ⊕ Fin (n + 1) → sp (Fin (n + 1)) ℚ
  | .inl i => ⟨positiveRootMatrix n i, positiveRootMatrix_mem_sp n i⟩
  | .inr i => ⟨negativeRootMatrix n i, negativeRootMatrix_mem_sp n i⟩

/-- The Bourbaki-numbered Cartan generators in the standard symplectic representation. -/
def cartanGenerator (i : Fin (n + 1)) : sp (Fin (n + 1)) ℚ :=
  ⟨cartanMatrix n i, cartanMatrix_mem_sp n i⟩

@[simp] theorem val_rootGenerator_inl (i : Fin (n + 1)) :
    (rootGenerator n (.inl i) :
      _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) =
        positiveRootMatrix n i := (rfl)

@[simp] theorem val_rootGenerator_inr (i : Fin (n + 1)) :
    (rootGenerator n (.inr i) :
      _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) =
        negativeRootMatrix n i := (rfl)

@[simp] theorem val_cartanGenerator (i : Fin (n + 1)) :
    (cartanGenerator n i :
      _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) =
        cartanMatrix n i := (rfl)

/-- The standard representation of the symplectic Lie algebra, extended to its enveloping
algebra. -/
noncomputable abbrev rep :
    _root_.UniversalEnvelopingAlgebra ℚ (sp (Fin (n + 1)) ℚ) →ₐ[ℚ]
      Module.End ℚ ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :=
  LieSubalgebra.matrixRepresentation (sp (Fin (n + 1)) ℚ)

theorem rep_ι_apply (x : sp (Fin (n + 1)) ℚ)
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v =
      (x : _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) *ᵥ v :=
  LieSubalgebra.matrixRepresentation_ι_apply _ x v

/-- A Cartan generator acts diagonally on every standard-module vector with the recorded
coordinate weight. -/
@[simp] theorem rep_cartanGenerator_apply (i : Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ)
    (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n ((_root_.UniversalEnvelopingAlgebra.mkAlgHom ℚ _)
      (_root_.TensorAlgebra.ι ℚ (cartanGenerator n i))) v a =
      (weight n a i : ℚ) * v a := by
  rw [← _root_.UniversalEnvelopingAlgebra.ι_apply, rep_ι_apply, val_cartanGenerator,
    cartanMatrix, _root_.Matrix.mulVec_diagonal]

/-- A coordinate vector on which a numbered root generator is nonzero with coefficient one. -/
def rootSource : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => if hi : i = Fin.last n then .inr i else .inl (next n i hi)
  | .inr i => .inl i

/-- The coordinate vector obtained from `rootSource` by applying its numbered root generator. -/
def rootTarget : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => .inl i
  | .inr i => if hi : i = Fin.last n then .inr i else .inl (next n i hi)

@[simp] theorem rootSource_inl_last :
    rootSource n (.inl (Fin.last n)) = .inr (Fin.last n) := by
  simp [rootSource]

@[simp] theorem rootSource_inl_of_ne (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootSource n (.inl i) = .inl (next n i hi) := by
  simp [rootSource, hi]

@[simp] theorem rootSource_inr (i : Fin (n + 1)) :
    rootSource n (.inr i) = .inl i := (rfl)

@[simp] theorem rootTarget_inl (i : Fin (n + 1)) :
    rootTarget n (.inl i) = .inl i := (rfl)

@[simp] theorem rootTarget_inr_last :
    rootTarget n (.inr (Fin.last n)) = .inr (Fin.last n) := by
  simp [rootTarget]

@[simp] theorem rootTarget_inr_of_ne (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootTarget n (.inr i) = .inl (next n i hi) := by
  simp [rootTarget, hi]

/-- The root character of a numbered generator, calculated as target weight minus source weight. -/
def rootWeight (k : Fin (n + 1) ⊕ Fin (n + 1)) (j : Fin (n + 1)) : ℤ :=
  weight n (rootTarget n k) j - weight n (rootSource n k) j

/-- The weight difference across a raising generator is the corresponding simple root in the
canonical simply connected type-`C` root datum. -/
theorem rootWeight_inl_eq_root (i : Fin (n + 1)) :
    rootWeight n (.inl i) =
      (DynkinType.typeCSimplyConnectedRootDatum (n + 1)).root
        (DynkinType.typeCSimpleIndex (n + 1) i) := by
  rw [DynkinType.root_typeCSimpleIndex]
  funext j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rootWeight, rootTarget_inl, rootSource_inl_last]
    simp only [weight_inl, weight_inr, DynkinType.TypeC.weight_apply, CartanMatrix.C,
      _root_.Matrix.of_apply, Fin.val_last, Nat.add_sub_cancel]
    split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> omega
  · rw [rootWeight, rootTarget_inl, rootSource_inl_of_ne n i hi]
    simp only [weight_inl, DynkinType.TypeC.weight_apply, CartanMatrix.C, _root_.Matrix.of_apply]
    have hinext : i.val + 1 = (next n i hi).val := by
      simp [next]
    split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

/-- The roots of the raising generators are the rows of the type-`C` Cartan matrix. -/
@[simp] theorem rootWeight_inl (i j : Fin (n + 1)) :
    rootWeight n (.inl i) j = CartanMatrix.C (n + 1) i j := by
  rw [rootWeight_inl_eq_root, DynkinType.root_typeCSimpleIndex]

/-- The roots of the lowering generators are the negatives of the rows of the type-`C` Cartan
matrix. -/
@[simp] theorem rootWeight_inr (i j : Fin (n + 1)) :
    rootWeight n (.inr i) j = -CartanMatrix.C (n + 1) i j := by
  rw [← rootWeight_inl n i j, rootWeight, rootWeight, rootTarget_inl, rootSource_inr]
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rootTarget_inr_last, rootSource_inl_last]
    simp only [weight_inr, weight_inl]
    ring
  · rw [rootTarget_inr_of_ne n i hi, rootSource_inl_of_ne n i hi]
    simp only [weight_inl]
    ring

/-- The final raising matrix is a single off-diagonal matrix unit. -/
theorem positiveRootMatrix_last :
    positiveRootMatrix n (Fin.last n) =
      _root_.Matrix.single (.inl (Fin.last n)) (.inr (Fin.last n)) 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [positiveRootMatrix, _root_.Matrix.fromBlocks, _root_.Matrix.single_apply]

/-- A nonfinal raising matrix is the difference of its upper and lower matrix units. -/
theorem positiveRootMatrix_of_ne (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    positiveRootMatrix n i =
      _root_.Matrix.single (.inl i) (.inl (next n i hi)) 1 -
        _root_.Matrix.single (.inr (next n i hi)) (.inr i) 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [positiveRootMatrix, hi, shortPositiveBlock, _root_.Matrix.fromBlocks,
      _root_.Matrix.single_apply]

/-- The final lowering matrix is a single off-diagonal matrix unit. -/
theorem negativeRootMatrix_last :
    negativeRootMatrix n (Fin.last n) =
      _root_.Matrix.single (.inr (Fin.last n)) (.inl (Fin.last n)) 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [negativeRootMatrix, _root_.Matrix.fromBlocks, _root_.Matrix.single_apply]

/-- A nonfinal lowering matrix is the difference of its upper and lower matrix units. -/
theorem negativeRootMatrix_of_ne (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    negativeRootMatrix n i =
      _root_.Matrix.single (.inl (next n i hi)) (.inl i) 1 -
        _root_.Matrix.single (.inr i) (.inr (next n i hi)) 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [negativeRootMatrix, hi, shortNegativeBlock, _root_.Matrix.fromBlocks,
      _root_.Matrix.single_apply]

/-- The matrix commutator of a Cartan generator with a raising generator. -/
private theorem cartanMatrix_commutator_positiveRootMatrix (i j : Fin (n + 1)) :
    ⁅cartanMatrix n j, positiveRootMatrix n i⁆ =
      ((rootWeight n (.inl i) j : ℤ) : ℚ) • positiveRootMatrix n i := by
  let _ : LieRing (_root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) := LieRing.ofAssociativeRing
  rw [cartanMatrix]
  by_cases hi : i = Fin.last n
  · subst hi
    rw [positiveRootMatrix_last,
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _)]
    simp [rootWeight]
  · rw [positiveRootMatrix_of_ne n i hi, lie_sub,
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _),
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _)]
    rw [rootWeight, rootTarget_inl, rootSource_inl_of_ne n i hi]
    simp only [weight_inl, _root_.Matrix.smul_single, smul_eq_mul, mul_one]
    rw [smul_sub]
    congr 1
    · ext a b
      simp [_root_.Matrix.single_apply]
    · ext a b
      simp [_root_.Matrix.single_apply]
      split_ifs <;> ring

/-- The matrix commutator of a Cartan generator with a lowering generator. -/
private theorem cartanMatrix_commutator_negativeRootMatrix (i j : Fin (n + 1)) :
    ⁅cartanMatrix n j, negativeRootMatrix n i⁆ =
      ((rootWeight n (.inr i) j : ℤ) : ℚ) • negativeRootMatrix n i := by
  let _ : LieRing (_root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) := LieRing.ofAssociativeRing
  rw [cartanMatrix]
  by_cases hi : i = Fin.last n
  · subst hi
    rw [negativeRootMatrix_last,
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _)]
    simp [rootWeight]
  · rw [negativeRootMatrix_of_ne n i hi, lie_sub,
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _),
      lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _)]
    rw [rootWeight, rootTarget_inr_of_ne n i hi, rootSource_inr]
    simp only [weight_inl, _root_.Matrix.smul_single, smul_eq_mul, mul_one]
    rw [smul_sub]
    congr 1
    · ext a b
      simp [_root_.Matrix.single_apply]
    · ext a b
      simp [_root_.Matrix.single_apply]
      split_ifs <;> ring

/-- The numbered Cartan generators act on the root generators through their recorded root
characters, equivalently through the type-`C` Cartan matrix and its negatives. -/
theorem lie_cartanGenerator_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1))
    (j : Fin (n + 1)) :
    ⁅cartanGenerator n j, rootGenerator n k⁆ =
      ((rootWeight n k j : ℤ) : ℚ) • rootGenerator n k := by
  let _ : LieRing (_root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1))
      (Fin (n + 1) ⊕ Fin (n + 1)) ℚ) := LieRing.ofAssociativeRing
  refine Subtype.ext ?_
  cases k with
  | inl i =>
      rw [LieSubalgebra.coe_bracket, val_cartanGenerator, Submodule.coe_smul,
        val_rootGenerator_inl]
      exact cartanMatrix_commutator_positiveRootMatrix n i j
  | inr i =>
      rw [LieSubalgebra.coe_bracket, val_cartanGenerator, Submodule.coe_smul,
        val_rootGenerator_inr]
      exact cartanMatrix_commutator_negativeRootMatrix n i j

/-- The action of a numbered simple root generator on the standard module, written in coordinate
vectors. -/
def rootAction (k : Fin (n + 1) ⊕ Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ :=
  match k with
  | .inl i =>
      if hi : i = Fin.last n then
        v (.inr i) • Pi.single (.inl i) 1
      else
        v (.inl (next n i hi)) • Pi.single (.inl i) 1 -
          v (.inr i) • Pi.single (.inr (next n i hi)) 1
  | .inr i =>
      if hi : i = Fin.last n then
        v (.inl i) • Pi.single (.inr i) 1
      else
        v (.inl i) • Pi.single (.inl (next n i hi)) 1 -
          v (.inr (next n i hi)) • Pi.single (.inr i) 1

/-- The standard action of a numbered root generator is the explicit coordinate operation
`rootAction`. -/
theorem rep_rootGenerator_apply (k : Fin (n + 1) ⊕ Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v = rootAction n k v := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [val_rootGenerator_inl, positiveRootMatrix, rootAction]
      split_ifs with hi
      · funext x
        cases x <;>
          simp [_root_.Matrix.fromBlocks_mulVec, _root_.Matrix.single_mulVec_eq, Pi.single_apply]
      · funext x
        cases x <;>
          simp [_root_.Matrix.fromBlocks_mulVec, shortPositiveBlock, _root_.Matrix.single_mulVec_eq,
            _root_.Matrix.transpose_single, _root_.Matrix.neg_mulVec, Pi.single_apply, mul_comm]
  | inr i =>
      rw [val_rootGenerator_inr, negativeRootMatrix, rootAction]
      split_ifs with hi
      · funext x
        cases x <;>
          simp [_root_.Matrix.fromBlocks_mulVec, _root_.Matrix.single_mulVec_eq, Pi.single_apply]
      · funext x
        cases x <;>
          simp [_root_.Matrix.fromBlocks_mulVec, shortNegativeBlock, _root_.Matrix.single_mulVec_eq,
            _root_.Matrix.transpose_single, _root_.Matrix.neg_mulVec, Pi.single_apply, mul_comm]

/-- Applying a numbered root generator twice in the standard representation gives zero. -/
theorem rep_rootGenerator_rep_rootGenerator_eq_zero
    (k : Fin (n + 1) ⊕ Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))
      (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v) = 0 := by
  rw [rep_rootGenerator_apply, rep_rootGenerator_apply]
  cases k with
  | inl i =>
      rw [rootAction]
      split_ifs with hi
      · simp [rootAction, hi]
      · simp [rootAction, hi, (lt_next n i hi).ne,
          (lt_next n i hi).ne']
  | inr i =>
      rw [rootAction]
      split_ifs with hi
      · simp [rootAction, hi]
      · simp [rootAction, hi, (lt_next n i hi).ne,
          (lt_next n i hi).ne']

/-- Every numbered root generator squares to zero in the standard representation. -/
theorem rep_rootGenerator_sq_eq_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) ^ 2 = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [pow_two, Module.End.mul_apply, rep_rootGenerator_rep_rootGenerator_eq_zero,
    LinearMap.zero_apply]

/-- Every numbered root generator acts nilpotently on the standard module. -/
theorem isNilpotent_rep_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsNilpotent (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))) :=
  ⟨2, rep_rootGenerator_sq_eq_zero n k⟩

/-! ## Weight vectors and the standard admissible lattice -/

/-- Every standard coordinate vector is a weight vector for the numbered Cartan generators. -/
theorem isCartanWeightVector_single (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator n) (rep n)
      (weight n a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (cartanGenerator n) (rep n)).mpr fun i => ?_
  rw [rep_ι_apply, val_cartanGenerator, cartanMatrix, _root_.Matrix.diagonal_mulVec_single]
  rw [← Pi.single_smul']
  simp

/-- The standard coordinate `ℤ`-lattice in the symplectic module. -/
def lattice : Submodule ℤ ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℚ (Fin (n + 1) ⊕ Fin (n + 1))))

/-- A vector is in the standard lattice exactly when all its coordinates are integers. -/
@[simp] theorem mem_lattice_iff {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} :
    v ∈ lattice n ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a := by
  rw [lattice, Module.Basis.mem_span_iff_repr_mem]
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom, Set.mem_range]

theorem single_mem_lattice (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    Pi.single a (1 : ℚ) ∈ lattice n := by
  rw [lattice, ← Pi.basisFun_apply]
  exact Submodule.subset_span (Set.mem_range_self a)

/-- The coordinate basis of the standard lattice, enumerated by a finite interval as required by
the matrix carrier construction. -/
noncomputable def latticeBasis :
    Module.Basis (Fin ((n + 1) + (n + 1))) ℤ (lattice n).toAddSubgroup :=
  ((Pi.basisFun ℚ (Fin (n + 1) ⊕ Fin (n + 1))).restrictScalars ℤ).reindex
    finSumFinEquiv

@[simp] theorem coe_latticeBasis (a : Fin ((n + 1) + (n + 1))) :
    ((latticeBasis n a : (lattice n).toAddSubgroup) :
      (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) = Pi.single (finSumFinEquiv.symm a) 1 := by
  unfold latticeBasis lattice
  rw [Module.Basis.reindex_apply, Module.Basis.restrictScalars_apply, Pi.basisFun_apply]

/-- The weight attached to the enumerated coordinate basis. -/
def basisWeight (a : Fin ((n + 1) + (n + 1))) : Fin (n + 1) → ℤ :=
  weight n (finSumFinEquiv.symm a)

/-- A numbered root generator preserves the standard lattice. -/
theorem rep_rootGenerator_mem_lattice (k : Fin (n + 1) ⊕ Fin (n + 1))
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v ∈ lattice n := by
  rw [rep_rootGenerator_apply]
  cases k with
  | inl i =>
      rw [rootAction]
      split_ifs with hi
      · obtain ⟨z, hz⟩ := (mem_lattice_iff n).1 hv (.inr i)
        rw [← hz, Int.cast_smul_eq_zsmul]
        exact zsmul_mem (single_mem_lattice n _) z
      · obtain ⟨z₁, hz₁⟩ := (mem_lattice_iff n).1 hv (.inl (next n i hi))
        obtain ⟨z₂, hz₂⟩ := (mem_lattice_iff n).1 hv (.inr i)
        rw [← hz₁, ← hz₂, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact sub_mem (zsmul_mem (single_mem_lattice n _) z₁)
          (zsmul_mem (single_mem_lattice n _) z₂)
  | inr i =>
      rw [rootAction]
      split_ifs with hi
      · obtain ⟨z, hz⟩ := (mem_lattice_iff n).1 hv (.inl i)
        rw [← hz, Int.cast_smul_eq_zsmul]
        exact zsmul_mem (single_mem_lattice n _) z
      · obtain ⟨z₁, hz₁⟩ := (mem_lattice_iff n).1 hv (.inl i)
        obtain ⟨z₂, hz₂⟩ := (mem_lattice_iff n).1 hv (.inr (next n i hi))
        rw [← hz₁, ← hz₂, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
        exact sub_mem (zsmul_mem (single_mem_lattice n _) z₁)
          (zsmul_mem (single_mem_lattice n _) z₂)

/-- Every divided power of a numbered root generator preserves the standard lattice. -/
theorem rep_dividedPower_rootGenerator_mem_lattice (k : Fin (n + 1) ⊕ Fin (n + 1)) (m : ℕ)
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n (Associative.dividedPower m
      (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))) v ∈ lattice n := by
  rw [Associative.map_dividedPower]
  match m with
  | 0 => rwa [Associative.dividedPower_zero, Module.End.one_apply]
  | 1 => rw [Associative.dividedPower_one]; exact rep_rootGenerator_mem_lattice n k hv
  | m + 2 =>
      rw [Associative.dividedPower_def,
        pow_eq_zero_of_le (m := 2) (by omega) (rep_rootGenerator_sq_eq_zero n k), smul_zero,
        LinearMap.zero_apply]
      exact zero_mem _

/-- Every Cartan binomial operator preserves the standard lattice. -/
theorem rep_ringChoose_cartanGenerator_mem_lattice (i : Fin (n + 1)) (m : ℕ)
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator n i)) m) v ∈
      lattice n := by
  rw [lattice] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      rw [Pi.basisFun_apply, Ring.map_choose]
      have hweight := (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
        (cartanGenerator n) (rep n)).1 (isCartanWeightVector_single n a) i
      rw [ringChoose_end_apply_of_apply_eq_smul hweight m, TauCeti.Ring.choose_intCast,
        Int.cast_smul_eq_zsmul ℚ]
      exact Submodule.smul_mem _ _ (single_mem_lattice n a)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul z x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ z hx

/-- The standard coordinate lattice is stable under the Kostant integral form. -/
theorem rep_kostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (sp (Fin (n + 1)) ℚ)}
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm (rootGenerator n)
      (cartanGenerator n))
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n u v ∈ lattice n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem (rootGenerator n) (cartanGenerator n)
    (rep n) (lattice n)
    (fun k m _ hv => rep_dividedPower_rootGenerator_mem_lattice n k m hv)
    (fun i m _ hv => rep_ringChoose_cartanGenerator_mem_lattice n i m hv) u hu hv

/-! ## The full weight lattice -/

/-- The upper standard weights generate every coordinate character. -/
private theorem single_mem_span_range_weight (a : Fin (n + 1)) :
    Pi.single a (1 : ℤ) ∈ Submodule.span ℤ (Set.range (weight n)) := by
  induction a using Fin.induction with
  | zero =>
      have h : weight n (.inl (0 : Fin (n + 1))) ∈
          Submodule.span ℤ (Set.range (weight n)) :=
        Submodule.subset_span (Set.mem_range_self _)
      convert h using 1
      funext i
      by_cases hi : i = 0
      · subst i
        simp only [weight_inl, DynkinType.TypeC.weight_apply, Pi.single_eq_same, Fin.val_zero,
          ↓reduceIte, zero_add, Nat.zero_ne_add_one, sub_zero]
      · have hval : (i : ℕ) ≠ 0 := by
          intro hval
          apply hi
          exact Fin.ext hval
        have hval' : (0 : ℕ) ≠ (i : ℕ) := Ne.symm hval
        simp only [weight_inl, DynkinType.TypeC.weight_apply, Pi.single_eq_of_ne hi,
          Fin.val_zero, hval', ↓reduceIte, Nat.zero_ne_add_one, sub_self]
  | succ a ih =>
      have h := add_mem
        (Submodule.subset_span (s := Set.range (weight n))
          (Set.mem_range_self (Sum.inl a.succ))) ih
      convert h using 1
      funext i
      simp only [weight_inl, DynkinType.TypeC.weight_apply, Pi.single_apply, Pi.add_apply,
        Fin.val_succ]
      split_ifs <;> simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at * <;> omega

/-- The weights of the standard symplectic module span the full character lattice. -/
theorem span_range_weight_eq_top : Submodule.span ℤ (Set.range (weight n)) = ⊤ := by
  apply top_unique
  intro x _
  rw [← (Pi.basisFun ℤ (Fin (n + 1))).sum_repr x]
  apply Submodule.sum_mem
  intro a _
  rw [Pi.basisFun_apply]
  exact Submodule.smul_mem _ _ (single_mem_span_range_weight n a)

/-- Enumerating the coordinate basis does not change the span of its weights. -/
theorem span_range_basisWeight_eq_top : Submodule.span ℤ (Set.range (basisWeight n)) = ⊤ := by
  have hrange : Set.range (basisWeight n) = Set.range (weight n) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, rfl⟩
      exact ⟨finSumFinEquiv.symm a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨finSumFinEquiv a, by rw [basisWeight, Equiv.symm_apply_apply]⟩
  rw [hrange]
  exact span_range_weight_eq_top n

/-! ## The pinned carrier -/

section Carrier

open AlgebraicGeometry CategoryTheory

attribute [local instance high] Algebra.toModule

/-- Every coordinate basis vector of the standard lattice is a Cartan weight vector. -/
theorem isCartanWeightVector_latticeBasis (a : Fin ((n + 1) + (n + 1))) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator n) (rep n)
      (basisWeight n a)
      ((latticeBasis n a : (lattice n).toAddSubgroup) :
        (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single n (finSumFinEquiv.symm a)

/-- Kostant-form stability in the shape consumed by the carrier construction. -/
theorem kostantForm_apply_mem_lattice :
    ∀ u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm (rootGenerator n) (cartanGenerator n),
      ∀ v ∈ (lattice n).toAddSubgroup, rep n u v ∈ (lattice n).toAddSubgroup :=
  fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv

/-- The Hopf ideal cutting out the full-weight type-`C_(n+1)` carrier inside the standard
general linear group. -/
noncomputable def definingIdeal :
    HopfIdeal ℤ
      (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The full-weight Chevalley carrier of type `C_(n+1)`, obtained as the smallest closed subgroup
of the standard general linear group containing its numbered root subgroups and weight torus. -/
noncomputable def groupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The quotient-spectrum presentation of the full-weight type-`C_(n+1)` carrier. -/
theorem groupScheme_def :
    groupScheme n =
      CommHopfAlgCat.quotientSpec
        (TauCeti.GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) := by
  rw [groupScheme, definingIdeal]

/-- The canonical inclusion of the type-`C_(n+1)` carrier into its ambient general linear group. -/
noncomputable def carrierι :
    groupScheme n ⟶ TauCeti.GeneralLinear.groupScheme ℤ ((n + 1) + (n + 1)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupSchemeι (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The type-`C_(n+1)` carrier is a closed subgroup scheme of its ambient general linear group. -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι n).hom.hom.left := by
  rw [carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantToralGroupSchemeι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- A numbered root subgroup of the type `C_(n+1)` carrier. -/
noncomputable def rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k

/-- The rank-`n+1` split weight torus in the type `C_(n+1)` carrier. -/
noncomputable def weightTorus :
    SplitTorus.groupScheme ℤ (Fin (n + 1)) ⟶ groupScheme n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- Including a numbered root subgroup into the ambient general linear group recovers its
represented Kostant root subgroup. -/
@[simp] theorem rootSubgroup_comp_carrierι (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroup n k ≫ carrierι n =
      TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroup (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (kostantForm_apply_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n) := by
  rw [rootSubgroup, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_comp_ι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) k

/-- Including the split weight torus into the ambient general linear group recovers the torus of
the standard-module weights. -/
@[simp] theorem weightTorus_comp_carrierι :
    weightTorus n ≫ carrierι n =
      TauCeti.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) := by
  rw [weightTorus, carrierι]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_comp_ι
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n)

/-- Two morphisms out of the type-`C_(n+1)` carrier agree when they agree on every numbered root
subgroup and on the split weight torus. -/
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (φ ψ : groupScheme n ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup n k ≫ φ = rootSubgroup n k ≫ ψ)
    (htorus : weightTorus n ≫ φ = weightTorus n ≫ ψ) :
    φ = ψ := by
  exact TauCeti.UniversalEnvelopingAlgebra.kostantToralGroupScheme_hom_ext
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) φ ψ hroot htorus

/-- The matrix-valued points of the type `C_(n+1)` carrier. -/
noncomputable def points (A : Type) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralPointsSubgroup (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- A matrix is a point of the type-`C_(n+1)` carrier exactly when its associated convolution
point kills the carrier's defining Hopf ideal. -/
@[simp] theorem mem_points_iff (A : Type) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
    g ∈ points n A ↔
      ∀ x ∈ definingIdeal n,
        ((TauCeti.GeneralLinear.pointsMulEquiv (R := ℤ) ((n + 1) + (n + 1))).symm g).ofConv x =
          0 := by
  rw [points, definingIdeal]
  exact TauCeti.UniversalEnvelopingAlgebra.mem_kostantToralPointsSubgroup_iff
    _ _ _ _ _ _ _ _ A g

/-- A represented numbered root-subgroup matrix is a point of the type-`C_(n+1)` carrier. -/
theorem rootSubgroupMatrix_mem_points (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type) [CommRing A]
    (u : HopfAlgebra.points (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ)
      (CommAlgCat.of ℤ A)) :
    TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (kostantForm_apply_mem_lattice n) k (isNilpotent_rep_rootGenerator n k)
        (latticeBasis n) u ∈ points n A := by
  rw [points]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantGeneratedPointsSubgroup_le_toralPoints
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) A
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_mem_generatedPoints
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
      (latticeBasis n) A k u)

/-- A represented split-torus matrix is a point of the type-`C_(n+1)` carrier. -/
theorem torusMatrix_mem_points (A : Type) [CommRing A] (s : Fin (n + 1) → Aˣ) :
    TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix
        (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n) s ∈ points n A := by
  rw [points]
  exact TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_mem_toralPoints
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (kostantForm_apply_mem_lattice n) (isNilpotent_rep_rootGenerator n)
    (latticeBasis n) (basisWeight n) A s

/-- A root generator sends its designated coordinate basis vector to the designated target with
coefficient one. -/
theorem rep_rootGenerator_latticeBasis (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))
        ((latticeBasis n (finSumFinEquiv (rootSource n k)) : (lattice n).toAddSubgroup) :
          (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) =
      (1 : ℤ) • ((latticeBasis n (finSumFinEquiv (rootTarget n k)) :
          (lattice n).toAddSubgroup) :
        (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  simp only [coe_latticeBasis, Equiv.symm_apply_apply]
  rw [rep_rootGenerator_apply, one_smul]
  cases k with
  | inl i =>
      by_cases hi : i = Fin.last n
      · subst hi
        simp [rootAction]
      · simp [rootAction, hi]
  | inr i =>
      by_cases hi : i = Fin.last n
      · subst hi
        simp [rootAction]
      · simp [rootAction, hi]

/-- The coordinate-algebra map representing a numbered root subgroup is surjective. -/
private theorem representedRootCoordinateMap_surjective
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
        k (isNilpotent_rep_rootGenerator n k) (latticeBasis n)).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap_surjective _ _ _ _ _ _ _ _
    isUnit_one (rep_rootGenerator_latticeBasis n k)
    (rep_rootGenerator_rep_rootGenerator_eq_zero n k _)

/-- The root-subgroup coordinate map remains surjective after adjoining the weight torus. -/
theorem rootSubgroupCoordinateMap_surjective (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    Function.Surjective
      (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k).hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
    _ _ _ _ _ _ _ _ k (representedRootCoordinateMap_surjective n k)

/-- Every numbered root subgroup is a closed copy of the additive group. -/
instance isClosedImmersion_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsClosedImmersion (rootSubgroup n k).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantRootSubgroupToToral_of_surjective
    (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k
    (rootSubgroupCoordinateMap_surjective n k)

/-- The full-weight torus is a closed immersion into the type `C_(n+1)` carrier. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion (weightTorus n).hom.hom.left :=
  TauCeti.UniversalEnvelopingAlgebra.isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_basisWeight_eq_top n)

/-- A parametrized numbered root subgroup on points of a value algebra. -/
noncomputable abbrev rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : CommAlgCat ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup (kostantForm_apply_mem_lattice n) k
    (isNilpotent_rep_rootGenerator n k) A

/-- The split weight torus on points of a value algebra. -/
noncomputable abbrev torusPoints (A : CommAlgCat ℤ) :
    (Fin (n + 1) → Aˣ) →*
      LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints (lattice n).toAddSubgroup
    (latticeBasis n) (basisWeight n) A

/-- A torus point conjugates a numbered root element by its type-`C` root character. -/
theorem torusPoints_conj_rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : CommAlgCat ℤ) (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    torusPoints n A s * rootSubgroupParam n k A u * (torusPoints n A s)⁻¹ =
      rootSubgroupParam n k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (rootWeight n k) : A) * Multiplicative.toAdd u)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n)
    (fun j => lie_cartanGenerator_rootGenerator n k j) _ A s u

/-- The scheme-level pinning equation: conjugation by the weight torus acts on each numbered root
subgroup through the corresponding row of the type-`C` Cartan matrix, with negative rows on
lowering generators. -/
@[simp] theorem weightTorus_conj_rootSubgroup (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin (n + 1))).X)
    (u : A) :
    (s ≫ (weightTorus n).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫
          (rootSubgroup n k).hom.hom) *
        (s ≫ (weightTorus n).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((TauCeti.torusCharacter (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (rootWeight n k) : A) * u)) ≫
        (rootSubgroup n k).hom.hom :=
  TauCeti.UniversalEnvelopingAlgebra.kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n) (isNilpotent_rep_rootGenerator n) A
    (fun j => lie_cartanGenerator_rootGenerator n k j) s u

end Carrier

end TauCeti.SpStd
