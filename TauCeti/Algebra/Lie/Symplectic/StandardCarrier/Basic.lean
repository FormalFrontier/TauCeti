/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.MatrixRepresentation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.C.Datum
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Algebra.Lie.Sl2.WeightString

/-!
# Type-C standard generators and full-weight lattice

For positive rank `n + 1`, the symplectic Lie algebra `sp₂ₙ₊₂` acts on its standard module
`(Fin (n + 1) ⊕ Fin (n + 1)) → ℚ`. This file records its Bourbaki-numbered simple Chevalley
generators, their Serre relations, the standard integral lattice, and the standard weights. These
data feed the Kostant toral-closure construction in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme`.

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
* `TauCeti.SpStd.weight` and `TauCeti.SpStd.rootGeneratorWeight`: the integral weights of the
  standard coordinates and the root characters of the numbered generators.
* `TauCeti.SpStd.lattice`, `TauCeti.SpStd.latticeBasis`, and `TauCeti.SpStd.basisWeight`: the
  standard admissible lattice, its enumerated coordinate basis, and the weights of that basis.
* `TauCeti.SpStd.rootSubgroupParam` and `TauCeti.SpStd.torusPoints`: the parametrized numbered
  root subgroups and the split weight torus on points of a value algebra.

## Main results

* `TauCeti.SpStd.isSl2Triple_rootGenerator`: the `sl₂` triple at each numbered index, from which
  the higher Serre relations are read off.
* `TauCeti.SpStd.isSerreSystem_rootGenerator`: the characteristic Chevalley--Serre relations of
  the numbered generators.
* `TauCeti.SpStd.lie_cartanGenerator_rootGenerator`: the numbered Cartan generators act on the
  root generators through the rows of the type-`C` Cartan matrix.
* `TauCeti.SpStd.isNilpotent_rep_rootGenerator` and
  `TauCeti.SpStd.nilpotencyClass_rep_rootGenerator`: each numbered root generator squares to zero
  on the standard module, and has nilpotency class exactly two.
* `TauCeti.SpStd.intCast_latticeBasis_repr`: the coordinate-basis coefficients of a lattice vector
  are its rational coordinates.
* `TauCeti.SpStd.rep_kostantForm_mem_lattice`: the Kostant `ℤ`-form preserves the standard
  lattice, so the lattice is admissible.
* `TauCeti.SpStd.span_range_weight_eq_top`: the weights of the standard module generate the full
  character lattice.
* `TauCeti.SpStd.torusPoints_conj_rootSubgroupParam`: the pointwise pinning equation.

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

universe v

namespace TauCeti.SpStd

open LieAlgebra.Symplectic
open scoped TensorProduct

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

private theorem fromBlocks_mem_sp (P Q S R : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hQ : Qᵀ = Q) (hS : Sᵀ = S) (hR : R = -Pᵀ) :
    _root_.Matrix.fromBlocks P Q S R ∈ sp (Fin (n + 1)) ℚ := by
  subst R
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

/-- Two nonfinal indices have the same successor exactly when they are equal. -/
theorem next_inj (i j : Fin (n + 1)) (hi : i ≠ Fin.last n) (hj : j ≠ Fin.last n) :
    next n i hi = next n j hj ↔ i = j := by
  rw [Fin.ext_iff, Fin.ext_iff, val_next, val_next]
  omega

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
def cartanGeneratorMatrix (i : Fin (n + 1)) :
    _root_.Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ :=
  _root_.Matrix.diagonal fun k => (weight n k i : ℚ)

/-- The entries of the diagonal matrix of a Cartan generator are the coordinate weights. -/
@[simp] theorem cartanGeneratorMatrix_apply (i : Fin (n + 1))
    (a b : Fin (n + 1) ⊕ Fin (n + 1)) :
    cartanGeneratorMatrix n i a b = if a = b then (weight n a i : ℚ) else 0 := by
  rw [cartanGeneratorMatrix, _root_.Matrix.diagonal_apply]

theorem cartanGeneratorMatrix_mem_sp (i : Fin (n + 1)) :
    cartanGeneratorMatrix n i ∈ sp (Fin (n + 1)) ℚ := by
  have hblocks : cartanGeneratorMatrix n i =
      _root_.Matrix.fromBlocks
        (_root_.Matrix.diagonal fun a : Fin (n + 1) =>
          (DynkinType.TypeC.weight (n + 1) a i : ℚ)) 0 0
        (-_root_.Matrix.diagonal fun a : Fin (n + 1) =>
          (DynkinType.TypeC.weight (n + 1) a i : ℚ)) := by
    ext a b
    cases a <;> cases b <;>
      simp [cartanGeneratorMatrix, _root_.Matrix.fromBlocks, _root_.Matrix.diagonal_apply]
  rw [hblocks]
  exact fromBlocks_mem_sp n _ 0 0 _ (by simp) (by simp) (by simp)

/-- The Bourbaki-numbered raising and lowering generators of `sp₂ₙ₊₂`. -/
def rootGenerator : Fin (n + 1) ⊕ Fin (n + 1) → sp (Fin (n + 1)) ℚ
  | .inl i => ⟨positiveRootMatrix n i, positiveRootMatrix_mem_sp n i⟩
  | .inr i => ⟨negativeRootMatrix n i, negativeRootMatrix_mem_sp n i⟩

/-- The Bourbaki-numbered Cartan generators in the standard symplectic representation. -/
def cartanGenerator (i : Fin (n + 1)) : sp (Fin (n + 1)) ℚ :=
  ⟨cartanGeneratorMatrix n i, cartanGeneratorMatrix_mem_sp n i⟩

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
        cartanGeneratorMatrix n i := (rfl)

private theorem lie_cartanGeneratorMatrix_cartanGeneratorMatrix (i j : Fin (n + 1)) :
    ⁅cartanGeneratorMatrix n i, cartanGeneratorMatrix n j⁆ = 0 := by
  rw [cartanGeneratorMatrix, cartanGeneratorMatrix, LieRing.of_associative_ring_bracket]
  ext a b
  simp only [_root_.Matrix.diagonal_mul_diagonal, _root_.Matrix.sub_apply,
    _root_.Matrix.diagonal_apply, _root_.Matrix.zero_apply]
  split_ifs <;> ring

/-- The standard representation of the symplectic Lie algebra, extended to its enveloping
algebra. -/
noncomputable def rep :
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
theorem rep_cartanGenerator_apply_apply (i : Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ)
    (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator n i)) v a =
      (weight n a i : ℚ) * v a := by
  rw [rep_ι_apply, val_cartanGenerator, cartanGeneratorMatrix, _root_.Matrix.mulVec_diagonal]

/-- The source coordinate of a numbered root generator: the coordinate on whose basis vector the
generator is nonzero with coefficient one. -/
def rootSource : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => if hi : i = Fin.last n then .inr i else .inl (next n i hi)
  | .inr i => .inl i

/-- The target coordinate of a numbered root generator: the coordinate carrying the image of the
basis vector at `rootSource`. -/
def rootTarget : Fin (n + 1) ⊕ Fin (n + 1) → Fin (n + 1) ⊕ Fin (n + 1)
  | .inl i => .inl i
  | .inr i => if hi : i = Fin.last n then .inr i else .inl (next n i hi)

@[simp] theorem rootSource_inl_last :
    rootSource n (.inl (Fin.last n)) = .inr (Fin.last n) := by
  simp [rootSource]

@[simp] theorem rootSource_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootSource n (.inl i) = .inl (next n i hi) := by
  simp [rootSource, hi]

@[simp] theorem rootSource_inr (i : Fin (n + 1)) :
    rootSource n (.inr i) = .inl i := (rfl)

@[simp] theorem rootTarget_inl (i : Fin (n + 1)) :
    rootTarget n (.inl i) = .inl i := (rfl)

@[simp] theorem rootTarget_inr_last :
    rootTarget n (.inr (Fin.last n)) = .inr (Fin.last n) := by
  simp [rootTarget]

@[simp] theorem rootTarget_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootTarget n (.inr i) = .inl (next n i hi) := by
  simp [rootTarget, hi]

/-- The root character of a numbered generator, calculated as target weight minus source weight. -/
def rootGeneratorWeight (k : Fin (n + 1) ⊕ Fin (n + 1)) (j : Fin (n + 1)) : ℤ :=
  weight n (rootTarget n k) j - weight n (rootSource n k) j

/-- The weight difference across a raising generator is the corresponding simple root in the
canonical simply connected type-`C` root datum. -/
theorem rootGeneratorWeight_inl_eq_root (i : Fin (n + 1)) :
    rootGeneratorWeight n (.inl i) =
      (DynkinType.typeCSimplyConnectedRootDatum (n + 1)).root
        (DynkinType.typeCSimpleIndex (n + 1) i) := by
  rw [DynkinType.root_typeCSimpleIndex]
  funext j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rootGeneratorWeight, rootTarget_inl, rootSource_inl_last]
    simp only [weight_inl, weight_inr, DynkinType.TypeC.weight_apply, CartanMatrix.C,
      _root_.Matrix.of_apply, Fin.val_last, Nat.add_sub_cancel]
    split_ifs <;> simp only [Fin.ext_iff, Fin.val_last] at * <;> omega
  · rw [rootGeneratorWeight, rootTarget_inl, rootSource_inl_of_ne_last n i hi]
    simp only [weight_inl, DynkinType.TypeC.weight_apply, CartanMatrix.C, _root_.Matrix.of_apply]
    have hinext : i.val + 1 = (next n i hi).val := (val_next n i hi).symm
    split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

/-- The roots of the raising generators are the rows of the type-`C` Cartan matrix. -/
@[simp] theorem rootGeneratorWeight_inl (i j : Fin (n + 1)) :
    rootGeneratorWeight n (.inl i) j = CartanMatrix.C (n + 1) i j := by
  rw [rootGeneratorWeight_inl_eq_root, DynkinType.root_typeCSimpleIndex]

/-- The roots of the lowering generators are the negatives of the rows of the type-`C` Cartan
matrix. -/
@[simp] theorem rootGeneratorWeight_inr (i j : Fin (n + 1)) :
    rootGeneratorWeight n (.inr i) j = -CartanMatrix.C (n + 1) i j := by
  rw [← rootGeneratorWeight_inl n i j, rootGeneratorWeight, rootGeneratorWeight, rootTarget_inl,
    rootSource_inr]
  by_cases hi : i = Fin.last n
  · subst hi
    rw [rootTarget_inr_last, rootSource_inl_last]
    simp only [weight_inr, weight_inl]
    ring
  · rw [rootTarget_inr_of_ne_last n i hi, rootSource_inl_of_ne_last n i hi]
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
theorem positiveRootMatrix_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    positiveRootMatrix n i =
      _root_.Matrix.single (.inl i) (.inl (next n i hi)) 1 -
        _root_.Matrix.single (.inr (next n i hi)) (.inr i) 1 := by
  ext a b
  cases a <;> cases b <;>
    simp [positiveRootMatrix, hi, shortPositiveBlock, _root_.Matrix.fromBlocks,
      _root_.Matrix.single_apply]

/-- Each lowering matrix is the transpose of the raising matrix at the same index. -/
theorem negativeRootMatrix_eq_transpose (i : Fin (n + 1)) :
    negativeRootMatrix n i = (positiveRootMatrix n i)ᵀ := by
  rw [negativeRootMatrix, positiveRootMatrix]
  split_ifs with hi <;>
    simp [_root_.Matrix.fromBlocks_transpose, shortPositiveBlock, shortNegativeBlock,
      _root_.Matrix.transpose_single]

/-- The final lowering matrix is a single off-diagonal matrix unit. -/
theorem negativeRootMatrix_last :
    negativeRootMatrix n (Fin.last n) =
      _root_.Matrix.single (.inr (Fin.last n)) (.inl (Fin.last n)) 1 := by
  rw [negativeRootMatrix_eq_transpose, positiveRootMatrix_last, _root_.Matrix.transpose_single]

/-- A nonfinal lowering matrix is the difference of its upper and lower matrix units. -/
theorem negativeRootMatrix_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    negativeRootMatrix n i =
      _root_.Matrix.single (.inl (next n i hi)) (.inl i) 1 -
        _root_.Matrix.single (.inr i) (.inr (next n i hi)) 1 := by
  rw [negativeRootMatrix_eq_transpose, positiveRootMatrix_of_ne_last n i hi,
    _root_.Matrix.transpose_sub, _root_.Matrix.transpose_single,
    _root_.Matrix.transpose_single]

private theorem lie_positiveRootMatrix_negativeRootMatrix_self (i : Fin (n + 1)) :
    ⁅positiveRootMatrix n i, negativeRootMatrix n i⁆ = cartanGeneratorMatrix n i := by
  by_cases hi : i = Fin.last n
  · subst i
    rw [positiveRootMatrix_last, negativeRootMatrix_last, lie_single_single]
    ext a b
    cases a <;> cases b <;>
      simp [cartanGeneratorMatrix, DynkinType.TypeC.weight_apply, _root_.Matrix.diagonal_apply,
        _root_.Matrix.single_apply] <;>
      split_ifs <;> simp_all [Fin.ext_iff, Fin.val_last] <;> omega
  · rw [positiveRootMatrix_of_ne_last n i hi, negativeRootMatrix_of_ne_last n i hi,
      sub_lie, lie_sub, lie_sub, lie_single_single, lie_single_single, lie_single_single,
      lie_single_single]
    ext a b
    cases a <;> cases b <;>
      simp [cartanGeneratorMatrix, DynkinType.TypeC.weight_apply, _root_.Matrix.diagonal_apply,
        _root_.Matrix.single_apply] <;>
      split_ifs <;> simp_all [Fin.ext_iff] <;> omega

private theorem lie_positiveRootMatrix_negativeRootMatrix_of_ne
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅positiveRootMatrix n i, negativeRootMatrix n j⁆ = 0 := by
  by_cases hi : i = Fin.last n
  · subst i
    have hj : j ≠ Fin.last n := Ne.symm hij
    rw [positiveRootMatrix_last, negativeRootMatrix_of_ne_last n j hj, lie_sub,
      lie_single_single, lie_single_single]
    ext a b
    cases a <;> cases b <;> simp [hj, Ne.symm hj]
  · by_cases hj : j = Fin.last n
    · subst j
      rw [positiveRootMatrix_of_ne_last n i hi, negativeRootMatrix_last, sub_lie,
        lie_single_single, lie_single_single]
      ext a b
      cases a <;> cases b <;> simp [hi, Ne.symm hi]
    · rw [positiveRootMatrix_of_ne_last n i hi, negativeRootMatrix_of_ne_last n j hj,
        sub_lie, lie_sub, lie_sub, lie_single_single, lie_single_single, lie_single_single,
        lie_single_single]
      ext a b
      cases a <;> cases b <;>
        simp [hij, Ne.symm hij, next_inj]

/-- A Cartan generator scales every matrix unit by the difference of the coordinate weights at its
row and column. -/
private theorem lie_cartanGeneratorMatrix_single (j : Fin (n + 1))
    (a b : Fin (n + 1) ⊕ Fin (n + 1)) :
    ⁅cartanGeneratorMatrix n j, _root_.Matrix.single a b (1 : ℚ)⁆ =
      ((weight n a j - weight n b j : ℤ) : ℚ) • _root_.Matrix.single a b (1 : ℚ) := by
  rw [cartanGeneratorMatrix, lie_single_of_mem_diagonalCartan (diagonal_mem_diagonalCartan _),
    _root_.Matrix.diagonal_apply_eq, _root_.Matrix.diagonal_apply_eq, Int.cast_sub]

/-- The matrix commutator of a Cartan generator with a raising generator. -/
private theorem lie_cartanGeneratorMatrix_positiveRootMatrix (i j : Fin (n + 1)) :
    ⁅cartanGeneratorMatrix n j, positiveRootMatrix n i⁆ =
      ((rootGeneratorWeight n (.inl i) j : ℤ) : ℚ) • positiveRootMatrix n i := by
  by_cases hi : i = Fin.last n
  · subst hi
    rw [positiveRootMatrix_last, lie_cartanGeneratorMatrix_single, rootGeneratorWeight,
      rootTarget_inl, rootSource_inl_last]
  · have hupper : weight n (.inl i) j - weight n (.inl (next n i hi)) j =
        rootGeneratorWeight n (.inl i) j := by
      rw [rootGeneratorWeight, rootTarget_inl, rootSource_inl_of_ne_last n i hi]
    have hlower : weight n (.inr (next n i hi)) j - weight n (.inr i) j =
        rootGeneratorWeight n (.inl i) j := by
      rw [← hupper]
      simp only [weight_inl, weight_inr]
      ring
    rw [positiveRootMatrix_of_ne_last n i hi, lie_sub, lie_cartanGeneratorMatrix_single,
      lie_cartanGeneratorMatrix_single, hupper, hlower, smul_sub]

/-- The matrix commutator of a Cartan generator with a lowering generator, read off from the
raising case by transposing: the diagonal matrix `cartanGeneratorMatrix` is invariant under
transposition and the lowering root character is the negative of the raising one. -/
private theorem lie_cartanGeneratorMatrix_negativeRootMatrix (i j : Fin (n + 1)) :
    ⁅cartanGeneratorMatrix n j, negativeRootMatrix n i⁆ =
      ((rootGeneratorWeight n (.inr i) j : ℤ) : ℚ) • negativeRootMatrix n i := by
  have hsymm : (cartanGeneratorMatrix n j)ᵀ = cartanGeneratorMatrix n j := by
    rw [cartanGeneratorMatrix, _root_.Matrix.diagonal_transpose]
  have hpos := lie_cartanGeneratorMatrix_positiveRootMatrix n i j
  rw [LieRing.of_associative_ring_bracket] at hpos
  rw [negativeRootMatrix_eq_transpose, LieRing.of_associative_ring_bracket,
    rootGeneratorWeight_inr, ← rootGeneratorWeight_inl n i j]
  have hswap : cartanGeneratorMatrix n j * (positiveRootMatrix n i)ᵀ -
      (positiveRootMatrix n i)ᵀ * cartanGeneratorMatrix n j =
      -(cartanGeneratorMatrix n j * positiveRootMatrix n i -
        positiveRootMatrix n i * cartanGeneratorMatrix n j)ᵀ := by
    rw [_root_.Matrix.transpose_sub, _root_.Matrix.transpose_mul, _root_.Matrix.transpose_mul,
      hsymm]
    abel
  rw [hswap, hpos, Int.cast_neg, neg_smul, _root_.Matrix.transpose_smul]

/-- The numbered Cartan generators act on the root generators through their recorded root
characters, equivalently through the type-`C` Cartan matrix and its negatives. -/
theorem lie_cartanGenerator_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1))
    (j : Fin (n + 1)) :
    ⁅cartanGenerator n j, rootGenerator n k⁆ =
      ((rootGeneratorWeight n k j : ℤ) : ℚ) • rootGenerator n k := by
  refine Subtype.ext ?_
  cases k with
  | inl i =>
      rw [LieSubalgebra.coe_bracket, val_cartanGenerator, Submodule.coe_smul,
        val_rootGenerator_inl]
      exact lie_cartanGeneratorMatrix_positiveRootMatrix n i j
  | inr i =>
      rw [LieSubalgebra.coe_bracket, val_cartanGenerator, Submodule.coe_smul,
        val_rootGenerator_inr]
      exact lie_cartanGeneratorMatrix_negativeRootMatrix n i j

/-! ## The `sl₂` triples of the numbered generators -/

private theorem positiveRootMatrix_ne_zero (i : Fin (n + 1)) : positiveRootMatrix n i ≠ 0 := by
  by_cases hi : i = Fin.last n
  · subst hi
    rw [positiveRootMatrix_last]
    intro hzero
    have h := congrFun (congrFun hzero (.inl (Fin.last n))) (.inr (Fin.last n))
    simp at h
  · rw [positiveRootMatrix_of_ne_last n i hi]
    intro hzero
    have h := congrFun (congrFun hzero (.inl i)) (.inl (next n i hi))
    simp at h

private theorem negativeRootMatrix_ne_zero (i : Fin (n + 1)) : negativeRootMatrix n i ≠ 0 := by
  rw [negativeRootMatrix_eq_transpose, Ne, _root_.Matrix.transpose_eq_zero]
  exact positiveRootMatrix_ne_zero n i

private theorem rootGenerator_ne_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootGenerator n k ≠ 0 := by
  intro hzero
  cases k with
  | inl i =>
      apply positiveRootMatrix_ne_zero n i
      rw [← val_rootGenerator_inl n i, hzero]
      rfl
  | inr i =>
      apply negativeRootMatrix_ne_zero n i
      rw [← val_rootGenerator_inr n i, hzero]
      rfl

private theorem lie_rootGenerator_inl_inr_of_ne (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅rootGenerator n (.inl i), rootGenerator n (.inr j)⁆ = 0 := by
  apply Subtype.ext
  simpa only [LieSubalgebra.coe_bracket, val_rootGenerator_inl, val_rootGenerator_inr,
    Submodule.coe_zero] using lie_positiveRootMatrix_negativeRootMatrix_of_ne n i j hij

private theorem lie_cartanGenerator_rootGenerator_inl_self (i : Fin (n + 1)) :
    ⁅cartanGenerator n i, rootGenerator n (.inl i)⁆ = (2 : ℚ) • rootGenerator n (.inl i) := by
  rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inl, CartanMatrix.C_diag]
  norm_num

private theorem cartanGenerator_ne_zero (i : Fin (n + 1)) : cartanGenerator n i ≠ 0 := by
  intro hzero
  have h2 : (2 : ℚ) • rootGenerator n (.inl i) = 0 := by
    rw [← lie_cartanGenerator_rootGenerator_inl_self, hzero, zero_lie]
  rcases smul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact rootGenerator_ne_zero n (.inl i) h

/-- The numbered raising and lowering generators at a common index, together with the Cartan
generator at that index, form an `sl₂` triple. -/
theorem isSl2Triple_rootGenerator (i : Fin (n + 1)) :
    _root_.IsSl2Triple (cartanGenerator n i) (rootGenerator n (.inl i))
      (rootGenerator n (.inr i)) where
  h_ne_zero := cartanGenerator_ne_zero n i
  lie_e_f := by
    apply Subtype.ext
    simpa only [LieSubalgebra.coe_bracket, val_rootGenerator_inl, val_rootGenerator_inr,
      val_cartanGenerator] using lie_positiveRootMatrix_negativeRootMatrix_self n i
  lie_h_e_nsmul := by
    rw [lie_cartanGenerator_rootGenerator_inl_self, two_smul, two_nsmul]
  lie_h_f_nsmul := by
    rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inr, CartanMatrix.C_diag,
      two_nsmul]
    push_cast
    rw [neg_smul, two_smul]

/-- The standard type-`C` Chevalley generators satisfy the Serre relations for the transposed
Cartan matrix, in the convention used by `IsSerreSystem`. -/
theorem isSerreSystem_rootGenerator :
    IsSerreSystem ℚ (CartanMatrix.C (n + 1))ᵀ
      (cartanGenerator n)
      (fun i => rootGenerator n (.inl i))
      (fun i => rootGenerator n (.inr i)) where
  lie_H_H i j := by
    apply Subtype.ext
    simpa only [LieSubalgebra.coe_bracket, val_cartanGenerator, Submodule.coe_zero] using
      lie_cartanGeneratorMatrix_cartanGeneratorMatrix n i j
  lie_E_F_self i := (isSl2Triple_rootGenerator n i).lie_e_f
  lie_E_F_of_ne i j hij := lie_rootGenerator_inl_inr_of_ne n i j hij
  lie_H_E i j := by
    rw [Matrix.transpose_apply]
    simpa only [rootGeneratorWeight_inl, Int.cast_smul_eq_zsmul] using
      lie_cartanGenerator_rootGenerator n (.inl j) i
  lie_H_F i j := by
    rw [Matrix.transpose_apply]
    simpa only [rootGeneratorWeight_inr, Int.cast_smul_eq_zsmul, neg_zsmul] using
      lie_cartanGenerator_rootGenerator n (.inr j) i
  ad_pow_lie_E_E i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple_rootGenerator n i)
        (by rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inl])
        (by rw [← lie_skew, lie_rootGenerator_inl_inr_of_ne n j i hij.symm, neg_zero])
  ad_pow_lie_F_F i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp
    · rw [Matrix.transpose_apply]
      exact ad_pow_lie_eq_zero_of_isSl2Triple_of_lie_h_eq_smul_of_lie_f_eq_zero
        (isSl2Triple_rootGenerator n i).symm
        (by rw [neg_lie, lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inr,
            Int.cast_neg, neg_smul, neg_neg])
        (lie_rootGenerator_inl_inr_of_ne n i j hij)

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

@[simp] theorem rootAction_inl_last (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rootAction n (.inl (Fin.last n)) v =
      v (.inr (Fin.last n)) • Pi.single (.inl (Fin.last n)) 1 := by
  simp [rootAction]

@[simp] theorem rootAction_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rootAction n (.inl i) v =
      v (.inl (next n i hi)) • Pi.single (.inl i) 1 -
        v (.inr i) • Pi.single (.inr (next n i hi)) 1 := by
  simp [rootAction, hi]

@[simp] theorem rootAction_inr_last (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rootAction n (.inr (Fin.last n)) v =
      v (.inl (Fin.last n)) • Pi.single (.inr (Fin.last n)) 1 := by
  simp [rootAction]

@[simp] theorem rootAction_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rootAction n (.inr i) v =
      v (.inl i) • Pi.single (.inl (next n i hi)) 1 -
        v (.inr (next n i hi)) • Pi.single (.inr i) 1 := by
  simp [rootAction, hi]

/-- The standard action of a numbered root generator is the explicit coordinate operation
`rootAction`. -/
theorem rep_rootGenerator_apply (k : Fin (n + 1) ⊕ Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v = rootAction n k v := by
  rw [rep_ι_apply]
  cases k with
  | inl i =>
      rw [val_rootGenerator_inl]
      by_cases hi : i = Fin.last n
      · subst hi
        rw [positiveRootMatrix_last, rootAction_inl_last, _root_.Matrix.single_mulVec_eq, one_mul]
      · rw [positiveRootMatrix_of_ne_last n i hi, rootAction_inl_of_ne_last n i hi,
          _root_.Matrix.sub_mulVec, _root_.Matrix.single_mulVec_eq,
          _root_.Matrix.single_mulVec_eq, one_mul, one_mul]
  | inr i =>
      rw [val_rootGenerator_inr]
      by_cases hi : i = Fin.last n
      · subst hi
        rw [negativeRootMatrix_last, rootAction_inr_last, _root_.Matrix.single_mulVec_eq, one_mul]
      · rw [negativeRootMatrix_of_ne_last n i hi, rootAction_inr_of_ne_last n i hi,
          _root_.Matrix.sub_mulVec, _root_.Matrix.single_mulVec_eq,
          _root_.Matrix.single_mulVec_eq, one_mul, one_mul]

/-- Applying a numbered root generator twice in the standard representation gives zero. -/
theorem rep_rootGenerator_rep_rootGenerator_eq_zero
    (k : Fin (n + 1) ⊕ Fin (n + 1))
    (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))
      (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v) = 0 := by
  rw [rep_rootGenerator_apply, rep_rootGenerator_apply]
  cases k with
  | inl i =>
      by_cases hi : i = Fin.last n
      · subst hi
        simp
      · simp [hi, (lt_next n i hi).ne, (lt_next n i hi).ne']
  | inr i =>
      by_cases hi : i = Fin.last n
      · subst hi
        simp
      · simp [hi, (lt_next n i hi).ne, (lt_next n i hi).ne']

/-- Every numbered root generator squares to zero in the standard representation. -/
theorem pow_two_rep_rootGenerator_eq_zero (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) ^ 2 = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [pow_two, Module.End.mul_apply, rep_rootGenerator_rep_rootGenerator_eq_zero,
    LinearMap.zero_apply]

/-- Every numbered root generator acts nilpotently on the standard module. -/
theorem isNilpotent_rep_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    IsNilpotent (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))) :=
  ⟨2, pow_two_rep_rootGenerator_eq_zero n k⟩

/-! ## Weight vectors and the standard admissible lattice -/

/-- Every standard coordinate vector is a weight vector for the numbered Cartan generators. -/
theorem isCartanWeightVector_single (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator n) (rep n)
      (weight n a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (cartanGenerator n) (rep n)).mpr fun i => ?_
  rw [rep_ι_apply, val_cartanGenerator, cartanGeneratorMatrix, _root_.Matrix.diagonal_mulVec_single]
  rw [← Pi.single_smul']
  simp

/-- The standard coordinate `ℤ`-lattice in the symplectic module. -/
def lattice : Submodule ℤ ((Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) :=
  TauCeti.coordinateLattice (Fin (n + 1) ⊕ Fin (n + 1))

/-- A vector is in the standard lattice exactly when all its coordinates are integers. -/
@[simp] theorem mem_lattice_iff {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} :
    v ∈ lattice n ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin (n + 1) ⊕ Fin (n + 1))

theorem single_mem_lattice (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    Pi.single a (1 : ℚ) ∈ lattice n := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin (n + 1) ⊕ Fin (n + 1)) a

/-- The coordinate basis of the standard lattice, enumerated by a finite interval as required by
the matrix carrier construction.

The carrier subtype and `ℤ`-module structure of a submodule are definitionally equal to those of
its underlying additive subgroup, so the reindexed coordinate basis has the displayed target
type. -/
noncomputable def latticeBasis :
    Module.Basis (Fin ((n + 1) + (n + 1))) ℤ (lattice n).toAddSubgroup :=
  (TauCeti.coordinateLatticeBasis (Fin (n + 1) ⊕ Fin (n + 1))).reindex finSumFinEquiv

@[simp] theorem coe_latticeBasis (a : Fin ((n + 1) + (n + 1))) :
    ((latticeBasis n a : (lattice n).toAddSubgroup) :
      (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) = Pi.single (finSumFinEquiv.symm a) 1 := by
  unfold latticeBasis lattice
  rw [Module.Basis.reindex_apply, ← Pi.basisFun_apply]
  exact TauCeti.coe_coordinateLatticeBasis (Fin (n + 1) ⊕ Fin (n + 1)) _

/-- The coordinate-basis coefficients of a lattice vector are its rational coordinates: extending
the `a`-th coefficient to `ℚ` recovers the coordinate at the standard index enumerated by `a`. -/
@[simp] theorem intCast_latticeBasis_repr (v : (lattice n).toAddSubgroup)
    (a : Fin ((n + 1) + (n + 1))) :
    (((latticeBasis n).repr v a : ℤ) : ℚ) =
      (v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) (finSumFinEquiv.symm a) := by
  unfold latticeBasis lattice at *
  rw [Module.Basis.repr_reindex_apply, TauCeti.intCast_coordinateLatticeBasis_repr]

/-- The weight attached to the enumerated coordinate basis. -/
def basisWeight (a : Fin ((n + 1) + (n + 1))) : Fin (n + 1) → ℤ :=
  weight n (finSumFinEquiv.symm a)

@[simp] theorem basisWeight_apply (a : Fin ((n + 1) + (n + 1))) :
    basisWeight n a = weight n (finSumFinEquiv.symm a) := (rfl)

/-- A numbered root generator preserves the standard lattice. -/
theorem rep_rootGenerator_mem_lattice (k : Fin (n + 1) ⊕ Fin (n + 1))
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k)) v ∈ lattice n := by
  have key : ∀ a b : Fin (n + 1) ⊕ Fin (n + 1), v a • Pi.single b (1 : ℚ) ∈ lattice n := by
    intro a b
    obtain ⟨z, hz⟩ := (mem_lattice_iff n).1 hv a
    rw [← hz, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (single_mem_lattice n b) z
  rw [rep_rootGenerator_apply]
  cases k with
  | inl i =>
      by_cases hi : i = Fin.last n
      · subst hi
        rw [rootAction_inl_last]
        exact key _ _
      · rw [rootAction_inl_of_ne_last n i hi]
        exact sub_mem (key _ _) (key _ _)
  | inr i =>
      by_cases hi : i = Fin.last n
      · subst hi
        rw [rootAction_inr_last]
        exact key _ _
      · rw [rootAction_inr_of_ne_last n i hi]
        exact sub_mem (key _ _) (key _ _)

/-- The standard coordinate lattice is stable under the Kostant integral form: the root generators
square to zero and preserve it, and the coordinate vectors have integral weights. -/
theorem rep_kostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (sp (Fin (n + 1)) ℚ)}
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm (rootGenerator n)
      (cartanGenerator n))
    {v : (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ} (hv : v ∈ lattice n) :
    rep n u v ∈ lattice n :=
  TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice (rootGenerator n)
    (cartanGenerator n) (rep n) (wt := weight n) (pow_two_rep_rootGenerator_eq_zero n)
    (fun k _ hw => rep_rootGenerator_mem_lattice n k hw) (isCartanWeightVector_single n) hu hv

/-! ## The full weight lattice -/

/-- The weights of the standard symplectic module span the full character lattice. -/
theorem span_range_weight_eq_top : Submodule.span ℤ (Set.range (weight n)) = ⊤ := by
  apply top_unique
  rw [← DynkinType.TypeC.span_range_weight_eq_top (n + 1)]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  refine ⟨Sum.inl a, ?_⟩
  funext i
  exact weight_inl n a i

/-- Enumerating the coordinate basis does not change the span of its weights. -/
theorem span_range_basisWeight_eq_top : Submodule.span ℤ (Set.range (basisWeight n)) = ⊤ := by
  have hrange : Set.range (basisWeight n) = Set.range (weight n) :=
    finSumFinEquiv.symm.surjective.range_comp (weight n)
  rw [hrange]
  exact span_range_weight_eq_top n

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
        simp
      · simp [hi]
  | inr i =>
      by_cases hi : i = Fin.last n
      · subst hi
        simp
      · simp [hi]

attribute [local instance high] Algebra.toModule

/-- Every numbered root generator has nilpotency class exactly two in the standard
representation. -/
theorem nilpotencyClass_rep_rootGenerator (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    nilpotencyClass
        (rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator n k))) = 2 := by
  refine nilpotencyClass_eq_succ_iff.mpr ⟨pow_two_rep_rootGenerator_eq_zero n k, ?_⟩
  rw [pow_one]
  intro hzero
  have h := DFunLike.congr_fun hzero
    ((latticeBasis n (finSumFinEquiv (rootSource n k)) : (lattice n).toAddSubgroup) :
      (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ)
  rw [rep_rootGenerator_latticeBasis, one_smul, coe_latticeBasis] at h
  simp only [LinearMap.zero_apply, Equiv.symm_apply_apply] at h
  have h2 := congrFun h (rootTarget n k)
  simp at h2

/-- Every coordinate basis vector of the standard lattice is a Cartan weight vector. -/
theorem isCartanWeightVector_latticeBasis (a : Fin ((n + 1) + (n + 1))) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector (cartanGenerator n) (rep n)
      (basisWeight n a)
      ((latticeBasis n a : (lattice n).toAddSubgroup) :
        (Fin (n + 1) ⊕ Fin (n + 1)) → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single n (finSumFinEquiv.symm a)

/-- The parametrized numbered root subgroup on points of a value algebra. -/
noncomputable def rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1)) (A : CommAlgCat ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
    (isNilpotent_rep_rootGenerator n k) A

/-- The split weight torus on points of a value algebra. -/
noncomputable def torusPoints (A : CommAlgCat ℤ) :
    (Fin (n + 1) → Aˣ) →*
      LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (lattice n).toAddSubgroup) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints (lattice n).toAddSubgroup
    (latticeBasis n) (basisWeight n) A

/-- **The pointwise pinning equation of the type `C_(n+1)` carrier.** A torus point `s`
conjugates the root-subgroup element of parameter `u` into the one of parameter `α_k(s) u`, where
`α_k` is the `k`-th row of the type-`C` Cartan matrix on a raising generator and its negative on a
lowering one. -/
theorem torusPoints_conj_rootSubgroupParam (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : CommAlgCat ℤ) (s : Fin (n + 1) → Aˣ) (u : Multiplicative A) :
    torusPoints n A s * rootSubgroupParam n k A u * (torusPoints n A s)⁻¹ =
      rootSubgroupParam n k A
        (Multiplicative.ofAdd
          ((TauCeti.torusCharacter s (rootGeneratorWeight n k) : A) * Multiplicative.toAdd u)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantTorusPoints_conj_kostantRootSubgroupParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n)
    (fun j => lie_cartanGenerator_rootGenerator n k j) _ A s u

end TauCeti.SpStd
