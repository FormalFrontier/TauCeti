/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD

/-!
# The numbered simple-root generators of the split type-D Lie algebra

For `4 ≤ n`, this file puts the Bourbaki-numbered Chevalley generators of the split orthogonal
Lie algebra `LieAlgebra.Orthogonal.typeD (Fin n) K` into explicit matrix form. In the hyperbolic
basis, whose Gram matrix is

```text
[ 0  1 ]
[ 1  0 ],
```

Lean indexes both nodes and coordinates from zero: `i : Fin n` represents Bourbaki node `i + 1`.
Thus the chain generator for `α_{i+1} = εᵢ - εᵢ₊₁` is

```text
E_{i,i+1} - E_{\bar{i+1},\bar i},
```

and the fork generator for `αₙ = ε_{n-2} + ε_{n-1}` is

```text
E_{n-2,\bar{n-1}} - E_{n-1,\bar{n-2}}.
```

The lowering generators are their transposes. The resulting matrices lie in the split orthogonal
Lie algebra and are square-zero in its standard representation.

These are the carrier-specific numbered root vectors needed to feed the type-`D` spin lattice
into Tau Ceti's existing Kostant-form and toral-closure machinery. Identifying their action with
quadratic Clifford elements, and then proving the divided-power stability needed by the full-weight
spin lattice, are deliberately left to the next carrier step.

## Main definitions and results

* `TauCeti.TypeDStd.raisingMatrix`: the explicit ambient raising matrix.
* `TauCeti.TypeDStd.rootGenerator`: the raising and lowering generators in the type-`D` Lie
  algebra.
* `TauCeti.TypeDStd.cartanGenerator`: the zero-based Bourbaki-numbered diagonal Cartan generators.
* `TauCeti.TypeDStd.rootGeneratorWeight`: the integral Cartan weights of the generators.
* `TauCeti.TypeDStd.lie_cartanGenerator_rootGenerator`: the Cartan action on the generators.
* `TauCeti.TypeDStd.val_rootGenerator_mul_self`: every numbered generator is square-zero in the
  standard representation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§11, 25.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.

This advances the explicit Chevalley--Demazure construction in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0, pinned ambient groups,
of `TauCetiRoadmap/CFSGStatement/README.md`.
-/

public section

namespace TauCeti.TypeDStd

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (hn : 4 ≤ n)

/-! ## Explicit matrices -/

/-- The penultimate coordinate in the standard type-`Dₙ` realization. -/
def forkLeft : Fin n := ⟨n - 2, by omega⟩

/-- The terminal coordinate in the standard type-`Dₙ` realization. -/
def forkRight : Fin n := ⟨n - 1, by omega⟩

/-- The successor of a nonterminal simple-root index. -/
def chainNext (i : Fin n) (hi : (i : ℕ) + 1 < n) : Fin n := ⟨(i : ℕ) + 1, hi⟩

/-- A chain node and its successor are distinct. -/
theorem ne_chainNext (i : Fin n) (hi : (i : ℕ) + 1 < n) : i ≠ chainNext n i hi := by
  intro h
  have := congrArg Fin.val h
  simp [chainNext] at this

/-- The two coordinates meeting at the fork are distinct. -/
theorem forkLeft_ne_forkRight : forkLeft n hn ≠ forkRight n hn := by
  intro h
  have := congrArg Fin.val h
  simp [forkLeft, forkRight] at this
  omega

private def forkBlock {K : Type*} [CommRing K] : Matrix (Fin n) (Fin n) K :=
  Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
    Matrix.single (forkRight n hn) (forkLeft n hn) 1

private theorem forkBlock_transpose {K : Type*} [CommRing K] :
    (forkBlock (K := K) n hn).transpose = -forkBlock n hn := by
  rw [forkBlock, Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single]
  abel

/-- The ambient raising matrix for the simple root at zero-based index `i`, namely Bourbaki node
`i + 1`, of type `Dₙ`.

For a chain node this is `E_{i,i+1} - E_{\bar{i+1},\bar i}`; at the fork node it is
`E_{n-2,\bar{n-1}} - E_{n-1,\bar{n-2}}`. -/
def raisingMatrix {K : Type*} [CommRing K] (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  if hi : (i : ℕ) + 1 < n then
    let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
    Matrix.fromBlocks A 0 0 (-A.transpose)
  else
    Matrix.fromBlocks 0 (forkBlock n hn) 0 0

/-- The lowering matrix is the transpose of the corresponding raising matrix. -/
def loweringMatrix {K : Type*} [CommRing K] (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  (raisingMatrix n hn i).transpose

@[simp]
theorem raisingMatrix_of_chain {K : Type*} [CommRing K] {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    raisingMatrix (K := K) n hn i =
      let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
      Matrix.fromBlocks A 0 0 (-A.transpose) := by
  simp [raisingMatrix, hi]

@[simp]
theorem raisingMatrix_of_fork {K : Type*} [CommRing K] {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) :
    raisingMatrix (K := K) n hn i =
      let B : Matrix (Fin n) (Fin n) K :=
        Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
          Matrix.single (forkRight n hn) (forkLeft n hn) 1
      Matrix.fromBlocks 0 B 0 0 := by
  simp [raisingMatrix, hi, forkBlock]

@[simp]
theorem loweringMatrix_of_chain {K : Type*} [CommRing K] {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    loweringMatrix (K := K) n hn i =
      let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
      Matrix.fromBlocks A.transpose 0 0 (-A) := by
  rw [loweringMatrix, raisingMatrix_of_chain n hn hi, Matrix.fromBlocks_transpose]
  simp

@[simp]
theorem loweringMatrix_of_fork {K : Type*} [CommRing K] {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) :
    loweringMatrix (K := K) n hn i =
      let B : Matrix (Fin n) (Fin n) K :=
        Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
          Matrix.single (forkRight n hn) (forkLeft n hn) 1
      Matrix.fromBlocks 0 0 (-B) 0 := by
  rw [loweringMatrix, raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_transpose]
  change Matrix.fromBlocks 0 0 (forkBlock (K := K) n hn).transpose 0 = _
  rw [forkBlock_transpose]
  rfl

private theorem fromBlocks_mem_typeD {K : Type*} [CommRing K]
    (A B C : Matrix (Fin n) (Fin n) K) (hB : B.transpose = -B) (hC : C.transpose = -C) :
    Matrix.fromBlocks A B C (-A.transpose) ∈ LieAlgebra.Orthogonal.typeD (Fin n) K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Membership in `typeD` unfolds to this ambient skew-adjoint matrix equation.
  change (Matrix.fromBlocks A B C (-A.transpose)).transpose *
      LieAlgebra.Orthogonal.JD (Fin n) K =
    LieAlgebra.Orthogonal.JD (Fin n) K *
      (-Matrix.fromBlocks A B C (-A.transpose))
  simp only [LieAlgebra.Orthogonal.JD, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.transpose_neg,
    Matrix.transpose_transpose, hB, hC, zero_mul, mul_zero, zero_add, add_zero,
    one_mul, mul_one, neg_neg]

/-- The explicit raising matrix is skew-adjoint for the split type-`D` Gram matrix. -/
theorem raisingMatrix_mem_typeD {K : Type*} [CommRing K] (i : Fin n) :
    raisingMatrix (K := K) n hn i ∈ LieAlgebra.Orthogonal.typeD (Fin n) K := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [raisingMatrix_of_chain n hn hi]
    exact fromBlocks_mem_typeD n _ 0 0 (by simp) (by simp)
  · rw [raisingMatrix_of_fork n hn hi]
    simpa only [forkBlock, Matrix.transpose_zero, neg_zero] using
      fromBlocks_mem_typeD (K := K) n 0 (forkBlock n hn) 0
      (forkBlock_transpose n hn) (by simp only [Matrix.transpose_zero, neg_zero])

/-- The transpose of an explicit raising matrix is again in the split type-`D` Lie algebra. -/
theorem loweringMatrix_mem_typeD {K : Type*} [CommRing K] (i : Fin n) :
    loweringMatrix (K := K) n hn i ∈ LieAlgebra.Orthogonal.typeD (Fin n) K := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [loweringMatrix, raisingMatrix_of_chain n hn hi,
      Matrix.fromBlocks_transpose]
    exact fromBlocks_mem_typeD n _ 0 0 (by simp) (by simp)
  · rw [loweringMatrix_of_fork n hn hi]
    simpa only [forkBlock, Matrix.transpose_zero, neg_zero] using
      fromBlocks_mem_typeD (K := K) n 0 0 (-forkBlock n hn)
      (by simp only [Matrix.transpose_zero, neg_zero]) (by
      rw [Matrix.transpose_neg, forkBlock_transpose])

/-- The raising and lowering generators, indexed by two copies of the zero-based Bourbaki nodes;
`Fin` index `i` represents node `i + 1`. -/
def rootGenerator {K : Type*} [CommRing K] :
    Fin n ⊕ Fin n → LieAlgebra.Orthogonal.typeD (Fin n) K
  | .inl i => ⟨raisingMatrix n hn i, raisingMatrix_mem_typeD n hn i⟩
  | .inr i => ⟨loweringMatrix n hn i, loweringMatrix_mem_typeD n hn i⟩

/-- The diagonal Cartan generator associated to the simple root at zero-based index `i`, namely
Bourbaki node `i + 1`. -/
def cartanGenerator {K : Type*} [CommRing K] (i : Fin n) :
    LieAlgebra.Orthogonal.typeD (Fin n) K :=
  ⟨typeDDiagonalMatrix (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)),
    typeDDiagonalMatrix_mem_typeD _⟩

@[simp]
theorem val_rootGenerator_inl {K : Type*} [CommRing K] (i : Fin n) :
    (rootGenerator (K := K) n hn (.inl i) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = raisingMatrix n hn i :=
  by simp [rootGenerator]

@[simp]
theorem val_rootGenerator_inr {K : Type*} [CommRing K] (i : Fin n) :
    (rootGenerator (K := K) n hn (.inr i) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = loweringMatrix n hn i :=
  by simp [rootGenerator]

@[simp]
theorem val_cartanGenerator {K : Type*} [CommRing K] (i : Fin n) :
    (cartanGenerator (K := K) n hn i :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        typeDDiagonalMatrix (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)) :=
  by simp [cartanGenerator]

/-! ## Cartan action -/

/-- The integral weight of a raising or lowering generator on the numbered Cartan generators: the
corresponding row of the type-`D` Cartan matrix for a raising generator and its negative for a
lowering generator. -/
def rootGeneratorWeight : Fin n ⊕ Fin n → Fin n → ℤ
  | .inl i => fun j => CartanMatrix.D n i j
  | .inr i => fun j => -CartanMatrix.D n i j

@[simp]
theorem rootGeneratorWeight_inl (i j : Fin n) :
    rootGeneratorWeight n (.inl i) j = CartanMatrix.D n i j := by
  simp [rootGeneratorWeight]

@[simp]
theorem rootGeneratorWeight_inr (i j : Fin n) :
    rootGeneratorWeight n (.inr i) j = -CartanMatrix.D n i j := by
  simp [rootGeneratorWeight]

private theorem chainCartanCoeff (i j : Fin n) (hi : (i : ℕ) + 1 < n) :
    DynkinType.typeDSimpleRoot n hn j i -
        DynkinType.typeDSimpleRoot n hn j (chainNext n i hi) = CartanMatrix.D n i j := by
  rw [← DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j,
    DynkinType.typeDSimpleRoot_of_add_one_lt hn hi, sub_dotProduct,
    single_dotProduct, single_dotProduct]
  simp [chainNext]

private theorem forkCartanCoeff (i j : Fin n) (hi : ¬(i : ℕ) + 1 < n) :
    DynkinType.typeDSimpleRoot n hn j (forkLeft n hn) +
        DynkinType.typeDSimpleRoot n hn j (forkRight n hn) = CartanMatrix.D n i j := by
  rw [← DynkinType.typeDSimpleRoot_dotProduct_typeDSimpleRoot hn i j,
    DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi, add_dotProduct,
    single_dotProduct, single_dotProduct]
  simp [forkLeft, forkRight]

/-- The numbered Cartan generators act on the numbered root generators through the type-`D`
Cartan matrix, with the opposite weight on lowering generators. -/
theorem lie_cartanGenerator_rootGenerator {K : Type*} [CommRing K]
    (k : Fin n ⊕ Fin n) (j : Fin n) :
    ⁅cartanGenerator (K := K) n hn j, rootGenerator (K := K) n hn k⁆ =
      ((rootGeneratorWeight n k j : ℤ) : K) • rootGenerator (K := K) n hn k := by
  apply Subtype.ext
  cases k with
  | inl i =>
      rw [LieSubalgebra.coe_bracket, SetLike.val_smul, val_cartanGenerator,
        val_rootGenerator_inl, rootGeneratorWeight_inl]
      change ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
          raisingMatrix n hn i⁆ = (CartanMatrix.D n i j : K) • raisingMatrix n hn i
      by_cases hi : (i : ℕ) + 1 < n
      · rw [raisingMatrix_of_chain n hn hi]
        have hcoeff := congrArg (fun z : ℤ => (z : K)) (chainCartanCoeff n hn i j hi)
        simp only [Int.cast_sub] at hcoeff
        ext (a | a) (b | b)
        · simp only [Matrix.transpose_single, typeDDiagonalMatrix_lie_apply,
            typeDDiagonalValue_inl, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul,
            Matrix.single_apply]
          split_ifs with h
          · rcases h with ⟨rfl, rfl⟩
            simpa only [mul_one] using hcoeff
          · simp only [mul_zero]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp only [Matrix.transpose_single, typeDDiagonalMatrix_lie_apply,
            typeDDiagonalValue_inr, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply,
            Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
          split_ifs with h
          · rcases h with ⟨rfl, rfl⟩
            linear_combination -hcoeff
          · simp only [neg_zero, mul_zero]
      · rw [raisingMatrix_of_fork n hn hi]
        have hcoeff := congrArg (fun z : ℤ => (z : K)) (forkCartanCoeff n hn i j hi)
        simp only [Int.cast_add] at hcoeff
        have hne := forkLeft_ne_forkRight n hn
        ext (a | a) (b | b)
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · by_cases h₁ : forkLeft n hn = a ∧ forkRight n hn = b
          · have h₂ : ¬(forkRight n hn = a ∧ forkLeft n hn = b) := by
              rintro ⟨hra, hlb⟩
              exact forkLeft_ne_forkRight n hn (h₁.1.trans hra.symm)
            rcases h₁ with ⟨rfl, rfl⟩
            simpa [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, Matrix.single_apply, hne]
              using hcoeff
          · by_cases h₂ : forkRight n hn = a ∧ forkLeft n hn = b
            · rcases h₂ with ⟨rfl, rfl⟩
              simpa [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, Matrix.single_apply,
                hne, add_comm] using congrArg Neg.neg hcoeff
            · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, h₁, h₂]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
  | inr i =>
      rw [LieSubalgebra.coe_bracket, SetLike.val_smul, val_cartanGenerator,
        val_rootGenerator_inr, rootGeneratorWeight_inr, Int.cast_neg]
      change ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
          loweringMatrix n hn i⁆ = (-CartanMatrix.D n i j : K) • loweringMatrix n hn i
      by_cases hi : (i : ℕ) + 1 < n
      · rw [loweringMatrix_of_chain n hn hi]
        have hcoeff := congrArg (fun z : ℤ => (z : K)) (chainCartanCoeff n hn i j hi)
        simp only [Int.cast_sub] at hcoeff
        ext (a | a) (b | b)
        · simp only [Matrix.transpose_single, typeDDiagonalMatrix_lie_apply,
            typeDDiagonalValue_inl, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, smul_eq_mul,
            Matrix.single_apply]
          split_ifs with h
          · rcases h with ⟨rfl, rfl⟩
            linear_combination -hcoeff
          · simp only [mul_zero]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp only [typeDDiagonalMatrix_lie_apply, typeDDiagonalValue_inr,
            Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
            Matrix.single_apply]
          split_ifs with h
          · rcases h with ⟨rfl, rfl⟩
            linear_combination hcoeff
          · simp only [neg_zero, mul_zero]
      · rw [loweringMatrix_of_fork n hn hi]
        have hcoeff := congrArg (fun z : ℤ => (z : K)) (forkCartanCoeff n hn i j hi)
        simp only [Int.cast_add] at hcoeff
        have hne := forkLeft_ne_forkRight n hn
        ext (a | a) (b | b)
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]
        · by_cases h₁ : forkRight n hn = a ∧ forkLeft n hn = b
          · have h₂ : ¬(forkLeft n hn = a ∧ forkRight n hn = b) := by
              rintro ⟨hla, hrb⟩
              exact forkLeft_ne_forkRight n hn (hla.trans h₁.1.symm)
            rcases h₁ with ⟨rfl, rfl⟩
            simpa [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, Matrix.single_apply,
              hne, sub_eq_add_neg, add_comm] using (congrArg Neg.neg hcoeff)
          · by_cases h₂ : forkLeft n hn = a ∧ forkRight n hn = b
            · rcases h₂ with ⟨rfl, rfl⟩
              simpa [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, Matrix.single_apply,
                hne, add_comm] using hcoeff
            · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks, h₁, h₂]
        · simp [typeDDiagonalMatrix_lie_apply, Matrix.fromBlocks]

/-! ## Nilpotence in the standard representation -/

/-- A raising generator squares to zero as an endomorphism of the standard split module. -/
@[simp]
theorem raisingMatrix_mul_self {K : Type*} [CommRing K] (i : Fin n) :
    raisingMatrix (K := K) n hn i * raisingMatrix n hn i = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [raisingMatrix_of_chain n hn hi, Matrix.fromBlocks_multiply]
    have hne := ne_chainNext n i hi
    simp [Matrix.transpose_single, Matrix.single_mul_single_of_ne, hne, hne.symm]
  · rw [raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_multiply]
    simp

/-- A lowering generator squares to zero as an endomorphism of the standard split module. -/
@[simp]
theorem loweringMatrix_mul_self {K : Type*} [CommRing K] (i : Fin n) :
    loweringMatrix (K := K) n hn i * loweringMatrix n hn i = 0 := by
  rw [loweringMatrix, ← Matrix.transpose_mul, raisingMatrix_mul_self n hn i]
  simp

/-- Every numbered type-`D` root generator squares to zero in the standard representation. -/
@[simp]
theorem val_rootGenerator_mul_self {K : Type*} [CommRing K] (k : Fin n ⊕ Fin n) :
    (rootGenerator (K := K) n hn k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (rootGenerator (K := K) n hn k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 0 := by
  cases k with
  | inl i => simp
  | inr i => simp

end TauCeti.TypeDStd
