/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic

/-!
# The numbered simple-root generators of the split type-D Lie algebra

For `4 ≤ n`, this file puts the Bourbaki-numbered Chevalley generators of the split orthogonal
Lie algebra `LieAlgebra.Orthogonal.typeD (Fin n) K` into explicit matrix form. In the hyperbolic
basis, whose Gram matrix is

```text
[ 0  1 ]
[ 1  0 ],
```

the chain generator for `αᵢ = εᵢ - εᵢ₊₁` is

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
* `TauCeti.TypeDStd.cartanGenerator`: the Bourbaki-numbered diagonal Cartan generators.
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

/-- The ambient raising matrix for the `i`-th Bourbaki simple root of type `Dₙ`.

For a chain node this is `E_{i,i+1} - E_{\bar{i+1},\bar i}`; at the fork node it is
`E_{n-2,\bar{n-1}} - E_{n-1,\bar{n-2}}`. -/
def raisingMatrix {K : Type*} [CommRing K] (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  if hi : (i : ℕ) + 1 < n then
    let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
    Matrix.fromBlocks A 0 0 (-A.transpose)
  else
    let B : Matrix (Fin n) (Fin n) K :=
      Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
        Matrix.single (forkRight n hn) (forkLeft n hn) 1
    Matrix.fromBlocks 0 B 0 0

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
  simp [raisingMatrix, hi]

private theorem fromBlocks_mem_typeD {K : Type*} [CommRing K]
    (A B C : Matrix (Fin n) (Fin n) K) (hB : B.transpose = -B) (hC : C.transpose = -C) :
    Matrix.fromBlocks A B C (-A.transpose) ∈ LieAlgebra.Orthogonal.typeD (Fin n) K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
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
    let B : Matrix (Fin n) (Fin n) K :=
      Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
        Matrix.single (forkRight n hn) (forkLeft n hn) 1
    change Matrix.fromBlocks 0 B 0 0 ∈ LieAlgebra.Orthogonal.typeD (Fin n) K
    simpa using fromBlocks_mem_typeD n 0 B 0 (by
      dsimp only [B]
      rw [Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single]
      abel) (by simp)

/-- The transpose of an explicit raising matrix is again in the split type-`D` Lie algebra. -/
theorem loweringMatrix_mem_typeD {K : Type*} [CommRing K] (i : Fin n) :
    loweringMatrix (K := K) n hn i ∈ LieAlgebra.Orthogonal.typeD (Fin n) K := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [loweringMatrix, raisingMatrix_of_chain n hn hi,
      Matrix.fromBlocks_transpose]
    exact fromBlocks_mem_typeD n _ 0 0 (by simp) (by simp)
  · let B : Matrix (Fin n) (Fin n) K :=
      Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
        Matrix.single (forkRight n hn) (forkLeft n hn) 1
    have hB : B.transpose = -B := by
      dsimp only [B]
      rw [Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single]
      abel
    rw [loweringMatrix, raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_transpose]
    change Matrix.fromBlocks 0 0 B.transpose 0 ∈ LieAlgebra.Orthogonal.typeD (Fin n) K
    simpa using fromBlocks_mem_typeD n 0 0 B.transpose (by simp) (by
      rw [Matrix.transpose_transpose, hB]
      simp)

/-- The raising and lowering generators, indexed by two copies of the Bourbaki nodes. -/
def rootGenerator {K : Type*} [CommRing K] :
    Fin n ⊕ Fin n → LieAlgebra.Orthogonal.typeD (Fin n) K
  | .inl i => ⟨raisingMatrix n hn i, raisingMatrix_mem_typeD n hn i⟩
  | .inr i => ⟨loweringMatrix n hn i, loweringMatrix_mem_typeD n hn i⟩

/-- The diagonal Cartan generator associated to a Bourbaki simple root. -/
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

/-! ## Nilpotence in the standard representation -/

/-- A raising generator squares to zero as an endomorphism of the standard split module. -/
theorem raisingMatrix_mul_self {K : Type*} [CommRing K] (i : Fin n) :
    raisingMatrix (K := K) n hn i * raisingMatrix n hn i = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [raisingMatrix_of_chain n hn hi, Matrix.fromBlocks_multiply]
    have hne := ne_chainNext n i hi
    simp [Matrix.transpose_single, Matrix.single_mul_single_of_ne, hne, hne.symm]
  · rw [raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_multiply]
    simp

/-- A lowering generator squares to zero as an endomorphism of the standard split module. -/
theorem loweringMatrix_mul_self {K : Type*} [CommRing K] (i : Fin n) :
    loweringMatrix (K := K) n hn i * loweringMatrix n hn i = 0 := by
  rw [loweringMatrix, ← Matrix.transpose_mul, raisingMatrix_mul_self n hn i]
  simp

/-- Every numbered type-`D` root generator squares to zero in the standard representation. -/
theorem val_rootGenerator_mul_self {K : Type*} [CommRing K] (k : Fin n ⊕ Fin n) :
    (rootGenerator (K := K) n hn k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (rootGenerator (K := K) n hn k : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = 0 := by
  cases k with
  | inl i => simpa using raisingMatrix_mul_self (K := K) n hn i
  | inr i => simpa using loweringMatrix_mul_self (K := K) n hn i

end TauCeti.TypeDStd
