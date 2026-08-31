/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.DiagonalCartan
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

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
* `TauCeti.TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and
  `TauCeti.TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex`: that weight is the
  correspondingly numbered simple root of `TauCeti.DynkinType.simplyConnectedRootDatum` at
  `TauCeti.DynkinType.D n`, respectively its negative.
* `TauCeti.TypeDStd.lie_cartanGenerator_rootGenerator`: the Cartan action on the generators.
* `TauCeti.TypeDStd.lie_rootGenerator_inl_inr`: the raising--lowering bracket relations.
* `TauCeti.TypeDStd.lie_rootGenerator_inl_inl_of_cartan_eq_zero`: nonadjacent same-sign
  generators commute.
* `TauCeti.TypeDStd.lie_rootGenerator_inl_lie_rootGenerator_inl`: the adjacent-node Serre
  relations, with a corresponding lowering-generator theorem.
* `TauCeti.TypeDStd.val_rootGenerator_mul_self`: every numbered generator is square-zero in the
  standard representation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§11, 25.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* The combined-generator interface adapts `LieAlgebra.Basis.rootGenerator`,
  `LieAlgebra.Basis.rootGeneratorWeight`, and `LieAlgebra.Basis.lie_h_rootGenerator` from
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Basis`.
* The two named-root identifications follow the formal template of
  `TauCeti.SpStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and its lowering counterpart in
  `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.RootDatum`, specialized to type `D`.

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

private def forkBlock {K : Type*} [Ring K] : Matrix (Fin n) (Fin n) K :=
  Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
    Matrix.single (forkRight n hn) (forkLeft n hn) 1

private theorem forkBlock_transpose {K : Type*} [Ring K] :
    (forkBlock (K := K) n hn).transpose = -forkBlock n hn := by
  rw [forkBlock, Matrix.transpose_sub, Matrix.transpose_single, Matrix.transpose_single]
  abel

/-- The ambient raising matrix for the simple root at zero-based index `i`, namely Bourbaki node
`i + 1`, of type `Dₙ`.

For a chain node this is `E_{i,i+1} - E_{\bar{i+1},\bar i}`; at the fork node it is
`E_{n-2,\bar{n-1}} - E_{n-1,\bar{n-2}}`. -/
def raisingMatrix {K : Type*} [Ring K] (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  if hi : (i : ℕ) + 1 < n then
    let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
    Matrix.fromBlocks A 0 0 (-A.transpose)
  else
    Matrix.fromBlocks 0 (forkBlock n hn) 0 0

/-- The lowering matrix is the transpose of the corresponding raising matrix. -/
def loweringMatrix {K : Type*} [Ring K] (i : Fin n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  (raisingMatrix n hn i).transpose

@[simp]
theorem raisingMatrix_of_chain {K : Type*} [Ring K] {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    raisingMatrix (K := K) n hn i =
      let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
      Matrix.fromBlocks A 0 0 (-A.transpose) := by
  simp [raisingMatrix, hi]

@[simp]
theorem raisingMatrix_of_fork {K : Type*} [Ring K] {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) :
    raisingMatrix (K := K) n hn i =
      let B : Matrix (Fin n) (Fin n) K :=
        Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
          Matrix.single (forkRight n hn) (forkLeft n hn) 1
      Matrix.fromBlocks 0 B 0 0 := by
  simp [raisingMatrix, hi, forkBlock]

@[simp]
theorem loweringMatrix_of_chain {K : Type*} [Ring K] {i : Fin n}
    (hi : (i : ℕ) + 1 < n) :
    loweringMatrix (K := K) n hn i =
      let A : Matrix (Fin n) (Fin n) K := Matrix.single i (chainNext n i hi) 1
      Matrix.fromBlocks A.transpose 0 0 (-A) := by
  rw [loweringMatrix, raisingMatrix_of_chain n hn hi, Matrix.fromBlocks_transpose]
  simp

@[simp]
theorem loweringMatrix_of_fork {K : Type*} [Ring K] {i : Fin n}
    (hi : ¬(i : ℕ) + 1 < n) :
    loweringMatrix (K := K) n hn i =
      let B : Matrix (Fin n) (Fin n) K :=
        Matrix.single (forkLeft n hn) (forkRight n hn) 1 -
          Matrix.single (forkRight n hn) (forkLeft n hn) 1
      Matrix.fromBlocks 0 0 (-B) 0 := by
  rw [loweringMatrix, raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_transpose]
  -- The branch equation uses a local `B`; expose its definition as `forkBlock` so that the
  -- private transpose lemma can rewrite the lower-left block.
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

/-! ### The numbered generators sit at the named simple roots

Neither identification below is a `simp` lemma. Their left-hand sides are already `simp`-normal:
`rootGeneratorWeight_inl` and `rootGeneratorWeight_inr` rewrite an applied weight to an entry of
`CartanMatrix.D n`, and orienting these identifications towards the datum would undo that. -/

/-- **The weight of the `i`-th raising generator is the `i`-th simple root of the uniform pinned
type-`Dₙ` datum.** This is the dispatcher form consumed by a construction indexed by a Dynkin
type rather than by an explicit orthogonal Lie algebra. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex (i : Fin n) :
    rootGeneratorWeight n (.inl i) =
      ((DynkinType.D n).simplyConnectedRootDatum (DynkinType.valid_D.mpr hn)).root
        ((DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i) := by
  -- The rank of `D n` is definitionally `n`, but the dependent root index prevents rewriting the
  -- dispatcher equation directly. Both sides are instead identified with the Cartan-matrix row.
  refine Eq.trans ?_
    (DynkinType.root_simpleIndex (DynkinType.D n) (DynkinType.valid_D.mpr hn) i).symm
  rw [DynkinType.cartanMatrix_D]
  funext j
  rw [rootGeneratorWeight_inl]

/-- **The weight of the `i`-th lowering generator is the negative of the `i`-th simple root of the
uniform pinned type-`Dₙ` datum.** -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex (i : Fin n) :
    rootGeneratorWeight n (.inr i) =
      -((DynkinType.D n).simplyConnectedRootDatum (DynkinType.valid_D.mpr hn)).root
        ((DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i) := by
  -- Relating the two signs first keeps that step indexed by `Fin n`, rather than by the
  -- definitionally equal but differently spelled rank of `D n` that the root datum carries.
  have hneg : rootGeneratorWeight n (.inr i) = -rootGeneratorWeight n (.inl i) := by
    funext j
    simp only [rootGeneratorWeight_inr, Pi.neg_apply, rootGeneratorWeight_inl]
  exact hneg.trans (congrArg Neg.neg (rootGeneratorWeight_inl_eq_root_simpleIndex n hn i))

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

private theorem lie_typeDDiagonalMatrix_raisingMatrix_of_chain {K : Type*} [CommRing K]
    (i j : Fin n) (hi : (i : ℕ) + 1 < n) :
    ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        raisingMatrix (K := K) n hn i⁆ =
      (CartanMatrix.D n i j : K) • raisingMatrix n hn i := by
  rw [raisingMatrix_of_chain n hn hi]
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

private theorem lie_typeDDiagonalMatrix_raisingMatrix_of_fork {K : Type*} [CommRing K]
    (i j : Fin n) (hi : ¬(i : ℕ) + 1 < n) :
    ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        raisingMatrix (K := K) n hn i⁆ =
      (CartanMatrix.D n i j : K) • raisingMatrix n hn i := by
  rw [raisingMatrix_of_fork n hn hi]
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

private theorem lie_typeDDiagonalMatrix_raisingMatrix {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        raisingMatrix (K := K) n hn i⁆ =
      (CartanMatrix.D n i j : K) • raisingMatrix n hn i := by
  by_cases hi : (i : ℕ) + 1 < n
  · exact lie_typeDDiagonalMatrix_raisingMatrix_of_chain n hn i j hi
  · exact lie_typeDDiagonalMatrix_raisingMatrix_of_fork n hn i j hi

private theorem lie_typeDDiagonalMatrix_loweringMatrix {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        loweringMatrix (K := K) n hn i⁆ =
      (-CartanMatrix.D n i j : K) • loweringMatrix n hn i := by
  rw [loweringMatrix]
  apply Matrix.transpose_injective
  calc
    (⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        (raisingMatrix n hn i).transpose⁆).transpose =
        ⁅raisingMatrix n hn i,
          (typeDDiagonalMatrix
            (fun a => (DynkinType.typeDSimpleRoot n hn j a : K))).transpose⁆ :=
      Matrix.lie_transpose _ _
    _ = ⁅raisingMatrix n hn i,
        typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K))⁆ := by
      congr 1
      ext a b
      by_cases hab : a = b
      · subst b
        simp [typeDDiagonalMatrix_apply]
      · have hba : b ≠ a := Ne.symm hab
        simp [typeDDiagonalMatrix_apply, hab, hba]
    _ = -⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
        raisingMatrix n hn i⁆ := by rw [← lie_skew]
    _ = -((CartanMatrix.D n i j : K) • raisingMatrix n hn i) := by
      rw [lie_typeDDiagonalMatrix_raisingMatrix n hn i j]
    _ = ((-CartanMatrix.D n i j : K) •
        (raisingMatrix n hn i).transpose).transpose := by simp

/-- The numbered Cartan generators act on the numbered root generators through the type-`D`
Cartan matrix, with the opposite weight on lowering generators. -/
@[simp]
theorem lie_cartanGenerator_rootGenerator {K : Type*} [CommRing K]
    (k : Fin n ⊕ Fin n) (j : Fin n) :
    ⁅cartanGenerator (K := K) n hn j, rootGenerator (K := K) n hn k⁆ =
      ((rootGeneratorWeight n k j : ℤ) : K) • rootGenerator (K := K) n hn k := by
  apply Subtype.ext
  cases k with
  | inl i =>
      rw [LieSubalgebra.coe_bracket, SetLike.val_smul, val_cartanGenerator,
        val_rootGenerator_inl, rootGeneratorWeight_inl]
      -- The subtype coercions have been rewritten away; state the resulting ambient matrix goal
      -- explicitly so that the private Cartan-action lemma applies.
      change ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
          raisingMatrix n hn i⁆ = (CartanMatrix.D n i j : K) • raisingMatrix n hn i
      exact lie_typeDDiagonalMatrix_raisingMatrix n hn i j
  | inr i =>
      rw [LieSubalgebra.coe_bracket, SetLike.val_smul, val_cartanGenerator,
        val_rootGenerator_inr, rootGeneratorWeight_inr, Int.cast_neg]
      -- As in the raising case, this bridge exposes the ambient matrix equality hidden by the
      -- Lie-subalgebra and scalar-action coercions.
      change ⁅typeDDiagonalMatrix (fun a => (DynkinType.typeDSimpleRoot n hn j a : K)),
          loweringMatrix n hn i⁆ = (-CartanMatrix.D n i j : K) • loweringMatrix n hn i
      exact lie_typeDDiagonalMatrix_loweringMatrix n hn i j

/-! ## Generator brackets -/

/-- The numbered Cartan generators commute. -/
@[simp]
theorem lie_cartanGenerator_cartanGenerator {K : Type*} [CommRing K] (i j : Fin n) :
    ⁅cartanGenerator (K := K) n hn i, cartanGenerator (K := K) n hn j⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_cartanGenerator, val_cartanGenerator]
  have hdiag (k : Fin n) :
      (typeDDiagonalMatrix
        (fun a => (DynkinType.typeDSimpleRoot n hn k a : K))).IsDiag := by
    intro a b hab
    rw [typeDDiagonalMatrix_apply, ite_eq_right hab]
  exact lie_eq_zero_of_isDiag (hdiag i) (hdiag j)

private theorem lie_raisingMatrix_loweringMatrix_self {K : Type*} [CommRing K] (i : Fin n) :
    ⁅raisingMatrix (K := K) n hn i, loweringMatrix (K := K) n hn i⁆ =
      typeDDiagonalMatrix (fun j => (DynkinType.typeDSimpleRoot n hn i j : K)) := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [raisingMatrix_of_chain n hn hi, loweringMatrix_of_chain n hn hi,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, DynkinType.typeDSimpleRoot_of_add_one_lt hn hi]
    ext (a | a) (b | b) <;>
      by_cases hab : a = b
    all_goals simp_all [Matrix.fromBlocks, typeDDiagonalMatrix_apply,
      Matrix.transpose_single, Matrix.single_apply, Pi.single_apply, chainNext,
      eq_comm, Fin.ext_iff]
    all_goals omega
  · rw [raisingMatrix_of_fork n hn hi, loweringMatrix_of_fork n hn hi,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.sub_mul, Matrix.mul_sub,
      DynkinType.typeDSimpleRoot_of_not_add_one_lt hn hi]
    have hne : (⟨n - 2, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      simp [Fin.ext_iff] at h
      omega
    ext (a | a) (b | b) <;>
      by_cases hab : a = b
    all_goals simp_all [Matrix.fromBlocks, typeDDiagonalMatrix_apply, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.single_apply, Pi.single_apply, forkLeft, forkRight,
      eq_comm, Fin.ext_iff]
    all_goals split_ifs <;> simp_all [add_comm]

private theorem lie_raisingMatrix_loweringMatrix_chain_fork {K : Type*} [CommRing K]
    (i j : Fin n) (hi : (i : ℕ) + 1 < n) (hj : ¬(j : ℕ) + 1 < n) :
    ⁅raisingMatrix (K := K) n hn i, loweringMatrix (K := K) n hn j⁆ = 0 := by
  have hir : i ≠ forkRight n hn := by
    intro h
    simp [forkRight, Fin.ext_iff] at h
    omega
  by_cases hil : i = forkLeft n hn
  · subst i
    have hne := forkLeft_ne_forkRight n hn
    have hinext : chainNext n (forkLeft n hn) hi = forkRight n hn := by
      apply Fin.ext
      simp [chainNext, forkLeft, forkRight]
      omega
    rw [raisingMatrix_of_chain n hn hi, loweringMatrix_of_fork n hn hj,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    ext (a | a) (b | b) <;>
      simp [Matrix.fromBlocks, Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_single,
        hinext, hne, hne.symm]
  · rw [raisingMatrix_of_chain n hn hi, loweringMatrix_of_fork n hn hj,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    ext (a | a) (b | b) <;>
      simp [Matrix.fromBlocks, Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_single,
        hil, Ne.symm hil, hir, Ne.symm hir]

private theorem lie_raisingMatrix_loweringMatrix_of_ne {K : Type*} [CommRing K]
    (i j : Fin n) (hij : i ≠ j) :
    ⁅raisingMatrix (K := K) n hn i, loweringMatrix (K := K) n hn j⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · have hnext : chainNext n i hi ≠ chainNext n j hj := by
        intro h
        apply hij
        apply Fin.ext
        simp [chainNext, Fin.ext_iff] at h ⊢
        omega
      rw [raisingMatrix_of_chain n hn hi, loweringMatrix_of_chain n hn hj,
        LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_multiply]
      ext (a | a) (b | b) <;>
        simp [Matrix.fromBlocks, Matrix.transpose_single, hij, hij.symm, hnext, hnext.symm]
    · exact lie_raisingMatrix_loweringMatrix_chain_fork n hn i j hi hj
  · by_cases hj : (j : ℕ) + 1 < n
    · apply Matrix.transpose_injective
      rw [Matrix.lie_transpose]
      simpa [loweringMatrix] using
        lie_raisingMatrix_loweringMatrix_chain_fork (K := K) n hn j i hj hi
    · exfalso
      apply hij
      apply Fin.ext
      have hi' := i.isLt
      have hj' := j.isLt
      omega

private theorem lie_raisingMatrix_raisingMatrix_chain_chain_of_cartan_eq_zero
    {K : Type*} [CommRing K] (i j : Fin n) (hi : (i : ℕ) + 1 < n)
    (hj : (j : ℕ) + 1 < n) (hij : CartanMatrix.D n i j = 0) :
    ⁅raisingMatrix (K := K) n hn i, raisingMatrix (K := K) n hn j⁆ = 0 := by
  have hi' := i.isLt
  have hj' := j.isLt
  have hforward : chainNext n i hi ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [chainNext] at hval
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at hij
    split_ifs at hij <;> omega
  have hback : chainNext n j hj ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    simp only [chainNext] at hval
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at hij
    split_ifs at hij <;> omega
  rw [raisingMatrix_of_chain n hn hi, raisingMatrix_of_chain n hn hj,
    LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [Matrix.transpose_single, Matrix.single_mul_single_of_ne _ _ _ _ hforward,
    Matrix.single_mul_single_of_ne _ _ _ _ hback, hforward.symm, hback.symm]

private theorem lie_raisingMatrix_raisingMatrix_chain_fork_of_cartan_eq_zero
    {K : Type*} [CommRing K] (i j : Fin n) (hi : (i : ℕ) + 1 < n)
    (hj : ¬(j : ℕ) + 1 < n) (hij : CartanMatrix.D n i j = 0) :
    ⁅raisingMatrix (K := K) n hn i, raisingMatrix (K := K) n hn j⁆ = 0 := by
  have hi' := i.isLt
  have hj' := j.isLt
  have hne := forkLeft_ne_forkRight n hn
  have hjfork : j = forkRight n hn := by
    apply Fin.ext
    simp [forkRight]
    omega
  by_cases hil : i = forkLeft n hn
  · subst i
    have hinext : chainNext n (forkLeft n hn) hi = forkRight n hn := by
      apply Fin.ext
      simp [chainNext, forkLeft, forkRight]
      omega
    rw [raisingMatrix_of_chain n hn hi, raisingMatrix_of_fork n hn hj,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [Matrix.transpose_single, Matrix.mul_sub, Matrix.sub_mul, hinext, hne, hne.symm]
  · have hinextl : chainNext n i hi ≠ forkLeft n hn := by
      intro h
      have hval := congrArg Fin.val h
      simp only [chainNext, forkLeft] at hval
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at hij
      split_ifs at hij <;> omega
    have hinextr : chainNext n i hi ≠ forkRight n hn := by
      intro h
      have hval := congrArg Fin.val h
      simp only [chainNext, forkRight] at hval
      apply hil
      apply Fin.ext
      simp [forkLeft]
      omega
    rw [raisingMatrix_of_chain n hn hi, raisingMatrix_of_fork n hn hj,
      LieRing.of_associative_ring_bracket, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [Matrix.transpose_single, Matrix.mul_sub, Matrix.sub_mul, hinextl, hinextr,
      hinextl.symm, hinextr.symm]

private theorem lie_raisingMatrix_raisingMatrix_of_cartan_eq_zero
    {K : Type*} [CommRing K] (i j : Fin n) (hij : CartanMatrix.D n i j = 0) :
    ⁅raisingMatrix (K := K) n hn i, raisingMatrix (K := K) n hn j⁆ = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · exact lie_raisingMatrix_raisingMatrix_chain_chain_of_cartan_eq_zero
        n hn i j hi hj hij
    · exact lie_raisingMatrix_raisingMatrix_chain_fork_of_cartan_eq_zero n hn i j hi hj hij
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [← lie_skew]
      have hji : CartanMatrix.D n j i = 0 := by
        exact ((CartanMatrix.D_isSymm n).apply j i).symm.trans hij
      rw [lie_raisingMatrix_raisingMatrix_chain_fork_of_cartan_eq_zero n hn j i hj hi hji,
        neg_zero]
    · have heq : i = j := by
        apply Fin.ext
        have hi' := i.isLt
        have hj' := j.isLt
        omega
      subst j
      simp [CartanMatrix.D] at hij

/-- A raising generator squares to zero as an endomorphism of the standard split module. -/
@[simp]
theorem raisingMatrix_mul_self {K : Type*} [Ring K] (i : Fin n) :
    raisingMatrix (K := K) n hn i * raisingMatrix n hn i = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [raisingMatrix_of_chain n hn hi, Matrix.fromBlocks_multiply]
    have hne := ne_chainNext n i hi
    simp [Matrix.transpose_single, Matrix.single_mul_single_of_ne, hne, hne.symm]
  · rw [raisingMatrix_of_fork n hn hi, Matrix.fromBlocks_multiply]
    simp

private theorem raisingMatrix_mul_raisingMatrix_mul_self {K : Type*} [CommRing K]
    (i j : Fin n) :
    raisingMatrix (K := K) n hn i * raisingMatrix (K := K) n hn j *
        raisingMatrix (K := K) n hn i = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [raisingMatrix_of_chain n hn hi, raisingMatrix_of_chain n hn hj,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      ext (a | a) (b | b) <;>
        simp [Matrix.fromBlocks, Matrix.transpose_single, Matrix.single_mul_mul_single,
          Matrix.single_apply, chainNext, Fin.ext_iff] <;>
        omega
    · rw [raisingMatrix_of_chain n hn hi, raisingMatrix_of_fork n hn hj,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      have hne := forkLeft_ne_forkRight n hn
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_single,
        Matrix.single_mul_mul_single, Matrix.single_apply]
      split_ifs with h₁ h₂ <;> simp_all
  · by_cases hj : (j : ℕ) + 1 < n
    · rw [raisingMatrix_of_fork n hn hi, raisingMatrix_of_chain n hn hj,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp
    · rw [raisingMatrix_of_fork n hn hi, raisingMatrix_of_fork n hn hj,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp

private theorem lie_raisingMatrix_lie_raisingMatrix {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅raisingMatrix (K := K) n hn i,
      ⁅raisingMatrix (K := K) n hn i, raisingMatrix (K := K) n hn j⁆⁆ = 0 := by
  have hleft : raisingMatrix (K := K) n hn i *
      (raisingMatrix n hn i * raisingMatrix n hn j) = 0 := by
    rw [← mul_assoc, raisingMatrix_mul_self n hn i, zero_mul]
  have hmiddle : raisingMatrix (K := K) n hn i *
      (raisingMatrix n hn j * raisingMatrix n hn i) = 0 := by
    rw [← mul_assoc, raisingMatrix_mul_raisingMatrix_mul_self n hn i j]
  have hmiddle' : (raisingMatrix (K := K) n hn i * raisingMatrix n hn j) *
      raisingMatrix n hn i = 0 := raisingMatrix_mul_raisingMatrix_mul_self n hn i j
  have hright : (raisingMatrix (K := K) n hn j * raisingMatrix n hn i) *
      raisingMatrix n hn i = 0 := by
    rw [mul_assoc, raisingMatrix_mul_self n hn i, mul_zero]
  rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket]
  rw [Matrix.mul_sub, Matrix.sub_mul, hleft, hmiddle, hmiddle', hright]
  simp

private theorem lie_loweringMatrix_loweringMatrix_of_cartan_eq_zero
    {K : Type*} [CommRing K] (i j : Fin n) (hij : CartanMatrix.D n i j = 0) :
    ⁅loweringMatrix (K := K) n hn i, loweringMatrix (K := K) n hn j⁆ = 0 := by
  have hji : CartanMatrix.D n j i = 0 :=
    ((CartanMatrix.D_isSymm n).apply j i).symm.trans hij
  apply Matrix.transpose_injective
  rw [Matrix.lie_transpose]
  simpa [loweringMatrix] using
    lie_raisingMatrix_raisingMatrix_of_cartan_eq_zero (K := K) n hn j i hji

private theorem lie_loweringMatrix_lie_loweringMatrix {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅loweringMatrix (K := K) n hn i,
      ⁅loweringMatrix (K := K) n hn i, loweringMatrix (K := K) n hn j⁆⁆ = 0 := by
  apply Matrix.transpose_injective
  rw [Matrix.lie_transpose, Matrix.lie_transpose]
  simp only [loweringMatrix, Matrix.transpose_transpose, Matrix.transpose_zero]
  rw [← lie_skew (raisingMatrix n hn j) (raisingMatrix n hn i), neg_lie,
    lie_skew (raisingMatrix n hn i) (⁅raisingMatrix n hn i, raisingMatrix n hn j⁆)]
  exact lie_raisingMatrix_lie_raisingMatrix n hn i j

/-- Raising generators at nonadjacent type-`D` nodes commute. -/
@[simp]
theorem lie_rootGenerator_inl_inl_of_cartan_eq_zero {K : Type*} [CommRing K]
    {i j : Fin n} (hij : CartanMatrix.D n i j = 0) :
    ⁅rootGenerator (K := K) n hn (.inl i), rootGenerator (K := K) n hn (.inl j)⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_rootGenerator_inl, val_rootGenerator_inl]
  -- Rewriting removes the subtype coercions but leaves the ambient bracket definition folded;
  -- expose the matrix equality so that the private bracket lemma applies.
  change ⁅raisingMatrix n hn i, raisingMatrix n hn j⁆ = 0
  exact lie_raisingMatrix_raisingMatrix_of_cartan_eq_zero n hn i j hij

/-- Lowering generators at nonadjacent type-`D` nodes commute. -/
@[simp]
theorem lie_rootGenerator_inr_inr_of_cartan_eq_zero {K : Type*} [CommRing K]
    {i j : Fin n} (hij : CartanMatrix.D n i j = 0) :
    ⁅rootGenerator (K := K) n hn (.inr i), rootGenerator (K := K) n hn (.inr j)⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_rootGenerator_inr, val_rootGenerator_inr]
  -- As in the raising case, state the ambient matrix equality hidden by the Lie-subalgebra
  -- bracket before applying the private bracket lemma.
  change ⁅loweringMatrix n hn i, loweringMatrix n hn j⁆ = 0
  exact lie_loweringMatrix_loweringMatrix_of_cartan_eq_zero n hn i j hij

/-- The raising generators satisfy the simply-laced type-`D` adjacent-node Serre relation.
The formula holds for every pair of nodes, including the nonadjacent and diagonal cases. -/
@[simp]
theorem lie_rootGenerator_inl_lie_rootGenerator_inl {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅rootGenerator (K := K) n hn (.inl i),
      ⁅rootGenerator (K := K) n hn (.inl i), rootGenerator (K := K) n hn (.inl j)⁆⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieSubalgebra.coe_bracket, val_rootGenerator_inl,
    val_rootGenerator_inl]
  -- The two rewritten subtype brackets are definitionally the following nested ambient bracket;
  -- make that bridge explicit so that the private Serre lemma applies.
  change ⁅raisingMatrix n hn i, ⁅raisingMatrix n hn i, raisingMatrix n hn j⁆⁆ = 0
  exact lie_raisingMatrix_lie_raisingMatrix n hn i j

/-- The lowering generators satisfy the simply-laced type-`D` adjacent-node Serre relation.
The formula holds for every pair of nodes, including the nonadjacent and diagonal cases. -/
@[simp]
theorem lie_rootGenerator_inr_lie_rootGenerator_inr {K : Type*} [CommRing K]
    (i j : Fin n) :
    ⁅rootGenerator (K := K) n hn (.inr i),
      ⁅rootGenerator (K := K) n hn (.inr i), rootGenerator (K := K) n hn (.inr j)⁆⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieSubalgebra.coe_bracket, val_rootGenerator_inr,
    val_rootGenerator_inr]
  -- As above, expose the nested ambient matrix bracket hidden by the subtype coercions before
  -- applying the private Serre lemma.
  change ⁅loweringMatrix n hn i, ⁅loweringMatrix n hn i, loweringMatrix n hn j⁆⁆ = 0
  exact lie_loweringMatrix_lie_loweringMatrix n hn i j

/-- A raising generator bracketed with a lowering generator is the corresponding Cartan
generator on the diagonal and zero off the diagonal. -/
@[simp]
theorem lie_rootGenerator_inl_inr {K : Type*} [CommRing K] (i j : Fin n) :
    ⁅rootGenerator (K := K) n hn (.inl i), rootGenerator (K := K) n hn (.inr j)⁆ =
      if i = j then cartanGenerator (K := K) n hn i else 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, val_rootGenerator_inl, val_rootGenerator_inr]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, val_cartanGenerator]
    exact lie_raisingMatrix_loweringMatrix_self n hn i
  · rw [ite_eq_right hij]
    -- Rewriting the conditional and subtype coercions leaves this ambient bracket only
    -- definitionally visible; state it explicitly for the private off-diagonal lemma.
    change ⁅raisingMatrix n hn i, loweringMatrix n hn j⁆ = 0
    exact lie_raisingMatrix_loweringMatrix_of_ne n hn i j hij

/-- A lowering generator bracketed with a raising generator is the negative corresponding Cartan
generator on the diagonal and zero off the diagonal. -/
@[simp]
theorem lie_rootGenerator_inr_inl {K : Type*} [CommRing K] (i j : Fin n) :
    ⁅rootGenerator (K := K) n hn (.inr i), rootGenerator (K := K) n hn (.inl j)⁆ =
      if i = j then -cartanGenerator (K := K) n hn i else 0 := by
  calc
    ⁅rootGenerator n hn (.inr i), rootGenerator n hn (.inl j)⁆ =
        -⁅rootGenerator n hn (.inl j), rootGenerator n hn (.inr i)⁆ := (lie_skew _ _).symm
    _ = -(if j = i then cartanGenerator n hn j else 0) := by
      rw [lie_rootGenerator_inl_inr]
    _ = if i = j then -cartanGenerator n hn i else 0 := by
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij, Ne.symm hij]

/-! ## Nilpotence in the standard representation -/

/-- A lowering generator squares to zero as an endomorphism of the standard split module. -/
@[simp]
theorem loweringMatrix_mul_self {K : Type*} [Ring K] (i : Fin n) :
    loweringMatrix (K := K) n hn i * loweringMatrix n hn i = 0 := by
  by_cases hi : (i : ℕ) + 1 < n
  · rw [loweringMatrix_of_chain n hn hi, Matrix.fromBlocks_multiply]
    have hne := ne_chainNext n i hi
    simp [Matrix.transpose_single, Matrix.single_mul_single_of_ne, hne, hne.symm]
  · rw [loweringMatrix_of_fork n hn hi, Matrix.fromBlocks_multiply]
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
