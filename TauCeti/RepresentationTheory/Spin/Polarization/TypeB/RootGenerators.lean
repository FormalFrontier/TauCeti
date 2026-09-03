/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators
public import TauCeti.RepresentationTheory.Spin.IntegralLattice
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Basic

/-!
# The type-`B` root vectors as quadratic Clifford elements

`TauCeti.SpinPolarizationData.typeBQuadraticEquiv` identifies the split type-`B` matrix algebra
`LieAlgebra.Orthogonal.typeB ι K` with the quadratic elements of the Clifford algebra of an odd
polarization. This file evaluates that identification on the Bourbaki-numbered root and coroot
matrices of `TauCeti/Algebra/Lie/Orthogonal/TypeB/RootGenerators.lean`, and reads off what the
resulting Clifford elements do to the coordinate integral lattice of the spinor module.

Each of the three numbered root vectors is a single Clifford bivector of two vectors of the odd
hyperbolic basis:

```text
e_{εᵢ-εⱼ} ↦ β(wᵢ, w'ⱼ),      e_{εᵢ} ↦ β(wᵢ, z),      f_{εᵢ} ↦ β(z, w'ᵢ),
```

with `wᵢ` the `i`-th basis vector of the first isotropic summand, `w'ᵢ` its polar dual, and `z` the
quadratic-unit remainder vector. The middle assignment is where the normalization of the type-`B`
short root vector is checked: `LieAlgebra.Orthogonal.JB` gives the remainder vector polar
self-pairing `2`, and that `2` is exactly the coefficient carried by the integral short-root matrix
`2 Eᵢ₀ - E₀₋ᵢ`, so the bivector of the *unscaled* pair `(wᵢ, z)` is its image.

The two coroots are not single bivectors but combinations of the diagonal ones
`H i = β(wᵢ, w'ᵢ)`: the short coroot is `2 • H i` and the long one is `H i - H j`.

Two consequences make these elements usable as Chevalley generators on the spinor lattice.

They square to zero in the Clifford algebra. The square of the bivector of two orthogonal vectors
is the scalar `-(Q a * Q b)`, and each of the three pairs above contains an isotropic vector, so
the root vectors act on the spinor module as square-zero operators. Their divided powers therefore
reduce to `1` and to the operator itself, and no denominator ever appears, even though the
type-`B` short root vector is *not* square-zero in the vector representation, where its divided
square `TauCeti.typeBShortRootDividedSquare` is a nonzero matrix.

They preserve the coordinate integral lattice. For a root vector this is immediate from the
product form: each factor is one of the three primitive integral operators — creation,
annihilation, and the parity operator of a remainder vector of unit quadratic norm. A coroot is
not a single such product. The spinor weights are half-integral in the `ε` coordinates, and
correspondingly a single diagonal bivector is a creation-annihilation product less the scalar
`⅟2`, so it is *not* integral. What clears the halves is that the short coroot doubles one
diagonal bivector while the long coroot subtracts two of them; each combination is then again an
integral polynomial in the primitive operators, and acts on the exterior basis by `±1`,
respectively by `0` or `±1`. Half-integral weights that are integral on the coroots are exactly
what makes the spinor lattice available to the simply connected form and not to the adjoint one.

Nothing here constructs a group scheme or asserts reductivity, and no divided-power structure is
introduced: the statements are about the Clifford elements and their action on the lattice.

## Main results

* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBLongRootGenerator`,
  `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBShortRootGenerator` and
  `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBShortNegativeRootGenerator`: the three
  numbered root vectors are the displayed Clifford bivectors.
* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBDiagonalMatrix_single`,
  `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBShortCorootGenerator` and
  `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBLongCorootGenerator`: the diagonal Cartan
  generators are the corresponding combinations of diagonal bivectors.
* The `typeBQuadraticEquiv_typeBSimple...` theorems specialize these formulas to the terminal
  short node and the nonfinal long nodes in Bourbaki order.
* `TauCeti.SpinPolarizationData.spinAction_typeBQuadraticEquiv_typeBShortCorootGenerator_basis`
  and its long counterpart: the coroots act on the exterior basis by integers.
* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBLongRootGenerator_mul_self` and its two
  short counterparts: the root vectors square to zero in the Clifford algebra.
* The five `mem_integralSpinActionSubring` statements, one for each numbered root vector and
  coroot: every generator preserves the coordinate integral lattice.

## Roadmap

This is the evaluation half of the "evaluate the comparison on the numbered root vectors and prove
their divided powers preserve the integral spinor lattice" step of the full-weight type-`B`
Chevalley carrier in Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: the comparison is evaluated on the numbered
generators, and those generators themselves are shown to preserve the lattice. The divided powers
are trivial as a consequence of the square-zero lemmas above, but no divided-power structure is
formalized here; that remains the next step. That carrier is consumed by milestone L0, "pinned
ambient groups", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose `Bₙ(q)` branch needs the simply connected form and
so the spinor lattice rather than the adjoint one.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2, for the integral normalization of the
  short-root operators.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Planche II, for the numbering.
* The basis-extensionality proof architecture is adapted from
  `SpinPolarizationData.typeDQuadraticEquiv_typeDDiagonalMatrix_single` in
  [`TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Basic`](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/RepresentationTheory/Spin/Polarization/TypeD/Basic.lean).
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v w

namespace SpinPolarizationData

attribute [local instance 100] LieRing.ofAssociativeRing

section Quadratic

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- Recognizing a quadratic Clifford element as the bivector of two vectors, from the action of
the corresponding matrix on the odd hyperbolic basis. This is
`CliffordAlgebra.quadraticLieSubalgebra_eq_bivector_of_lie_ι` read through the type-`B`
comparison; only the matrix computation differs between the identifications below. -/
private theorem typeBQuadraticEquiv_eq_bivector (A : LieAlgebra.Orthogonal.typeB ι K) (x y : V)
    (h : ∀ c : Unit ⊕ ι ⊕ ι,
        Matrix.toLinAlgEquiv (P.typeBBasis b z hz)
            (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (P.typeBBasis b z hz c) =
          polar Q y (P.typeBBasis b z hz c) • x - polar Q x (P.typeBBasis b z hz c) • y) :
    P.typeBQuadraticEquiv b z hz A =
      ⟨bivector Q x y, bivector_mem_quadraticLieSubalgebra Q x y⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeBBasis b z hz)
  exact quadraticLieSubalgebra_eq_bivector_of_lie_ι Q
    (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K)) _ _
    (P.typeBQuadraticEquiv_lie_ι b z hz A) (P.typeBBasis b z hz) x y h

/-- The coerced form of `typeBQuadraticEquiv_eq_bivector`, which is how the root-vector
identifications below are stated. -/
private theorem typeBQuadraticEquiv_coe_eq_bivector (A : LieAlgebra.Orthogonal.typeB ι K)
    (x y : V)
    (h : ∀ c : Unit ⊕ ι ⊕ ι,
        Matrix.toLinAlgEquiv (P.typeBBasis b z hz)
            (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (P.typeBBasis b z hz c) =
          polar Q y (P.typeBBasis b z hz c) • x - polar Q x (P.typeBBasis b z hz c) • y) :
    (P.typeBQuadraticEquiv b z hz A : CliffordAlgebra Q) = bivector Q x y :=
  congrArg Subtype.val (P.typeBQuadraticEquiv_eq_bivector b z hz A x y h)

/-! ### The root vectors -/

/-- **The long root vector `e_{εᵢ-εⱼ}` is the Clifford bivector of the `i`-th basis vector and the
polar dual of the `j`-th.** -/
@[simp]
theorem typeBQuadraticEquiv_typeBLongRootGenerator (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) : CliffordAlgebra Q) =
      bivector Q (b i : V) (P.dualVector b j : V) := by
  apply P.typeBQuadraticEquiv_coe_eq_bivector b z hz
  intro c
  -- Each matrix unit picks out one basis index, and so does each polar coordinate.
  rw [coe_typeBLongRootGenerator, toLinAlgEquiv_typeBLongRootMatrix_apply_basis]
  simp [eq_comm]

/-- **The short root vector `e_{εᵢ}` is the Clifford bivector of the `i`-th basis vector and the
remainder vector.** The factor `2` in the integral matrix `2 Eᵢ₀ - E₀₋ᵢ` is the polar self-pairing
of the remainder vector, so no scaling of the bivector is needed. -/
@[simp]
theorem typeBQuadraticEquiv_typeBShortRootGenerator (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) : CliffordAlgebra Q) =
      bivector Q (b i : V) (z : V) := by
  apply P.typeBQuadraticEquiv_coe_eq_bivector b z hz
  intro c
  -- The polar self-pairing `2` of the remainder vector matches the matrix coefficient `2`.
  rw [coe_typeBShortRootGenerator, toLinAlgEquiv_typeBShortRootMatrix_apply_basis]
  simp [eq_comm]

/-- **The negative short root vector `f_{εᵢ}` is the Clifford bivector of the remainder vector and
the polar dual of the `i`-th basis vector.** -/
@[simp]
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) =
      bivector Q (z : V) (P.dualVector b i : V) := by
  apply P.typeBQuadraticEquiv_coe_eq_bivector b z hz
  intro c
  rw [coe_typeBShortNegativeRootGenerator,
    toLinAlgEquiv_typeBShortNegativeRootMatrix_apply_basis]
  simp [eq_comm]

/-! ### The Cartan generators -/

/-- The standard one-coordinate diagonal matrix is the diagonal Clifford bivector of the
corresponding polarization coordinate. -/
@[simp]
theorem typeBQuadraticEquiv_typeBDiagonalMatrix_single (i : ι) :
    P.typeBQuadraticEquiv b z hz
        ⟨typeBDiagonalMatrix (Pi.single i 1), typeBDiagonalMatrix_mem_typeB _⟩ =
      ⟨P.diagonalBivector b i, P.diagonalBivector_mem_quadraticLieSubalgebra b i⟩ := by
  have key : P.typeBQuadraticEquiv b z hz
        ⟨typeBDiagonalMatrix (Pi.single i 1), typeBDiagonalMatrix_mem_typeB _⟩ =
      ⟨bivector Q (b i : V) (P.dualVector b i : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
    apply P.typeBQuadraticEquiv_eq_bivector b z hz
    intro c
    -- Read off the polar coordinates first, then let the diagonal matrix scale the basis vector
    -- `c` by its own diagonal entry.
    simp only [P.polar_basis_typeBBasis, P.polar_dualVector_typeBBasis]
    rw [Matrix.toLinAlgEquiv_self]
    rcases c with ⟨⟩ | (c | c)
    · simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq']
    · by_cases hic : c = i <;>
        simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', hic]
    · by_cases hic : c = i <;>
        simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', hic]
  rw [key]
  exact Subtype.ext (P.diagonalBivector_def b i).symm

/-- **The short coroot `h_{εᵢ}` is twice the `i`-th diagonal bivector.** The doubling is the
reason the coroot takes integer values on the spinor weights, whose own values are
half-integers. -/
@[simp]
theorem typeBQuadraticEquiv_typeBShortCorootGenerator (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortCorootGenerator i) : CliffordAlgebra Q) =
      (2 : K) • P.diagonalBivector b i := by
  have hsmul : (2 • Pi.single i (1 : K)) = (2 : K) • Pi.single i (1 : K) := by
    ext c
    simp [two_smul, two_mul]
  have hmat : (typeBShortCorootGenerator (K := K) (ι := ι) i) =
      (2 : K) • (⟨typeBDiagonalMatrix (Pi.single i 1), typeBDiagonalMatrix_mem_typeB _⟩ :
        LieAlgebra.Orthogonal.typeB ι K) := by
    rw [typeBShortCorootGenerator_eq_diagonal, hsmul, map_smul]
    simp
  rw [hmat, map_smul, P.typeBQuadraticEquiv_typeBDiagonalMatrix_single b z hz]
  -- The quadratic Lie subalgebra carries the ambient scalar action on its elements.
  simp

/-- **The long coroot `h_{εᵢ-εⱼ}` is the difference of two diagonal bivectors.** -/
@[simp]
theorem typeBQuadraticEquiv_typeBLongCorootGenerator (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongCorootGenerator i j hij) : CliffordAlgebra Q) =
      P.diagonalBivector b i - P.diagonalBivector b j := by
  have hmat : (typeBLongCorootGenerator (K := K) (ι := ι) i j hij) =
      (⟨typeBDiagonalMatrix (Pi.single i 1), typeBDiagonalMatrix_mem_typeB _⟩ :
          LieAlgebra.Orthogonal.typeB ι K) -
        ⟨typeBDiagonalMatrix (Pi.single j 1), typeBDiagonalMatrix_mem_typeB _⟩ := by
    rw [typeBLongCorootGenerator_eq_diagonal, map_sub]
    simp
  rw [hmat, map_sub, P.typeBQuadraticEquiv_typeBDiagonalMatrix_single b z hz,
    P.typeBQuadraticEquiv_typeBDiagonalMatrix_single b z hz]
  -- The quadratic Lie subalgebra carries the ambient subtraction on its elements.
  exact AddSubgroupClass.coe_sub _ _

/-! ### The Bourbaki simple roots -/

-- These specializations are intentionally not simp lemmas: the simple-generator simp rules
-- reduce their left-hand sides to the general evaluations above, so `simpNF` rejects them.

/-- The terminal positive simple root is the short Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleRootGenerator_last {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleRootGenerator (K := K) (Fin.last n)) : CliffordAlgebra Q) =
      bivector Q (bFin (Fin.last n) : V) (z : V) := by
  rw [typeBSimpleRootGenerator_last]
  exact P.typeBQuadraticEquiv_typeBShortRootGenerator bFin z hz (Fin.last n)

/-- A nonfinal positive simple root is the adjacent long Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleRootGenerator_castSucc {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) (j : Fin n) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleRootGenerator (K := K) j.castSucc) : CliffordAlgebra Q) =
      bivector Q (bFin j.castSucc : V) (P.dualVector bFin j.succ : V) := by
  rw [typeBSimpleRootGenerator_castSucc]
  exact P.typeBQuadraticEquiv_typeBLongRootGenerator bFin z hz _ _
    (ne_of_lt j.castSucc_lt_succ)

/-- The terminal negative simple root is the opposite short Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_last {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleNegativeRootGenerator (K := K) (Fin.last n)) : CliffordAlgebra Q) =
      bivector Q (z : V) (P.dualVector bFin (Fin.last n) : V) := by
  rw [typeBSimpleNegativeRootGenerator_last]
  exact P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator bFin z hz (Fin.last n)

/-- A nonfinal negative simple root is the opposite adjacent long Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_castSucc {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) (j : Fin n) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleNegativeRootGenerator (K := K) j.castSucc) : CliffordAlgebra Q) =
      bivector Q (bFin j.succ : V) (P.dualVector bFin j.castSucc : V) := by
  rw [typeBSimpleNegativeRootGenerator_castSucc]
  exact P.typeBQuadraticEquiv_typeBLongRootGenerator bFin z hz _ _
    (ne_of_gt j.castSucc_lt_succ)

/-- The terminal simple coroot is twice the final diagonal bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleCorootGenerator_last {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleCorootGenerator (K := K) (Fin.last n)) : CliffordAlgebra Q) =
      (2 : K) • P.diagonalBivector bFin (Fin.last n) := by
  rw [typeBSimpleCorootGenerator_last]
  exact P.typeBQuadraticEquiv_typeBShortCorootGenerator bFin z hz (Fin.last n)

/-- A nonfinal simple coroot is the difference of the two adjacent diagonal bivectors. -/
theorem typeBQuadraticEquiv_typeBSimpleCorootGenerator_castSucc {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) (j : Fin n) :
    (P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleCorootGenerator (K := K) j.castSucc) : CliffordAlgebra Q) =
      P.diagonalBivector bFin j.castSucc - P.diagonalBivector bFin j.succ := by
  rw [typeBSimpleCorootGenerator_castSucc]
  exact P.typeBQuadraticEquiv_typeBLongCorootGenerator bFin z hz _ _
    (ne_of_lt j.castSucc_lt_succ)

/-! ### The root vectors are square-zero -/

/-- **A long root vector squares to zero** in the Clifford algebra: off the diagonal a basis vector
of the first isotropic summand is orthogonal to a polar dual vector, and it is isotropic. -/
theorem typeBQuadraticEquiv_typeBLongRootGenerator_mul_self (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) : CliffordAlgebra Q) *
        (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij)) = 0 := by
  rw [P.typeBQuadraticEquiv_typeBLongRootGenerator b z hz i j hij,
    bivector_mul_self_of_isOrtho Q (P.isOrtho_basis_dualVector b hij), P.isotropic_W (b i),
    zero_mul, map_zero, neg_zero]

/-- **A short root vector squares to zero** in the Clifford algebra, even though the corresponding
matrix does not: the remainder vector is orthogonal to the isotropic summand, and the basis vector
paired with it is isotropic. -/
theorem typeBQuadraticEquiv_typeBShortRootGenerator_mul_self (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) : CliffordAlgebra Q) *
        (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i)) = 0 := by
  rw [P.typeBQuadraticEquiv_typeBShortRootGenerator b z hz i,
    bivector_mul_self_of_isOrtho Q (P.isOrtho_W_line (b i) z), P.isotropic_W (b i), zero_mul,
    map_zero, neg_zero]

/-- **A negative short root vector squares to zero** in the Clifford algebra. -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator_mul_self (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) *
        (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i)) = 0 := by
  rw [P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz i,
    bivector_mul_self_of_isOrtho Q (P.isOrtho_line_W' z (P.dualVector b i)),
    P.isotropic_W' (P.dualVector b i), mul_zero, map_zero, neg_zero]

end Quadratic

/-! ### The action of the Cartan generators on the exterior basis -/

section Weights

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- **The short coroot acts on the exterior basis by `±1`**, according to whether its coordinate
is occupied. -/
theorem spinAction_typeBQuadraticEquiv_typeBShortCorootGenerator_basis (i : ι) (s : Finset ι) :
    spinAction Q P (P.typeBQuadraticEquiv b z hz (typeBShortCorootGenerator i))
        (b.ExteriorAlgebra s) =
      (if i ∈ s then (1 : K) else -1) • b.ExteriorAlgebra s := by
  rw [P.typeBQuadraticEquiv_typeBShortCorootGenerator b z hz i]
  exact P.spinAction_two_smul_diagonalBivector_basis b i s

/-- **The long coroot acts on the exterior basis by the difference of two spin weights**, which is
`0` or `±1`. -/
theorem spinAction_typeBQuadraticEquiv_typeBLongCorootGenerator_basis (i j : ι) (hij : i ≠ j)
    (s : Finset ι) :
    spinAction Q P (P.typeBQuadraticEquiv b z hz (typeBLongCorootGenerator i j hij))
        (b.ExteriorAlgebra s) =
      (spinWeight K s i - spinWeight K s j) • b.ExteriorAlgebra s := by
  rw [P.typeBQuadraticEquiv_typeBLongCorootGenerator b z hz i j hij]
  exact P.spinAction_diagonalBivector_sub_diagonalBivector_basis b i j s

end Weights

section Integral

variable {V : Type v} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {ι : Type w} [Fintype ι] [LinearOrder ι]
  (b : Module.Basis ι ℚ P.W) (z : P.line) (hz : Q (z : V) = 1)

/-- **A long root vector preserves the coordinate integral lattice**: it is a creation operator
followed by an annihilation operator. -/
theorem typeBQuadraticEquiv_typeBLongRootGenerator_mem_integralSpinActionSubring
    (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBLongRootGenerator b z hz i j hij,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_basis_dualVector b hij)]
  exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b i)
    (P.ι_dualVector_mem_integralSpinActionSubring b j)

/-- **A short root vector preserves the coordinate integral lattice**: it is a creation operator
followed by the parity operator of the remainder vector. -/
theorem typeBQuadraticEquiv_typeBShortRootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBShortRootGenerator b z hz i,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_W_line (b i) z)]
  exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b i)
    (P.ι_line_mem_integralSpinActionSubring_of_norm_one b z hz)

/-- **A negative short root vector preserves the coordinate integral lattice.** -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz i,
    bivector_eq_ι_mul_ι_of_isOrtho Q (P.isOrtho_line_W' z (P.dualVector b i))]
  exact mul_mem (P.ι_line_mem_integralSpinActionSubring_of_norm_one b z hz)
    (P.ι_dualVector_mem_integralSpinActionSubring b i)

/-- **The short coroot preserves the coordinate integral lattice**, acting on the exterior basis
by `±1`. -/
theorem typeBQuadraticEquiv_typeBShortCorootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortCorootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBShortCorootGenerator b z hz i]
  exact P.two_smul_diagonalBivector_mem_integralSpinActionSubring b i

/-- **The long coroot preserves the coordinate integral lattice**, acting on the exterior basis by
`0` or `±1`. -/
theorem typeBQuadraticEquiv_typeBLongCorootGenerator_mem_integralSpinActionSubring
    (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongCorootGenerator i j hij) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBLongCorootGenerator b z hz i j hij]
  exact P.diagonalBivector_sub_diagonalBivector_mem_integralSpinActionSubring b i j

end Integral

end SpinPolarizationData

end TauCeti
