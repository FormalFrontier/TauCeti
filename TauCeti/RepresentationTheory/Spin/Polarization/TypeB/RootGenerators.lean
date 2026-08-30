/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators
public import TauCeti.RepresentationTheory.Spin.IntegralLattice
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Basic
public import TauCeti.RepresentationTheory.Spin.Weight

/-!
# The type-`B` root vectors as quadratic Clifford elements

`TauCeti.SpinPolarizationData.typeBQuadraticEquiv` identifies the split type-`B` matrix algebra
`LieAlgebra.Orthogonal.typeB ι K` with the quadratic elements of the Clifford algebra of an odd
polarization. This file evaluates that identification on the Bourbaki-numbered root and coroot
matrices of `TauCeti/Algebra/Lie/Orthogonal/TypeB/RootGenerators.lean`, and reads off what the
resulting Clifford elements do to the coordinate integral lattice of the spinor module.

Every one of them is a single Clifford bivector of two vectors of the odd hyperbolic basis:

```text
e_{εᵢ-εⱼ} ↦ β(wᵢ, w'ⱼ),      e_{εᵢ} ↦ β(wᵢ, z),      f_{εᵢ} ↦ β(z, w'ᵢ),
```

with `wᵢ` the `i`-th basis vector of the first isotropic summand, `w'ᵢ` its polar dual, and `z` the
quadratic-unit remainder vector. The middle assignment is where the normalization of the type-`B`
short root vector is checked: `LieAlgebra.Orthogonal.JB` gives the remainder vector polar
self-pairing `2`, and that `2` is exactly the coefficient carried by the integral short-root matrix
`2 Eᵢ₀ - E₀₋ᵢ`, so the bivector of the *unscaled* pair `(wᵢ, z)` is its image.

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
not such a product, and its integrality is instead read off its action on the exterior basis,
which is by `±1` for a short coroot and by `0` or `±1` for a long one. The reason is that a coroot
is *twice* a diagonal bivector: the spinor weights are half-integral in the `ε` coordinates and
integral on the coroots, which is what makes the spinor lattice available to the simply connected
form and not to the adjoint one.

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
* `TauCeti.SpinPolarizationData.spinAction_typeBQuadraticEquiv_typeBShortCorootGenerator_basis`
  and its long counterpart: the coroots act on the exterior basis by integers.
* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBLongRootGenerator_mul_self` and its two
  short counterparts: the root vectors square to zero in the Clifford algebra.
* The five `mem_integralSpinActionSubring` statements, one for each numbered root vector and
  coroot: every generator preserves the coordinate integral lattice.

## Roadmap

This is the "evaluate the comparison on the numbered root vectors and prove their divided powers
preserve the integral spinor lattice" step of the full-weight type-`B` Chevalley carrier in Layer
9, "The Chevalley--Demazure construction", of `TauCetiRoadmap/ReductiveGroups/README.md`. That
carrier is consumed by milestone L0, "pinned ambient groups", of
`TauCetiRoadmap/CFSGStatement/README.md`, whose `Bₙ(q)` branch needs the simply connected form and
so the spinor lattice rather than the adjoint one.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2, for the integral normalization of the
  short-root operators.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Planche II, for the numbering.
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

omit [Invertible (2 : K)] in
/-- A vector of the first isotropic summand is orthogonal to the remainder. This is
`SpinPolarizationData.line_orthogonal_W` with its two arguments in the order the computations
below produce them. -/
private theorem polar_W_line (x : P.W) : polar Q (x : V) (z : V) = 0 := by
  rw [polar_comm]
  exact P.line_orthogonal_W z x

omit [Invertible (2 : K)] in
/-- A vector of the second isotropic summand is orthogonal to the remainder. -/
private theorem polar_W'_line (y : P.W') : polar Q (y : V) (z : V) = 0 := by
  rw [polar_comm]
  exact P.line_orthogonal_W' z y

/-- Recognizing a quadratic Clifford element as the bivector of two vectors, from the action of
the corresponding matrix on the odd hyperbolic basis. This is the shared shell of every
identification below; only the matrix computation differs between them. -/
private theorem typeBQuadraticEquiv_eq_bivector (A : LieAlgebra.Orthogonal.typeB ι K) (x y : V)
    (h : ∀ c : Unit ⊕ ι ⊕ ι,
        Matrix.toLin (P.typeBBasis b z hz) (P.typeBBasis b z hz)
            (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (P.typeBBasis b z hz c) =
          polar Q y (P.typeBBasis b z hz c) • x - polar Q x (P.typeBBasis b z hz c) • y) :
    P.typeBQuadraticEquiv b z hz A =
      ⟨bivector Q x y, bivector_mem_quadraticLieSubalgebra Q x y⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeBBasis b z hz)
  apply quadraticLieSubalgebra_ext Q
    (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
  intro v
  rw [P.typeBQuadraticEquiv_lie_ι b z hz]
  -- The extensionality lemma compares the underlying Clifford elements, so the bracket on the
  -- right is still stated on the subtype and has to be exposed before its action formula applies.
  change _ = ⁅bivector Q x y, CliffordAlgebra.ι Q v⁆
  rw [bivector_lie_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  -- Both sides are values of a linear map at `v`, so compare those maps on the basis.
  have hlin : Matrix.toLin (P.typeBBasis b z hz) (P.typeBBasis b z hz)
        (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) =
      (Q.polarBilin y).smulRight x - (Q.polarBilin x).smulRight y := by
    apply (P.typeBBasis b z hz).ext
    intro c
    rw [h c]
    simp
  -- `Matrix.toLinAlgEquiv` on a square matrix is `Matrix.toLin` for the same basis on both sides.
  change Matrix.toLin (P.typeBBasis b z hz) (P.typeBBasis b z hz)
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) v = _
  rw [hlin]
  simp

omit [Invertible (2 : K)] in
/-- The value of a matrix unit's endomorphism on a vector of the odd hyperbolic basis. -/
private theorem toLin_typeBBasis_single (p q : Unit ⊕ ι ⊕ ι) (v : K) (c : Unit ⊕ ι ⊕ ι) :
    Matrix.toLin (P.typeBBasis b z hz) (P.typeBBasis b z hz) (Matrix.single p q v)
        (P.typeBBasis b z hz c) =
      (if q = c then v else 0) • P.typeBBasis b z hz p := by
  rw [Matrix.toLin_self]
  simp [Matrix.single_apply, ite_and, ite_smul]

omit [Invertible (2 : K)] in
/-- The value on the odd hyperbolic basis of the endomorphism of a difference of two matrix
units, which is the shape of every type-`B` root matrix. -/
private theorem toLin_typeBBasis_single_sub_single (p q p' q' : Unit ⊕ ι ⊕ ι) (v v' : K)
    (c : Unit ⊕ ι ⊕ ι) :
    Matrix.toLin (P.typeBBasis b z hz) (P.typeBBasis b z hz)
        (Matrix.single p q v - Matrix.single p' q' v') (P.typeBBasis b z hz c) =
      (if q = c then v else 0) • P.typeBBasis b z hz p -
        (if q' = c then v' else 0) • P.typeBBasis b z hz p' := by
  rw [map_sub, LinearMap.sub_apply, P.toLin_typeBBasis_single b z hz,
    P.toLin_typeBBasis_single b z hz]

/-! ### The root vectors -/

/-- **The long root vector `e_{εᵢ-εⱼ}` is the Clifford bivector of the `i`-th basis vector and the
polar dual of the `j`-th.** -/
theorem typeBQuadraticEquiv_typeBLongRootGenerator (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) : CliffordAlgebra Q) =
      bivector Q (b i : V) (P.dualVector b j : V) := by
  refine Subtype.ext_iff.mp (?_ :
    P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) =
      ⟨bivector Q (b i : V) (P.dualVector b j : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩)
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  intro c
  rw [coe_typeBLongRootGenerator, typeBLongRootMatrix_def,
    P.toLin_typeBBasis_single_sub_single b z hz]
  rcases c with c | (c | c) <;>
    simp only [typeBBasis_inl, typeBBasis_inr_inl, typeBBasis_inr_inr]
  · -- The remainder vector is orthogonal to both isotropic summands.
    simp [P.polar_W_line z (b i), P.polar_W'_line z (P.dualVector b j)]
  · -- Only the first matrix unit sees a vector of the first isotropic summand.
    by_cases hjc : j = c
    · subst hjc
      simp [P.polar_W_eq_zero, polar_comm (⇑Q) (P.dualVector b j : V), P.polar_dualVector]
    · simp [hjc, Ne.symm hjc, P.polar_W_eq_zero, polar_comm (⇑Q) (P.dualVector b j : V),
        P.polar_dualVector]
  · -- Only the second matrix unit sees a polar dual vector.
    by_cases hic : i = c
    · subst hic
      simp [P.polar_W'_eq_zero, P.polar_dualVector]
    · simp [hic, P.polar_W'_eq_zero, P.polar_dualVector]

/-- **The short root vector `e_{εᵢ}` is the Clifford bivector of the `i`-th basis vector and the
remainder vector.** The factor `2` in the integral matrix `2 Eᵢ₀ - E₀₋ᵢ` is the polar self-pairing
of the remainder vector, so no scaling of the bivector is needed. -/
theorem typeBQuadraticEquiv_typeBShortRootGenerator (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) : CliffordAlgebra Q) =
      bivector Q (b i : V) (z : V) := by
  refine Subtype.ext_iff.mp (?_ :
    P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) =
      ⟨bivector Q (b i : V) (z : V), bivector_mem_quadraticLieSubalgebra Q _ _⟩)
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  intro c
  rw [coe_typeBShortRootGenerator, typeBShortRootMatrix_def,
    P.toLin_typeBBasis_single_sub_single b z hz]
  rcases c with c | (c | c) <;>
    simp only [typeBBasis_inl, typeBBasis_inr_inl, typeBBasis_inr_inr]
  · -- The remainder vector has polar self-pairing `2`, which is the matrix coefficient.
    rw [polar_self, hz, P.polar_W_line z (b i)]
    simp [two_smul, add_smul]
  · -- A vector of the first isotropic summand is killed by both terms.
    simp [P.polar_W_eq_zero, P.line_orthogonal_W]
  · -- A polar dual vector is seen only by the second matrix unit.
    by_cases hic : i = c
    · subst hic
      simp [P.line_orthogonal_W', P.polar_dualVector]
    · simp [hic, P.line_orthogonal_W', P.polar_dualVector]

/-- **The negative short root vector `f_{εᵢ}` is the Clifford bivector of the remainder vector and
the polar dual of the `i`-th basis vector.** -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) =
      bivector Q (z : V) (P.dualVector b i : V) := by
  refine Subtype.ext_iff.mp (?_ :
    P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) =
      ⟨bivector Q (z : V) (P.dualVector b i : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩)
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  intro c
  rw [coe_typeBShortNegativeRootGenerator, typeBShortNegativeRootMatrix_def,
    P.toLin_typeBBasis_single_sub_single b z hz]
  rcases c with c | (c | c) <;>
    simp only [typeBBasis_inl, typeBBasis_inr_inl, typeBBasis_inr_inr]
  · -- The remainder vector is orthogonal to the second isotropic summand and self-pairs to `2`.
    rw [polar_self, hz, P.polar_W'_line z (P.dualVector b i)]
    simp [two_smul, add_smul]
  · -- A vector of the first isotropic summand is seen only by the first matrix unit.
    by_cases hic : i = c
    · subst hic
      simp [P.line_orthogonal_W, polar_comm (⇑Q) (P.dualVector b i : V), P.polar_dualVector]
    · simp [hic, Ne.symm hic, P.line_orthogonal_W, polar_comm (⇑Q) (P.dualVector b i : V),
        P.polar_dualVector]
  · -- A polar dual vector is killed by both terms.
    simp [P.polar_W'_eq_zero, P.line_orthogonal_W']

/-! ### The Cartan generators -/

/-- The standard one-coordinate diagonal matrix is the diagonal Clifford bivector of the
corresponding polarization coordinate. -/
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
    rw [Matrix.toLin_self]
    rcases c with c | (c | c) <;>
      simp only [typeBBasis_inl, typeBBasis_inr_inl, typeBBasis_inr_inr]
    · simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', P.polar_W_line z (b i),
        P.polar_W'_line z (P.dualVector b i)]
    · by_cases hic : i = c
      · subst hic
        simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', P.polar_W_eq_zero,
          polar_comm (⇑Q) (P.dualVector b i : V) (b i : V), P.polar_dualVector_self]
      · simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', Ne.symm hic, P.polar_W_eq_zero,
          polar_comm (⇑Q) (P.dualVector b i : V), P.polar_dualVector]
    · by_cases hic : i = c
      · subst hic
        simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', P.polar_W'_eq_zero,
          P.polar_dualVector]
      · simp [typeBDiagonalMatrix_apply, Finset.sum_ite_eq', hic, P.polar_W'_eq_zero,
          P.polar_dualVector]
  rw [key]
  exact Subtype.ext (P.diagonalBivector_def b i).symm

/-- **The short coroot `h_{εᵢ}` is twice the `i`-th diagonal bivector.** The doubling is the
reason the coroot takes integer values on the spinor weights, whose own values are
half-integers. -/
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
  rfl

/-- **The long coroot `h_{εᵢ-εⱼ}` is the difference of two diagonal bivectors.** -/
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
  rfl

/-! ### The root vectors are square-zero -/

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : K)] in
/-- Off the diagonal a basis vector of the first isotropic summand is orthogonal to a polar dual
vector. -/
private theorem isOrtho_basis_dualVector {i j : ι} (hij : i ≠ j) :
    Q.IsOrtho (b i : V) (P.dualVector b j : V) := by
  classical
  rw [← isOrtho_polarBilin, polarBilin_apply_apply, P.polar_dualVector b j i]
  simp [hij]

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : K)] in
/-- The remainder is orthogonal to the first isotropic summand. -/
private theorem isOrtho_basis_line (i : ι) : Q.IsOrtho (b i : V) (z : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply]
  exact P.polar_W_line z (b i)

omit [Fintype ι] [DecidableEq ι] [Invertible (2 : K)] in
/-- The remainder is orthogonal to the second isotropic summand. -/
private theorem isOrtho_line_dualVector (i : ι) : Q.IsOrtho (z : V) (P.dualVector b i : V) := by
  rw [← isOrtho_polarBilin, polarBilin_apply_apply]
  exact P.line_orthogonal_W' z (P.dualVector b i)

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
    bivector_mul_self_of_isOrtho Q (P.isOrtho_basis_line b z i), P.isotropic_W (b i), zero_mul,
    map_zero, neg_zero]

/-- **A negative short root vector squares to zero** in the Clifford algebra. -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator_mul_self (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) *
        (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i)) = 0 := by
  rw [P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz i,
    bivector_mul_self_of_isOrtho Q (P.isOrtho_line_dualVector b z i),
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
  rw [P.typeBQuadraticEquiv_typeBShortCorootGenerator b z hz i, map_smul, LinearMap.smul_apply,
    P.spinAction_diagonalBivector_basis b i s, smul_smul]
  by_cases hi : i ∈ s <;> simp [hi, spinWeight_of_mem, spinWeight_of_notMem]

/-- **The long coroot acts on the exterior basis by the difference of two spin weights**, which is
`0` or `±1`. -/
theorem spinAction_typeBQuadraticEquiv_typeBLongCorootGenerator_basis (i j : ι) (hij : i ≠ j)
    (s : Finset ι) :
    spinAction Q P (P.typeBQuadraticEquiv b z hz (typeBLongCorootGenerator i j hij))
        (b.ExteriorAlgebra s) =
      (spinWeight K s i - spinWeight K s j) • b.ExteriorAlgebra s := by
  rw [P.typeBQuadraticEquiv_typeBLongCorootGenerator b z hz i j hij, map_sub,
    LinearMap.sub_apply, P.spinAction_diagonalBivector_basis b i s,
    P.spinAction_diagonalBivector_basis b j s]
  simp [sub_smul]

end Weights

section Integral

variable {V : Type v} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {ι : Type w} [Fintype ι] [LinearOrder ι]
  (b : Module.Basis ι ℚ P.W) (z : P.line) (hz : Q (z : V) = 1)

include hz in
omit [Fintype ι] in
/-- A remainder vector of unit quadratic norm has coordinate `±1`, so it acts integrally. -/
private theorem ι_line_mem_integralSpinActionSubring_of_norm_one :
    CliffordAlgebra.ι Q (z : V) ∈ P.integralSpinActionSubring b := by
  have hsq : P.lineCoordinate z * P.lineCoordinate z = 1 := by rw [P.lineCoordinate_sq, hz]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact P.ι_line_mem_integralSpinActionSubring b z 1 (by simpa using h)
  · exact P.ι_line_mem_integralSpinActionSubring b z (-1) (by simpa using h)

/-- **A long root vector preserves the coordinate integral lattice**: it is a creation operator
followed by an annihilation operator. -/
theorem typeBQuadraticEquiv_typeBLongRootGenerator_mem_integralSpinActionSubring
    (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBLongRootGenerator b z hz i j hij,
    bivector_of_isOrtho Q (P.isOrtho_basis_dualVector b hij)]
  exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b i)
    (P.ι_dualVector_mem_integralSpinActionSubring b j)

/-- **A short root vector preserves the coordinate integral lattice**: it is a creation operator
followed by the parity operator of the remainder vector. -/
theorem typeBQuadraticEquiv_typeBShortRootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBShortRootGenerator b z hz i,
    bivector_of_isOrtho Q (P.isOrtho_basis_line b z i)]
  exact mul_mem (P.ι_basis_mem_integralSpinActionSubring b i)
    (P.ι_line_mem_integralSpinActionSubring_of_norm_one b z hz)

/-- **A negative short root vector preserves the coordinate integral lattice.** -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  rw [P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator b z hz i,
    bivector_of_isOrtho Q (P.isOrtho_line_dualVector b z i)]
  exact mul_mem (P.ι_line_mem_integralSpinActionSubring_of_norm_one b z hz)
    (P.ι_dualVector_mem_integralSpinActionSubring b i)

/-- **The short coroot preserves the coordinate integral lattice**, acting on the exterior basis
by `±1`. -/
theorem typeBQuadraticEquiv_typeBShortCorootGenerator_mem_integralSpinActionSubring (i : ι) :
    (P.typeBQuadraticEquiv b z hz (typeBShortCorootGenerator i) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  apply P.mem_integralSpinActionSubring_of_basis b
  intro s
  rw [P.spinAction_typeBQuadraticEquiv_typeBShortCorootGenerator_basis b z hz i s]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (if i ∈ s then (1 : ℚ) else -1) = (m : ℚ) := by
    by_cases hi : i ∈ s
    · exact ⟨1, by simp [hi]⟩
    · exact ⟨-1, by simp [hi]⟩
  rw [hm, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ m (TauCeti.ExteriorAlgebra.basis_mem_integralLattice b s)

/-- **The long coroot preserves the coordinate integral lattice**, acting on the exterior basis by
`0` or `±1`. -/
theorem typeBQuadraticEquiv_typeBLongCorootGenerator_mem_integralSpinActionSubring
    (i j : ι) (hij : i ≠ j) :
    (P.typeBQuadraticEquiv b z hz (typeBLongCorootGenerator i j hij) : CliffordAlgebra Q) ∈
      P.integralSpinActionSubring b := by
  apply P.mem_integralSpinActionSubring_of_basis b
  intro s
  rw [P.spinAction_typeBQuadraticEquiv_typeBLongCorootGenerator_basis b z hz i j hij s]
  have hhalf : (⅟(2 : ℚ)) = 2⁻¹ := invOf_eq_inv 2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, spinWeight ℚ s i - spinWeight ℚ s j = (m : ℚ) := by
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · exact ⟨0, by simp [spinWeight_of_mem hi, spinWeight_of_mem hj]⟩
    · exact ⟨1, by rw [spinWeight_of_mem hi, spinWeight_of_notMem hj, hhalf]; norm_num⟩
    · exact ⟨-1, by rw [spinWeight_of_notMem hi, spinWeight_of_mem hj, hhalf]; norm_num⟩
    · exact ⟨0, by simp [spinWeight_of_notMem hi, spinWeight_of_notMem hj]⟩
  rw [hm, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ m (TauCeti.ExteriorAlgebra.basis_mem_integralLattice b s)

end Integral



end SpinPolarizationData

end TauCeti
