/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.Basic

/-!
# Type-B root generators in the quadratic Clifford algebra

An odd polarization identifies the standard split type-`B` matrix Lie algebra with the quadratic
elements of its Clifford algebra. This file evaluates that identification on the root vectors.
For distinct indices `i` and `j`, the long-root matrix of weight `ε_i - ε_j` becomes the Clifford
bivector of the isotropic basis vector `b_i` and the polar-dual vector `b^j`. The short-root
matrices become the bivectors of `b_i` with the quadratic-unit vector `z` in the orthogonal line:

```text
e_(ε_i-ε_j) ↦ bivector(b_i, b^j),
e_(ε_i)     ↦ bivector(b_i, z),
e_(-ε_i)    ↦ bivector(z, b^i).
```

The order of the two vectors fixes the signs. For example, `bivector(b_i, z)` sends `z` to
`2 b_i` and `b^i` to `-z`, exactly matching the integral normalization
`2 E_(i,0) - E_(0,-i)` of the short root. The three comparison theorems below cover the ordered
long-root family and both signs of the short-root family. Reversing the two long-root indices
gives the opposite root. Their Bourbaki-numbered simple-root specializations are then recorded in
the same last-node/nonfinal-node form as the matrix API.

These equations are the bridge needed to prove that the divided powers of the type-`B` Chevalley
generators preserve the integral spinor lattice. They do not yet construct the corresponding
Kostant carrier or claim that any group is finite or simple.

The proofs adapt the basis-extensionality comparison used for diagonal type-`D` elements in
`TauCeti.RepresentationTheory.Spin.Polarization.TypeD`; the root-matrix computations here are
specific to type `B`.

## Main results

* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBLongRootGenerator`: every ordered long
  root becomes the corresponding isotropic--dual Clifford bivector.
* `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBShortRootGenerator` and
  `TauCeti.SpinPolarizationData.typeBQuadraticEquiv_typeBShortNegativeRootGenerator`: the two
  signs of a short root become the bivectors with the quadratic-unit remainder vector.
* The four `typeBQuadraticEquiv_typeBSimple...` theorems specialize these formulas to the terminal
  short node and the nonfinal long nodes in Bourbaki order.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. W. Carter, *Simple Groups of Lie Type*, Section 4.2.

This advances the explicit full-weight type-`B` Chevalley--Demazure carrier in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. The carrier is consumed by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` as the pinned ambient group for the `B_n(q)` family.
-/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v w

namespace SpinPolarizationData

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

omit [Fintype ι] [Invertible (2 : K)] in
@[simp] private theorem polar_dualVector_comm (i j : ι) :
    polar Q (P.dualVector b i : V) (b j : V) = if j = i then 1 else 0 := by
  rw [polar_comm, P.polar_dualVector]

private theorem typeBQuadraticEquiv_eq_bivector
    (A : LieAlgebra.Orthogonal.typeB ι K) (a c : V)
    (hact : Matrix.toLinAlgEquiv (P.typeBBasis b z hz) A =
      (Q.polarBilin c).smulRight a - (Q.polarBilin a).smulRight c) :
    P.typeBQuadraticEquiv b z hz A =
      ⟨bivector Q a c, bivector_mem_quadraticLieSubalgebra Q a c⟩ := by
  let _ : Module.Finite K V := Module.Finite.of_basis (P.typeBBasis b z hz)
  apply quadraticLieSubalgebra_ext Q
    (P.nondegenerate ((isUnit_of_invertible (2 : K)).isSMulRegular K))
  intro x
  rw [P.typeBQuadraticEquiv_lie_ι b z hz, bivector_lie_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  exact LinearMap.congr_fun hact x

/-! ## Long roots -/

/-- **A positive long-root matrix becomes its isotropic--dual Clifford bivector.** -/
theorem typeBQuadraticEquiv_typeBLongRootGenerator (i j : ι) (hij : i ≠ j) :
    P.typeBQuadraticEquiv b z hz (typeBLongRootGenerator i j hij) =
      ⟨bivector Q (b i : V) (P.dualVector b j : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  rw [coe_typeBLongRootGenerator]
  apply (P.typeBBasis b z hz).ext
  rintro (k | (k | k))
  all_goals
    rw [Matrix.toLinAlgEquiv_self]
    simp [typeBLongRootMatrix, Matrix.single_apply, ite_and,
      P.line_orthogonal_W, P.line_orthogonal_W', P.polar_W_eq_zero,
      P.polar_W'_eq_zero, polar_comm,
      P.polar_dualVector_comm b, eq_comm]

/-! ## Short roots -/

/-- **A positive short-root matrix becomes the bivector of its isotropic vector and the
quadratic-unit remainder vector.** The order realizes the integral normalization
`z ↦ 2 b_i`, `b^i ↦ -z`. -/
theorem typeBQuadraticEquiv_typeBShortRootGenerator (i : ι) :
    P.typeBQuadraticEquiv b z hz (typeBShortRootGenerator i) =
      ⟨bivector Q (b i : V) (z : V), bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  rw [coe_typeBShortRootGenerator]
  apply (P.typeBBasis b z hz).ext
  rintro (k | (k | k))
  all_goals
    rw [Matrix.toLinAlgEquiv_self]
    simp [Fintype.sum_sum_type, typeBShortRootMatrix, Matrix.single_apply,
      Finset.sum_ite_eq', QuadraticMap.polar_self, hz,
      P.line_orthogonal_W, P.line_orthogonal_W', P.polar_W_eq_zero, polar_comm,
      P.polar_dualVector_comm b, eq_comm]

/-- **A negative short-root matrix becomes the bivector with the remainder vector first.** This
order realizes `b_i ↦ z`, `z ↦ -2 b^i`. -/
theorem typeBQuadraticEquiv_typeBShortNegativeRootGenerator (i : ι) :
    P.typeBQuadraticEquiv b z hz (typeBShortNegativeRootGenerator i) =
      ⟨bivector Q (z : V) (P.dualVector b i : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  apply P.typeBQuadraticEquiv_eq_bivector b z hz
  rw [coe_typeBShortNegativeRootGenerator]
  apply (P.typeBBasis b z hz).ext
  rintro (k | (k | k))
  all_goals
    rw [Matrix.toLinAlgEquiv_self]
    simp [Fintype.sum_sum_type, typeBShortNegativeRootMatrix, Matrix.single_apply,
      Finset.sum_ite_eq', QuadraticMap.polar_self, hz,
      P.line_orthogonal_W, P.line_orthogonal_W', P.polar_W'_eq_zero, polar_comm,
      P.polar_dualVector_comm b, eq_comm]

/-! ## Bourbaki-numbered simple roots -/

/-- The terminal positive simple root is the short Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleRootGenerator_last {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) :
    P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleRootGenerator (K := K) (Fin.last n)) =
      ⟨bivector Q (bFin (Fin.last n) : V) (z : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  rw [typeBSimpleRootGenerator_last]
  exact P.typeBQuadraticEquiv_typeBShortRootGenerator bFin z hz (Fin.last n)

/-- A nonfinal positive simple root is the adjacent long Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleRootGenerator_castSucc {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) (j : Fin n) :
    P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleRootGenerator (K := K) j.castSucc) =
      ⟨bivector Q (bFin j.castSucc : V) (P.dualVector bFin j.succ : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  rw [typeBSimpleRootGenerator_castSucc]
  exact P.typeBQuadraticEquiv_typeBLongRootGenerator bFin z hz _ _
    (ne_of_lt j.castSucc_lt_succ)

/-- The terminal negative simple root is the opposite short Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_last {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) :
    P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleNegativeRootGenerator (K := K) (Fin.last n)) =
      ⟨bivector Q (z : V) (P.dualVector bFin (Fin.last n) : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  rw [typeBSimpleNegativeRootGenerator_last]
  exact P.typeBQuadraticEquiv_typeBShortNegativeRootGenerator bFin z hz (Fin.last n)

/-- A nonfinal negative simple root is the opposite adjacent long Clifford bivector. -/
theorem typeBQuadraticEquiv_typeBSimpleNegativeRootGenerator_castSucc {n : ℕ}
    (bFin : Module.Basis (Fin (n + 1)) K P.W) (j : Fin n) :
    P.typeBQuadraticEquiv bFin z hz
        (typeBSimpleNegativeRootGenerator (K := K) j.castSucc) =
      ⟨bivector Q (bFin j.succ : V) (P.dualVector bFin j.castSucc : V),
        bivector_mem_quadraticLieSubalgebra Q _ _⟩ := by
  rw [typeBSimpleNegativeRootGenerator_castSucc]
  exact P.typeBQuadraticEquiv_typeBLongRootGenerator bFin z hz _ _
    (ne_of_gt j.castSucc_lt_succ)

end SpinPolarizationData

end TauCeti
