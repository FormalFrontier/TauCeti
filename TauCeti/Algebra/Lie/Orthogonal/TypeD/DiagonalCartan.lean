/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import Mathlib.Algebra.Lie.Classical

/-!
# The diagonal Cartan subalgebra of the split orthogonal Lie algebra of type D

Mathlib's `LieAlgebra.Orthogonal.typeD ι K` is the Lie algebra of matrices skew-adjoint for the
split symmetric form with matrix

```
[ 0  1 ]
[ 1  0 ].
```

Its standard Cartan subalgebra consists of the diagonal matrices `diag(d, -d)`. This file bundles
that subalgebra, proves that it is abelian and self-normalizing when `2` is regular, and gives its
coordinate basis and dual coordinates. Over an algebraically closed field of characteristic not
two, the existing finite-dimensional triangularizability instance therefore makes it a splitting
Cartan subalgebra.

The self-normalizing argument is entrywise. If `X` normalizes every `diag(d, -d)`, then the
off-diagonal `(a, b)` entry of their bracket is
`(weight d b - weight d a) * X a b`. Distinct indices in `ι ⊕ ι` have distinct weights when
multiplication by `2` is injective, so every off-diagonal entry of `X` vanishes. Skew-adjointness
then forces the two diagonal blocks to be negatives of one another.

## Main definitions

* `TauCeti.typeDDiagonalCartan`: the diagonal Cartan subalgebra of
  `LieAlgebra.Orthogonal.typeD ι K`.
* `TauCeti.typeDDiagonalEquiv`: the coordinate equivalence
  `(ι → K) ≃ₗ[K] typeDDiagonalCartan K ι`.
* `TauCeti.typeDDiagonalCartanBasis`: its basis by the matrices with diagonal entries `1` and `-1`
  in the paired positions.
* `TauCeti.typeDWeightEquiv`: the corresponding coordinate equivalence with the dual Cartan.
* `TauCeti.typeDEpsilon`: the coordinate functional `εᵢ`.

## Main results

* `TauCeti.typeDDiagonalCartan_normalizer_eq_self`: the diagonal Cartan is self-normalizing.
* `TauCeti.instIsCartanSubalgebraTypeDDiagonalCartan`: it is a Cartan subalgebra.
* `TauCeti.finrank_typeDDiagonalCartan`: its dimension is `Fintype.card ι`.

## References

The declaration order and coordinate API adapt the existing formal template in
`TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan` to the split orthogonal subalgebra.
This is the split type-`D` Cartan prerequisite for Layer 5 of the
[Spin-representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md).
See Fulton--Harris, *Representation Theory*, Lecture 20, for the coordinate model.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u}
variable {ι : Type*}

/-! ### The diagonal matrices of type D -/

section Neg

variable [Neg K]

/-- The weight of a coordinate in the standard type-`D` module: `d i` on the first copy of `ι`
and `-d i` on the second. -/
def typeDDiagonalValue (d : ι → K) : ι ⊕ ι → K :=
  Sum.elim d (-d)

@[simp]
theorem typeDDiagonalValue_inl (d : ι → K) (i : ι) :
    typeDDiagonalValue d (.inl i) = d i :=
  (rfl)

@[simp]
theorem typeDDiagonalValue_inr (d : ι → K) (i : ι) :
    typeDDiagonalValue d (.inr i) = -d i :=
  (rfl)

end Neg

section NegZero

variable [Neg K] [Zero K] [DecidableEq ι]

/-- The ambient matrix `diag(d, -d)` in the split type-`D` model. -/
def typeDDiagonalMatrix (d : ι → K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K :=
  diagonal (typeDDiagonalValue d)

@[simp]
theorem typeDDiagonalMatrix_apply (d : ι → K) (i j : ι ⊕ ι) :
    typeDDiagonalMatrix d i j = if i = j then typeDDiagonalValue d i else 0 :=
  (rfl)

end NegZero

variable [CommRing K] [DecidableEq ι] [Fintype ι]

/-- Every `diag(d, -d)` is skew-adjoint for the split type-`D` form. -/
theorem typeDDiagonalMatrix_mem_typeD (d : ι → K) :
    typeDDiagonalMatrix d ∈ LieAlgebra.Orthogonal.typeD ι K := by
  rw [LieAlgebra.Orthogonal.typeD, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Membership in `typeD` unfolds to the ambient skew-adjoint matrix equation.
  change (typeDDiagonalMatrix d)ᵀ * LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K * (-typeDDiagonalMatrix d)
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [typeDDiagonalMatrix, typeDDiagonalValue, LieAlgebra.Orthogonal.JD,
      Matrix.diagonal_mul, Matrix.mul_diagonal, h]

/-- In a type-`D` matrix, the lower-right block is the negative transpose of the upper-left
block. -/
@[simp]
theorem typeD_apply_inr_inr (A : LieAlgebra.Orthogonal.typeD ι K) (i j : ι) :
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inr i) (.inr j) =
      -(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl j) (.inl i) := by
  have hA := A.2
  -- The subtype witness is membership in the skew-adjoint matrix submodule.
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JD ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  -- Unfold the submodule predicate once to read the two corresponding block entries.
  change (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JD ι K =
    LieAlgebra.Orthogonal.JD ι K * (-(A : Matrix (ι ⊕ ι) (ι ⊕ ι) K)) at hA
  have h := congr_fun (congr_fun hA (.inl i)) (.inr j)
  exact neg_eq_iff_eq_neg.mp (by
    simpa [LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply] using h.symm)

/-! ### The Cartan subalgebra and its coordinates -/

variable (K ι)

/-- The diagonal matrices inside the split orthogonal Lie algebra of type `D`. -/
def typeDDiagonalCartan : LieSubalgebra K (LieAlgebra.Orthogonal.typeD ι K) :=
  (diagonalCartan K (ι ⊕ ι)).comap (LieAlgebra.Orthogonal.typeD ι K).incl

variable {K ι}

/-- Membership in the type-`D` diagonal Cartan means that the ambient matrix is diagonal. -/
@[simp]
theorem mem_typeDDiagonalCartan_iff_isDiag {A : LieAlgebra.Orthogonal.typeD ι K} :
    A ∈ typeDDiagonalCartan K ι ↔
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K).IsDiag :=
  by simp [typeDDiagonalCartan]

/-- The coordinate equivalence from `ι`-tuples to the type-`D` diagonal Cartan. -/
def typeDDiagonalEquiv : (ι → K) ≃ₗ[K] typeDDiagonalCartan K ι where
  toFun d := ⟨⟨typeDDiagonalMatrix d, typeDDiagonalMatrix_mem_typeD d⟩,
    by simp [typeDDiagonalMatrix]⟩
  map_add' d e := by
    apply Subtype.ext
    apply Subtype.ext
    ext (i | i) (j | j) <;> by_cases hij : i = j <;>
      simp [typeDDiagonalMatrix, typeDDiagonalValue, hij, eq_comm, add_comm]
  map_smul' c d := by
    apply Subtype.ext
    apply Subtype.ext
    ext (i | i) (j | j) <;> by_cases hij : i = j <;>
      simp [typeDDiagonalMatrix, typeDDiagonalValue, hij, eq_comm]
  invFun A i := (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i)
  left_inv d := by
    ext i
    simp [typeDDiagonalMatrix]
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    -- After the subtype extensionality steps, the goal is the ambient matrix equation.
    change typeDDiagonalMatrix (fun i =>
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i)) a b =
        (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b
    by_cases hab : a = b
    · subst b
      rcases a with i | i
      · simp [typeDDiagonalMatrix]
      · simp only [typeDDiagonalMatrix_apply, ↓reduceIte, typeDDiagonalValue_inr]
        exact (typeD_apply_inr_inr
          (A : LieAlgebra.Orthogonal.typeD ι K) i i).symm
    · rw [typeDDiagonalMatrix_apply, ite_eq_right hab]
      exact (mem_typeDDiagonalCartan_iff_isDiag.mp A.2 hab).symm

@[simp]
theorem coe_typeDDiagonalEquiv_apply (d : ι → K) :
    ((typeDDiagonalEquiv (K := K) (ι := ι) d : typeDDiagonalCartan K ι) :
      LieAlgebra.Orthogonal.typeD ι K) =
      ⟨typeDDiagonalMatrix d, typeDDiagonalMatrix_mem_typeD d⟩ :=
  (rfl)

@[simp]
theorem typeDDiagonalEquiv_symm_apply (A : typeDDiagonalCartan K ι) (i : ι) :
    (typeDDiagonalEquiv (K := K) (ι := ι)).symm A i =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) :=
  (rfl)

instance : IsLieAbelian (typeDDiagonalCartan K ι) where
  trivial A B := by
    apply Subtype.ext
    apply Subtype.ext
    exact lie_eq_zero_of_isDiag
      (mem_typeDDiagonalCartan_iff_isDiag.mp A.2)
      (mem_typeDDiagonalCartan_iff_isDiag.mp B.2)

/-! ### Self-normalization -/

section

omit [DecidableEq ι] [Fintype ι] in
private theorem exists_isRegular_typeDDiagonalValue_sub (h2 : IsRegular (2 : K))
    (a b : ι ⊕ ι) (hab : a ≠ b) :
    ∃ d : ι → K, IsRegular (typeDDiagonalValue d b - typeDDiagonalValue d a) := by
  classical
  rcases a with i | i <;> rcases b with j | j
  · have hij : i ≠ j := fun h => hab (congrArg Sum.inl h)
    refine ⟨Pi.single i 1, ?_⟩
    simpa [typeDDiagonalValue, hij] using
      (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · refine ⟨Pi.single i 1, ?_⟩
    by_cases hij : i = j
    · subst j
      simp only [typeDDiagonalValue_inr, Pi.single_eq_same, typeDDiagonalValue_inl]
      simpa only [sub_eq_add_neg, ← neg_add, one_add_one_eq_two, neg_one_mul] using
        isUnit_neg_one.isRegular.mul h2
    · simpa [typeDDiagonalValue, hij] using
        (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · refine ⟨Pi.single i 1, ?_⟩
    by_cases hij : i = j
    · subst j
      simp only [typeDDiagonalValue_inl, Pi.single_eq_same, typeDDiagonalValue_inr,
        sub_neg_eq_add]
      simpa only [one_add_one_eq_two] using h2
    · simpa [typeDDiagonalValue, hij] using (isRegular_one : IsRegular (1 : K))
  · have hij : i ≠ j := fun h => hab (congrArg Sum.inr h)
    refine ⟨Pi.single i 1, ?_⟩
    simpa [typeDDiagonalValue, hij] using (isRegular_one : IsRegular (1 : K))

/-- The adjoint action of the matrix `diag(d, -d)` scales each matrix entry by the difference of
its two coordinate weights. -/
@[simp]
theorem typeDDiagonalMatrix_lie_apply (d : ι → K) (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K)
    (a b : ι ⊕ ι) :
    ⁅typeDDiagonalMatrix d, X⁆ a b =
      (typeDDiagonalValue d a - typeDDiagonalValue d b) * X a b := by
  simpa only [typeDDiagonalMatrix, diagonal_apply_eq] using
    lie_apply_of_mem_diagonalCartan
      (diagonal_mem_diagonalCartan (typeDDiagonalValue d))
      X a b

/-- The adjoint action of the bundled Cartan element `diag(d, -d)` has the same entrywise normal
form. -/
theorem typeDDiagonalEquiv_lie_apply (d : ι → K) (X : LieAlgebra.Orthogonal.typeD ι K)
    (a b : ι ⊕ ι) :
    ((⁅(typeDDiagonalEquiv (K := K) (ι := ι) d : typeDDiagonalCartan K ι), X⁆ :
        LieAlgebra.Orthogonal.typeD ι K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b =
      (typeDDiagonalValue d a - typeDDiagonalValue d b) *
        (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b := by
  simpa only [LieSubalgebra.coe_bracket_of_module, coe_typeDDiagonalEquiv_apply,
    LieSubalgebra.coe_bracket] using typeDDiagonalMatrix_lie_apply d X a b

/-- Bracketing in the reverse order with the matrix `diag(d, -d)` scales each matrix entry by the
reverse weight difference. -/
@[simp]
theorem lie_typeDDiagonalMatrix_apply (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (d : ι → K)
    (a b : ι ⊕ ι) :
    ⁅X, typeDDiagonalMatrix d⁆ a b =
      (typeDDiagonalValue d b - typeDDiagonalValue d a) * X a b := by
  have hskew :
      ⁅X, typeDDiagonalMatrix d⁆ = -⁅typeDDiagonalMatrix d, X⁆ :=
    (lie_skew _ _).symm
  rw [hskew, Matrix.neg_apply, typeDDiagonalMatrix_lie_apply]
  ring

/-- Bracketing in the reverse order with the bundled Cartan element `diag(d, -d)` has the same
entrywise normal form. -/
theorem lie_typeDDiagonalEquiv_apply (X : LieAlgebra.Orthogonal.typeD ι K) (d : ι → K)
    (a b : ι ⊕ ι) :
    ((⁅X, (typeDDiagonalEquiv (K := K) (ι := ι) d : typeDDiagonalCartan K ι)⁆ :
        LieAlgebra.Orthogonal.typeD ι K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b =
      (typeDDiagonalValue d b - typeDDiagonalValue d a) *
        (X : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b := by
  simpa only [coe_typeDDiagonalEquiv_apply, LieSubalgebra.coe_bracket] using
    lie_typeDDiagonalMatrix_apply X d a b

variable (K ι)

/-- The diagonal Cartan of type `D` is self-normalizing. -/
theorem typeDDiagonalCartan_normalizer_eq_self (h2 : IsRegular (2 : K)) :
    (typeDDiagonalCartan K ι).normalizer = typeDDiagonalCartan K ι := by
  refine le_antisymm (fun X hX => mem_typeDDiagonalCartan_iff_isDiag.mpr fun a b hab => ?_)
    (typeDDiagonalCartan K ι).le_normalizer
  obtain ⟨d, hd⟩ := exists_isRegular_typeDDiagonalValue_sub (K := K) h2 a b hab
  have hbracket := ((typeDDiagonalCartan K ι).mem_normalizer_iff X).mp hX
    (typeDDiagonalEquiv (K := K) (ι := ι) d)
    (typeDDiagonalEquiv (K := K) (ι := ι) d).2
  have hzero :
      ((⁅X, (typeDDiagonalEquiv (K := K) (ι := ι) d : typeDDiagonalCartan K ι)⁆ :
          LieAlgebra.Orthogonal.typeD ι K) : Matrix (ι ⊕ ι) (ι ⊕ ι) K) a b = 0 :=
    (mem_typeDDiagonalCartan_iff_isDiag.mp hbracket) hab
  rw [lie_typeDDiagonalEquiv_apply] at hzero
  apply hd.left
  simpa using hzero

/-- The diagonal matrices form a Cartan subalgebra of the split orthogonal Lie algebra of type
`D`: they are abelian, hence nilpotent, and self-normalizing. -/
instance instIsCartanSubalgebraTypeDDiagonalCartan [h2 : Fact (IsRegular (2 : K))] :
    (typeDDiagonalCartan K ι).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := typeDDiagonalCartan_normalizer_eq_self K ι h2.out

/-- Over a domain, nonvanishing of `2` supplies the regularity needed by the type-`D` Cartan
instance. -/
instance (priority := low) instIsCartanSubalgebraTypeDDiagonalCartanOfNoZeroDivisors
    [NoZeroDivisors K] [NeZero (2 : K)] :
    (typeDDiagonalCartan K ι).IsCartanSubalgebra := by
  let _ : Fact (IsRegular (2 : K)) :=
    ⟨IsRegular.of_ne_zero' (NeZero.ne (2 : K))⟩
  infer_instance

end

/-! ### A basis and dual coordinates -/

/-- The coordinate basis of the type-`D` diagonal Cartan. -/
noncomputable def typeDDiagonalCartanBasis : Module.Basis ι K (typeDDiagonalCartan K ι) :=
  Module.Basis.ofEquivFun (typeDDiagonalEquiv (K := K) (ι := ι)).symm

@[simp]
theorem coe_typeDDiagonalCartanBasis_apply (i : ι) :
    ((typeDDiagonalCartanBasis (K := K) (ι := ι) i : typeDDiagonalCartan K ι) :
      LieAlgebra.Orthogonal.typeD ι K) =
      ⟨typeDDiagonalMatrix (Pi.single i 1),
        typeDDiagonalMatrix_mem_typeD (Pi.single i 1)⟩ := by
  rw [typeDDiagonalCartanBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
    coe_typeDDiagonalEquiv_apply]

@[simp]
theorem typeDDiagonalCartanBasis_repr_apply (A : typeDDiagonalCartan K ι) (i : ι) :
    (typeDDiagonalCartanBasis (K := K) (ι := ι)).repr A i =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) := by
  rw [typeDDiagonalCartanBasis, Module.Basis.ofEquivFun_repr_apply,
    typeDDiagonalEquiv_symm_apply]

instance : Module.Free K (typeDDiagonalCartan K ι) :=
  Module.Free.of_basis (typeDDiagonalCartanBasis (K := K) (ι := ι))

instance : Module.Finite K (typeDDiagonalCartan K ι) :=
  Module.Finite.of_basis (typeDDiagonalCartanBasis (K := K) (ι := ι))

/-- The type-`D` diagonal Cartan has dimension `Fintype.card ι`. -/
theorem finrank_typeDDiagonalCartan [StrongRankCondition K] :
    Module.finrank K (typeDDiagonalCartan K ι) = Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (typeDDiagonalCartanBasis (K := K) (ι := ι))]

/-- Coordinates on the type-`D` Cartan are also coordinates on its dual. -/
noncomputable def typeDWeightEquiv :
    (ι → K) ≃ₗ[K] Module.Dual K (typeDDiagonalCartan K ι) :=
  (typeDDiagonalCartanBasis (K := K) (ι := ι)).dualBasis.equivFun.symm

@[simp]
theorem typeDWeightEquiv_apply (mu : ι → K) (A : typeDDiagonalCartan K ι) :
    typeDWeightEquiv (K := K) (ι := ι) mu A =
      ∑ i, mu i * (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) := by
  simp [typeDWeightEquiv, Module.Basis.equivFun_symm_apply,
    typeDDiagonalCartanBasis_repr_apply]

@[simp]
theorem typeDWeightEquiv_symm_apply
    (f : Module.Dual K (typeDDiagonalCartan K ι)) (i : ι) :
    (typeDWeightEquiv (K := K) (ι := ι)).symm f i =
      f (typeDDiagonalCartanBasis (K := K) (ι := ι) i) := by
  exact (typeDDiagonalCartanBasis (K := K) (ι := ι)).dualBasis_equivFun f i

/-- The coordinate functional `εᵢ` on the type-`D` diagonal Cartan. -/
noncomputable def typeDEpsilon (i : ι) : Module.Dual K (typeDDiagonalCartan K ι) :=
  (typeDDiagonalCartanBasis (K := K) (ι := ι)).dualBasis i

@[simp]
theorem typeDEpsilon_apply (i : ι) (A : typeDDiagonalCartan K ι) :
    typeDEpsilon (K := K) (ι := ι) i A =
      (A : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (.inl i) (.inl i) := by
  rw [typeDEpsilon, Module.Basis.dualBasis_apply,
    typeDDiagonalCartanBasis_repr_apply]

end TauCeti
