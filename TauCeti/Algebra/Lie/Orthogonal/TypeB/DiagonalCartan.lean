/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import Mathlib.Algebra.Lie.Classical

/-!
# The diagonal Cartan subalgebra of the split orthogonal Lie algebra of type B

Mathlib's `LieAlgebra.Orthogonal.typeB ι K` is the Lie algebra of matrices skew-adjoint for
the split symmetric form with matrix

```text
[ 2  0  0 ]
[ 0  0  1 ]
[ 0  1  0 ].
```

Its standard Cartan subalgebra consists of the matrices `diag(0, d, -d)`. This file bundles that
subalgebra, proves that it is abelian and self-normalizing, and gives its coordinate basis and
dual coordinates. The regularity of `2` is needed only for self-normalization: it distinguishes
the two opposite coordinate weights.

## Main definitions

* `TauCeti.typeBDiagonalCartan`: the diagonal Cartan subalgebra of
  `LieAlgebra.Orthogonal.typeB ι K`.
* `TauCeti.typeBDiagonalEquiv`: the coordinate equivalence
  `(ι → K) ≃ₗ[K] typeBDiagonalCartan K ι`.
* `TauCeti.typeBDiagonalCartanBasis`: its basis by the matrices with diagonal entries `1` and
  `-1` in paired positions.
* `TauCeti.typeBWeightEquiv`: the corresponding coordinate equivalence with the dual Cartan.
* `TauCeti.typeBEpsilon`: the coordinate functional `εᵢ`.

## Main results

* `TauCeti.typeBDiagonalCartan_normalizer_eq_self`: the diagonal Cartan is self-normalizing.
* `TauCeti.instIsCartanSubalgebraTypeBDiagonalCartan`: it is a Cartan subalgebra.
* `TauCeti.finrank_typeBDiagonalCartan`: its dimension is `Fintype.card ι`.

## References

The construction follows Fulton--Harris, *Representation Theory*, Lecture 20. Its declaration
order and coordinate API follow `TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan` and the type-D
analogue in [TauCeti#4356](https://github.com/TauCetiProject/TauCeti/pull/4356). This is the
split type-`B` Cartan prerequisite for Layer 5 of the Spin-representations roadmap.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [CommRing K]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### The diagonal matrices of type B -/

/-- The weight of a coordinate in the standard type-`B` module: zero on the middle coordinate,
`d i` on the first copy of `ι`, and `-d i` on the second. -/
def typeBDiagonalValue (d : ι → K) : Unit ⊕ ι ⊕ ι → K :=
  Sum.elim 0 (Sum.elim d (-d))

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem typeBDiagonalValue_inl (d : ι → K) (i : Unit) :
    typeBDiagonalValue d (.inl i) = 0 :=
  (rfl)

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem typeBDiagonalValue_inr_inl (d : ι → K) (i : ι) :
    typeBDiagonalValue d (.inr (.inl i)) = d i :=
  (rfl)

omit [DecidableEq ι] [Fintype ι] in
@[simp]
theorem typeBDiagonalValue_inr_inr (d : ι → K) (i : ι) :
    typeBDiagonalValue d (.inr (.inr i)) = -d i :=
  (rfl)

/-- The ambient matrix `diag(0, d, -d)` in the split type-`B` model. -/
def typeBDiagonalMatrix (d : ι → K) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  diagonal (typeBDiagonalValue d)

omit [Fintype ι] in
@[simp]
theorem typeBDiagonalMatrix_apply (d : ι → K) (i j : Unit ⊕ ι ⊕ ι) :
    typeBDiagonalMatrix d i j = if i = j then typeBDiagonalValue d i else 0 :=
  (rfl)

/-- Every `diag(0, d, -d)` is skew-adjoint for the split type-`B` form. -/
theorem typeBDiagonalMatrix_mem_typeB (d : ι → K) :
    typeBDiagonalMatrix d ∈ LieAlgebra.Orthogonal.typeB ι K := by
  rw [LieAlgebra.Orthogonal.typeB, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  -- Unfold the skew-adjoint submodule predicate to the matrix equation defining `typeB`.
  change (typeBDiagonalMatrix d)ᵀ * LieAlgebra.Orthogonal.JB ι K =
    LieAlgebra.Orthogonal.JB ι K * (-typeBDiagonalMatrix d)
  ext a b
  rcases a with a | (a | a)
  · rcases b with b | (b | b)
    · cases a; cases b
      simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
  · rcases b with b | (b | b)
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
    · by_cases h : a = b
      · subst b
        simp [typeBDiagonalMatrix, typeBDiagonalValue,
          LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply]
      · simp [typeBDiagonalMatrix, typeBDiagonalValue,
          LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply, h]
  · rcases b with b | (b | b)
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply]
    · by_cases h : a = b
      · subst b
        simp [typeBDiagonalMatrix, typeBDiagonalValue,
          LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply]
      · simp [typeBDiagonalMatrix, typeBDiagonalValue,
          LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply, h]
    · simp [typeBDiagonalMatrix, typeBDiagonalValue,
        LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply, Matrix.one_apply]

/-! ### The Cartan subalgebra and its coordinates -/

variable (K ι)

/-- The explicit diagonal matrices `diag(0, d, -d)` inside the split orthogonal Lie algebra of
type `B`. -/
def typeBDiagonalCartan : LieSubalgebra K (LieAlgebra.Orthogonal.typeB ι K) where
  carrier := {A | ∃ d : ι → K,
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBDiagonalMatrix d}
  zero_mem' := ⟨0, by ext a b; simp [typeBDiagonalMatrix, typeBDiagonalValue]⟩
  add_mem' := by
    rintro A B ⟨d, hd⟩ ⟨e, he⟩
    refine ⟨d + e, ?_⟩
    -- Expose the ambient matrix addition beneath the two subtype coercions.
    rw [show ((A + B : LieAlgebra.Orthogonal.typeB ι K) :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) =
        (A : Matrix _ _ K) + (B : Matrix _ _ K) from rfl, hd, he]
    ext a b
    by_cases hab : a = b
    · subst b
      rcases a with a | (a | a) <;> simp [typeBDiagonalMatrix, typeBDiagonalValue, add_comm]
    · simp [typeBDiagonalMatrix, hab]
  smul_mem' := by
    rintro c A ⟨d, hd⟩
    refine ⟨c • d, ?_⟩
    -- Expose the ambient matrix scalar action beneath the two subtype coercions.
    rw [show ((c • A : LieAlgebra.Orthogonal.typeB ι K) :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) =
        c • (A : Matrix _ _ K) from rfl, hd]
    ext a b
    by_cases hab : a = b
    · subst b
      rcases a with a | (a | a) <;> simp [typeBDiagonalMatrix, typeBDiagonalValue]
    · simp [typeBDiagonalMatrix, hab]
  lie_mem' := by
    rintro A B ⟨d, hd⟩ ⟨e, he⟩
    refine ⟨0, ?_⟩
    -- The bracket inherited by `typeB` is the ambient matrix commutator.
    change (⁅(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K),
      (B : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)⁆ :
        Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBDiagonalMatrix 0
    rw [lie_eq_zero_of_isDiag (hd ▸ isDiag_diagonal _) (he ▸ isDiag_diagonal _)]
    ext a b
    simp [typeBDiagonalMatrix, typeBDiagonalValue]

variable {K ι}

/-- Membership in the type-`B` diagonal Cartan is an explicit `diag(0, d, -d)` presentation. -/
theorem mem_typeBDiagonalCartan_iff {A : LieAlgebra.Orthogonal.typeB ι K} :
    A ∈ typeBDiagonalCartan K ι ↔ ∃ d : ι → K,
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) = typeBDiagonalMatrix d :=
  Iff.rfl

/-- The coordinate equivalence from `ι`-tuples to the type-`B` diagonal Cartan. -/
def typeBDiagonalEquiv : (ι → K) ≃ₗ[K] typeBDiagonalCartan K ι where
  toFun d := ⟨⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩, ⟨d, rfl⟩⟩
  map_add' d e := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    by_cases hab : a = b
    · subst b
      rcases a with a | (a | a) <;> simp [typeBDiagonalMatrix, typeBDiagonalValue, add_comm]
    · simp [typeBDiagonalMatrix, hab]
  map_smul' c d := by
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    by_cases hab : a = b
    · subst b
      rcases a with a | (a | a) <;> simp [typeBDiagonalMatrix, typeBDiagonalValue]
    · simp [typeBDiagonalMatrix, hab]
  invFun A i := (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i))
  left_inv d := by simp [typeBDiagonalMatrix]
  right_inv A := by
    obtain ⟨d, hd⟩ := A.2
    have hcoord : (fun i =>
        (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)
          (.inr (.inl i)) (.inr (.inl i))) = d := by
      funext i
      rw [hd]
      simp [typeBDiagonalMatrix]
    apply Subtype.ext
    apply Subtype.ext
    -- Expose the matrix represented by the reconstructed coordinate tuple.
    change typeBDiagonalMatrix (fun i =>
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)
        (.inr (.inl i)) (.inr (.inl i))) =
          (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)
    rw [hcoord, hd]

@[simp]
theorem coe_typeBDiagonalEquiv_apply (d : ι → K) :
    ((typeBDiagonalEquiv (K := K) (ι := ι) d : typeBDiagonalCartan K ι) :
      LieAlgebra.Orthogonal.typeB ι K) =
      ⟨typeBDiagonalMatrix d, typeBDiagonalMatrix_mem_typeB d⟩ :=
  (rfl)

@[simp]
theorem typeBDiagonalEquiv_symm_apply (A : typeBDiagonalCartan K ι) (i : ι) :
    (typeBDiagonalEquiv (K := K) (ι := ι)).symm A i =
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i)) :=
  (rfl)

instance : IsLieAbelian (typeBDiagonalCartan K ι) where
  trivial A B := by
    obtain ⟨d, hd⟩ := A.2
    obtain ⟨e, he⟩ := B.2
    apply Subtype.ext
    apply Subtype.ext
    exact lie_eq_zero_of_isDiag (hd ▸ isDiag_diagonal _) (he ▸ isDiag_diagonal _)

/-! ### Self-normalization -/

section

omit [DecidableEq ι] [Fintype ι] in
private theorem exists_isRegular_typeBDiagonalValue_sub (h2 : IsRegular (2 : K))
    (a b : Unit ⊕ ι ⊕ ι) (hab : a ≠ b) :
    ∃ d : ι → K, IsRegular (typeBDiagonalValue d b - typeBDiagonalValue d a) := by
  classical
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact (hab (congrArg Sum.inl (Subsingleton.elim a b))).elim
  · refine ⟨Pi.single b 1, ?_⟩
    simpa using (isRegular_one : IsRegular (1 : K))
  · refine ⟨Pi.single b 1, ?_⟩
    simpa using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · refine ⟨Pi.single a 1, ?_⟩
    simpa using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · have hab' : a ≠ b := fun h => hab (congrArg (Sum.inr ∘ Sum.inl) h)
    refine ⟨Pi.single a 1, ?_⟩
    simpa [hab'] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · refine ⟨Pi.single a 1, ?_⟩
    by_cases h : a = b
    · subst b
      -- Opposite coordinate weights differ by the regular element `-2`.
      rw [show typeBDiagonalValue (Pi.single a 1) (.inr (.inr a)) -
        typeBDiagonalValue (Pi.single a 1) (.inr (.inl a)) = (-1 : K) * 2 by simp; ring]
      exact isUnit_neg_one.isRegular.mul h2
    · simpa [h] using (isUnit_neg_one.isRegular : IsRegular (-1 : K))
  · refine ⟨Pi.single a 1, ?_⟩
    simpa using (isRegular_one : IsRegular (1 : K))
  · refine ⟨Pi.single a 1, ?_⟩
    by_cases h : a = b
    · subst b
      -- Opposite coordinate weights differ by the regular element `2`.
      rw [show typeBDiagonalValue (Pi.single a 1) (.inr (.inl a)) -
        typeBDiagonalValue (Pi.single a 1) (.inr (.inr a)) = (2 : K) by simp; ring]
      exact h2
    · simpa [h] using (isRegular_one : IsRegular (1 : K))
  · have hab' : a ≠ b := fun h => hab (congrArg (Sum.inr ∘ Sum.inr) h)
    refine ⟨Pi.single a 1, ?_⟩
    simpa [hab'] using (isRegular_one : IsRegular (1 : K))

/-- Bracketing with `diag(0, d, -d)` scales each matrix entry by the difference of its two
coordinate weights. -/
theorem lie_typeBDiagonalEquiv_apply (X : LieAlgebra.Orthogonal.typeB ι K) (d : ι → K)
    (a b : Unit ⊕ ι ⊕ ι) :
    ((⁅X, (typeBDiagonalEquiv (K := K) (ι := ι) d : typeBDiagonalCartan K ι)⁆ :
        LieAlgebra.Orthogonal.typeB ι K) : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b =
      (typeBDiagonalValue d b - typeBDiagonalValue d a) *
        (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b := by
  have h := lie_apply_of_mem_diagonalCartan
    (diagonal_mem_diagonalCartan (typeBDiagonalValue d))
    (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b
  -- Identify the public type-`B` diagonal with the ambient diagonal used by the generic theorem.
  change (⁅typeBDiagonalMatrix d,
    (X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)⁆ :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b = _ at h
  -- Coerce the type-`B` bracket to matrices and reverse its order.
  change (⁅(X : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K),
    typeBDiagonalMatrix d⁆ : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b = _
  rw [(lie_skew _ _).symm, Matrix.neg_apply, h]
  simp only [diagonal_apply_eq]
  ring

private theorem typeB_apply_inr_inr (A : LieAlgebra.Orthogonal.typeB ι K) (i : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inr (.inr i)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i)) := by
  have hA := A.2
  -- The subtype witness is the skew-adjoint equation for Mathlib's matrix `JB`.
  change (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JB ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  have h := congr_fun (congr_fun hA (.inr (.inl i))) (.inr (.inr i))
  exact neg_eq_iff_eq_neg.mp (by
    simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
      Matrix.one_apply] using h.symm)

private theorem typeB_apply_inl_inl_eq_zero (h2 : IsRegular (2 : K))
    (A : LieAlgebra.Orthogonal.typeB ι K) (i : Unit) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl i) (.inl i) = 0 := by
  cases i
  have hA := A.2
  -- The subtype witness is the skew-adjoint equation for Mathlib's matrix `JB`.
  change (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JB ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  have h := congr_fun (congr_fun hA (.inl ())) (.inl ())
  apply h2.left
  apply h2.left
  simp only [mul_zero]
  have h' :
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl ()) (.inl ()) * 2 =
        -(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl ()) (.inl ())) := by
    simpa [LieAlgebra.Orthogonal.JB, Matrix.mul_apply, Matrix.one_apply] using h
  calc
    2 * (2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl ()) (.inl ())) =
        (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl ()) (.inl ()) * 2 -
          (-(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl ()) (.inl ()))) := by ring
    _ = 0 := sub_eq_zero.mpr h'

/-- When multiplication by `2` is injective, membership in the type-`B` diagonal Cartan is
equivalent to being diagonal as an ambient matrix. Skew-adjointness then forces the middle entry
to vanish and the two remaining diagonal blocks to be opposite. -/
theorem mem_typeBDiagonalCartan_iff_isDiag (h2 : IsRegular (2 : K))
    {A : LieAlgebra.Orthogonal.typeB ι K} :
    A ∈ typeBDiagonalCartan K ι ↔
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K).IsDiag := by
  constructor
  · rintro ⟨d, hd⟩
    exact hd ▸ isDiag_diagonal _
  · intro hdiag
    refine mem_typeBDiagonalCartan_iff.mpr ⟨fun i =>
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)), ?_⟩
    ext a b
    by_cases hab : a = b
    · subst b
      rcases a with a | (a | a)
      · simpa [typeBDiagonalMatrix] using (typeB_apply_inl_inl_eq_zero h2 A a)
      · simp [typeBDiagonalMatrix]
      · simpa [typeBDiagonalMatrix] using (typeB_apply_inr_inr A a)
    · simpa [typeBDiagonalMatrix_apply, hab] using hdiag hab

variable (K ι)

/-- The diagonal Cartan of type `B` is self-normalizing when multiplication by `2` is injective. -/
@[simp]
theorem typeBDiagonalCartan_normalizer_eq_self (h2 : IsRegular (2 : K)) :
    (typeBDiagonalCartan K ι).normalizer = typeBDiagonalCartan K ι := by
  refine le_antisymm (fun X hX => ?_) (typeBDiagonalCartan K ι).le_normalizer
  apply (mem_typeBDiagonalCartan_iff_isDiag h2).2
  -- The normalizer element has two subtype layers; expose its ambient matrix diagonal condition.
  show ((X : LieAlgebra.Orthogonal.typeB ι K) :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K).IsDiag
  intro a b hab
  -- Reduce the diagonal predicate to the corresponding ambient matrix entry.
  show ((X : LieAlgebra.Orthogonal.typeB ι K) :
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) a b = 0
  obtain ⟨d, hd⟩ := exists_isRegular_typeBDiagonalValue_sub (K := K) h2 a b hab
  have hbracket := ((typeBDiagonalCartan K ι).mem_normalizer_iff X).mp hX
    (typeBDiagonalEquiv (K := K) (ι := ι) d)
    (typeBDiagonalEquiv (K := K) (ι := ι) d).2
  obtain ⟨e, he⟩ := hbracket
  have hzero :
      ((⁅X, (typeBDiagonalEquiv (K := K) (ι := ι) d : typeBDiagonalCartan K ι)⁆ :
          LieAlgebra.Orthogonal.typeB ι K) : Matrix _ _ K) a b = 0 := by
    rw [he]
    exact (isDiag_diagonal (typeBDiagonalValue e)) hab
  rw [lie_typeBDiagonalEquiv_apply] at hzero
  apply hd.left
  simpa using hzero

/-- The diagonal matrices form a Cartan subalgebra of the split orthogonal Lie algebra of type
`B`: they are abelian, hence nilpotent, and self-normalizing. -/
instance instIsCartanSubalgebraTypeBDiagonalCartan [h2 : Fact (IsRegular (2 : K))] :
    (typeBDiagonalCartan K ι).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := typeBDiagonalCartan_normalizer_eq_self K ι h2.out

/-- Over a domain, nonvanishing of `2` supplies the regularity needed by the type-`B` Cartan
instance. -/
instance (priority := low) instIsCartanSubalgebraTypeBDiagonalCartanOfNoZeroDivisors
    [NoZeroDivisors K] [NeZero (2 : K)] :
    (typeBDiagonalCartan K ι).IsCartanSubalgebra := by
  let _ : Fact (IsRegular (2 : K)) :=
    ⟨IsRegular.of_ne_zero' (NeZero.ne (2 : K))⟩
  infer_instance

end

/-! ### A basis and dual coordinates -/

/-- The coordinate basis of the type-`B` diagonal Cartan. -/
noncomputable def typeBDiagonalCartanBasis : Module.Basis ι K (typeBDiagonalCartan K ι) :=
  Module.Basis.ofEquivFun (typeBDiagonalEquiv (K := K) (ι := ι)).symm

@[simp]
theorem coe_typeBDiagonalCartanBasis_apply (i : ι) :
    ((typeBDiagonalCartanBasis (K := K) (ι := ι) i : typeBDiagonalCartan K ι) :
      LieAlgebra.Orthogonal.typeB ι K) =
      ⟨typeBDiagonalMatrix (Pi.single i 1),
        typeBDiagonalMatrix_mem_typeB (Pi.single i 1)⟩ := by
  rw [typeBDiagonalCartanBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm,
    coe_typeBDiagonalEquiv_apply]

@[simp]
theorem typeBDiagonalCartanBasis_repr_apply (A : typeBDiagonalCartan K ι) (i : ι) :
    (typeBDiagonalCartanBasis (K := K) (ι := ι)).repr A i =
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i)) := by
  rw [typeBDiagonalCartanBasis, Module.Basis.ofEquivFun_repr_apply,
    typeBDiagonalEquiv_symm_apply]

instance : Module.Free K (typeBDiagonalCartan K ι) :=
  Module.Free.of_basis (typeBDiagonalCartanBasis (K := K) (ι := ι))

instance : Module.Finite K (typeBDiagonalCartan K ι) :=
  Module.Finite.of_basis (typeBDiagonalCartanBasis (K := K) (ι := ι))

/-- The type-`B` diagonal Cartan has dimension `Fintype.card ι`. -/
theorem finrank_typeBDiagonalCartan [StrongRankCondition K] :
    Module.finrank K (typeBDiagonalCartan K ι) = Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (typeBDiagonalCartanBasis (K := K) (ι := ι))]

/-- Coordinates on the type-`B` Cartan are also coordinates on its dual. -/
noncomputable def typeBWeightEquiv :
    (ι → K) ≃ₗ[K] Module.Dual K (typeBDiagonalCartan K ι) :=
  (typeBDiagonalEquiv (K := K) (ι := ι)).trans
    (typeBDiagonalCartanBasis (K := K) (ι := ι)).toDualEquiv

@[simp]
theorem typeBWeightEquiv_apply (mu : ι → K) (A : typeBDiagonalCartan K ι) :
    typeBWeightEquiv (K := K) (ι := ι) mu A =
      ∑ i, mu i * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i)) := by
  conv_lhs => rw [← (typeBDiagonalCartanBasis (K := K) (ι := ι)).sum_repr A]
  simp [typeBWeightEquiv, Module.Basis.toDual_apply_left, mul_comm]

@[simp]
theorem typeBWeightEquiv_symm_apply
    (f : Module.Dual K (typeBDiagonalCartan K ι)) (i : ι) :
    (typeBWeightEquiv (K := K) (ι := ι)).symm f i =
      f (typeBDiagonalCartanBasis (K := K) (ι := ι) i) := by
  let b := typeBDiagonalCartanBasis (K := K) (ι := ι)
  -- Unfold the composite equivalence to the coordinate statement of its defining basis.
  change b.repr (b.toDualEquiv.symm f) i = f (b i)
  simpa only [Module.Basis.toDualEquiv_apply, Module.Basis.toDual_apply_left] using
    LinearMap.congr_fun (b.toDualEquiv.apply_symm_apply f) (b i)

/-- The coordinate functional `εᵢ` on the type-`B` diagonal Cartan. -/
noncomputable def typeBEpsilon (i : ι) : Module.Dual K (typeBDiagonalCartan K ι) :=
  typeBWeightEquiv (K := K) (ι := ι) (Pi.single i 1)

@[simp]
theorem typeBEpsilon_apply (i : ι) (A : typeBDiagonalCartan K ι) :
    typeBEpsilon (K := K) (ι := ι) i A =
      (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inl i)) := by
  simp [typeBEpsilon, Pi.single_apply]

end TauCeti
