/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.GeneratorRelations
import TauCeti.Algebra.Lie.GeneralLinear.Basic

/-!
# Serre relations in the standard split Lie algebra of type B

The Bourbaki-numbered matrices in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.RootGenerators` give explicit positive-root,
negative-root, and coroot generators for the standard integral split orthogonal Lie algebra of
type `B`. This file proves the two families of Serre relations not supplied by the Cartan-action
computations:

* positive and negative generators at distinct simple nodes commute;
* the iterated adjoint actions between two positive generators, and between two negative
  generators, vanish with the exponents prescribed by the transposed type-`B` Cartan matrix.

The transpose is the convention used by the existing Cartan-action API: the coroot index is the
first index in `⁅hᵢ, eⱼ⁆`. All results hold over an arbitrary commutative ring, including in
characteristic two. Together with the Cartan-action relations, these are the inputs for packaging
the standard matrices as a `TauCeti.IsSerreSystem` and hence for mapping the integral Kostant form
into the standard type-`B` representation.

## Main results

* `TauCeti.typeBSimpleRootGenerator_lie_negativeRoot_of_ne`: distinct positive and negative
  simple-root generators commute.
* `TauCeti.ad_pow_lie_typeBSimpleRootGenerator`: the higher positive Serre relations.
* `TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator`: the higher negative Serre relations.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Chapter VI, Appendix.

This supplies the mixed and higher generator relations needed by the Chevalley--Demazure
construction and pinnings in Layer 9 of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

open LieAlgebra Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {K : Type u} [CommRing K]
variable {n : ℕ}

private theorem lie_typeBSimpleRootMatrix_typeBSimpleNegativeRootMatrix_of_ne
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅typeBSimpleRootMatrix (K := K) i, typeBSimpleNegativeRootMatrix (K := K) j⁆ = 0 := by
  induction i using Fin.lastCases with
  | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j₀ =>
          simp only [typeBSimpleRootMatrix_last, typeBSimpleNegativeRootMatrix_castSucc]
          simp [typeBShortRootMatrix_def, typeBLongRootMatrix_def, lie_sub, sub_lie,
            lie_single_single, hij]
  | cast i₀ =>
      induction j using Fin.lastCases with
      | last =>
          have hlast : Fin.last n ≠ i₀.castSucc := fun h ↦ hij h.symm
          simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_last]
          simp [typeBLongRootMatrix_def, typeBShortNegativeRootMatrix_def, lie_sub, sub_lie,
            lie_single_single, hij, hlast]
      | cast j₀ =>
          have hij₀ : i₀ ≠ j₀ := fun h ↦ hij (congrArg Fin.castSucc h)
          simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_castSucc]
          simp [typeBLongRootMatrix_def, lie_sub, sub_lie, lie_single_single, hij₀,
            hij₀.symm]

/-- Positive and negative simple-root generators at distinct Bourbaki nodes commute. -/
@[simp]
theorem typeBSimpleRootGenerator_lie_negativeRoot_of_ne
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅typeBSimpleRootGenerator (K := K) i, typeBSimpleNegativeRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  simpa only [coe_typeBSimpleRootGenerator, coe_typeBSimpleNegativeRootGenerator,
    LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using
      lie_typeBSimpleRootMatrix_typeBSimpleNegativeRootMatrix_of_ne (K := K) i j hij

/-- The higher Serre relation for the positive simple-root generators of the standard split
type-`B` Lie algebra. The Cartan matrix is transposed to match the coroot-first convention in the
Cartan-action relations. -/
@[simp]
theorem ad_pow_lie_typeBSimpleRootGenerator (i j : Fin (n + 1)) :
    (ad K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (typeBSimpleRootGenerator (K := K) i) ^
      (-(CartanMatrix.B (n + 1)).transpose i j).toNat)
        ⁅typeBSimpleRootGenerator (K := K) i, typeBSimpleRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket,
    coe_typeBSimpleRootGenerator, coe_typeBSimpleRootGenerator]
  simp only [ZeroMemClass.coe_zero]
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp
    · simp only [typeBSimpleRootMatrix_last, typeBSimpleRootMatrix_castSucc]
      simp_rw [typeBShortRootMatrix_def, typeBLongRootMatrix_def]
      rcases j₀ with ⟨j, hj⟩
      have hjn : j ≠ n := by omega
      have hnj : n ≠ j := hjn.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff, pow_two, Module.End.mul_apply] <;>
        omega
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleRootMatrix_last]
      simp_rw [typeBLongRootMatrix_def, typeBShortRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      have hin : i ≠ n := by omega
      have hni : n ≠ i := hin.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff] <;>
        omega
    · simp only [typeBSimpleRootMatrix_castSucc]
      simp_rw [typeBLongRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      rcases j₀ with ⟨j, hj⟩
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp only [Fin.succ_mk, map_sub, Int.reduceNeg, neg_neg,
        Int.reduceToNat, Int.toNat_one, pow_one, neg_zero, Int.toNat_zero, pow_zero,
        lie_sub, sub_lie, lie_single_single, Sum.inr.injEq, Sum.inl.injEq,
        Fin.mk.injEq, mul_one, reduceCtorEq, ↓reduceIte, sub_self, sub_zero, zero_sub,
        neg_sub, LinearMap.sub_apply, LieAlgebra.ad_apply, Module.End.one_apply] <;>
        (first | omega | split_ifs) <;>
        try simp only [lie_zero, lie_single_single, Sum.inr.injEq, Sum.inl.injEq,
          Fin.mk.injEq, mul_one, Nat.add_eq_left, one_ne_zero, ↓reduceIte, sub_zero,
          zero_sub, reduceCtorEq, sub_self, Nat.left_eq_add, sub_neg_eq_add, zero_add] <;>
        simp only [Fin.ext_iff] at * <;>
        (first | omega | (split_ifs; simp))
      all_goals omega

/-- The higher Serre relation for the negative simple-root generators of the standard split
type-`B` Lie algebra. -/
@[simp]
theorem ad_pow_lie_typeBSimpleNegativeRootGenerator (i j : Fin (n + 1)) :
    (ad K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (typeBSimpleNegativeRootGenerator (K := K) i) ^
      (-(CartanMatrix.B (n + 1)).transpose i j).toNat)
        ⁅typeBSimpleNegativeRootGenerator (K := K) i,
          typeBSimpleNegativeRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket,
    coe_typeBSimpleNegativeRootGenerator, coe_typeBSimpleNegativeRootGenerator]
  simp only [ZeroMemClass.coe_zero]
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp
    · simp only [typeBSimpleNegativeRootMatrix_last,
        typeBSimpleNegativeRootMatrix_castSucc]
      simp_rw [typeBShortNegativeRootMatrix_def, typeBLongRootMatrix_def]
      rcases j₀ with ⟨j, hj⟩
      have hjn : j ≠ n := by omega
      have hnj : n ≠ j := hjn.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff, pow_two, Module.End.mul_apply] <;>
        omega
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp only [typeBSimpleNegativeRootMatrix_castSucc,
        typeBSimpleNegativeRootMatrix_last]
      simp_rw [typeBLongRootMatrix_def, typeBShortNegativeRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      have hin : i ≠ n := by omega
      have hni : n ≠ i := hin.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff] <;>
        omega
    · simp only [typeBSimpleNegativeRootMatrix_castSucc]
      simp_rw [typeBLongRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      rcases j₀ with ⟨j, hj⟩
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.transpose_apply, Matrix.of_apply]
      split_ifs <;> simp only [Fin.succ_mk, map_sub, Int.reduceNeg, neg_neg,
        Int.reduceToNat, Int.toNat_one, pow_one, neg_zero, Int.toNat_zero, pow_zero,
        lie_sub, sub_lie, lie_single_single, Sum.inr.injEq, Sum.inl.injEq,
        Fin.mk.injEq, mul_one, reduceCtorEq, ↓reduceIte, sub_self, sub_zero, zero_sub,
        neg_sub, LinearMap.sub_apply, LieAlgebra.ad_apply, Module.End.one_apply] <;>
        (first | omega | split_ifs) <;>
        try simp only [lie_zero, lie_single_single, Sum.inr.injEq, Sum.inl.injEq,
          Fin.mk.injEq, mul_one, Nat.add_eq_left, one_ne_zero, ↓reduceIte, sub_zero,
          zero_sub, reduceCtorEq, sub_self, Nat.left_eq_add, sub_neg_eq_add, zero_add] <;>
        simp only [Fin.ext_iff] at * <;>
        (first | omega | (split_ifs; simp))
      all_goals omega

end TauCeti
