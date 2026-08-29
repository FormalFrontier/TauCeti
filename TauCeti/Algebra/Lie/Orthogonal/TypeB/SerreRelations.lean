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
  generators, vanish with the exponents prescribed by the type-`B` Cartan matrix.

The reversed matrix indices encode the convention used by the existing Cartan-action API: the
coroot index is the first index in `⁅hᵢ, eⱼ⁆`. All results hold over an arbitrary commutative
ring, including in characteristic two. Together with the Cartan-action relations, these are the
inputs for packaging
the standard matrices as a `TauCeti.IsSerreSystem` and hence for mapping the integral Kostant form
into the standard type-`B` representation.

## Main results

* `TauCeti.typeBSimpleRootGenerator_lie_negativeRoot_of_ne`: distinct positive and negative
  simple-root generators commute.
* `TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator`: the higher positive
  Serre relations.
* `TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator`: the
  higher negative Serre relations.

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

/- The four `Fin.lastCases` branches separate ordinary long-root nodes from the terminal short-root
node. Only the positive orientation is computed: the sign-reindexing below transports it to the
negative orientation. -/
private theorem ad_pow_lie_typeBSimpleRootMatrix (i j : Fin (n + 1)) :
    (ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
        (typeBSimpleRootMatrix (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleRootMatrix (K := K) i, typeBSimpleRootMatrix (K := K) j⁆ = 0 := by
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp
    · simp only [typeBSimpleRootMatrix_last, typeBSimpleRootMatrix_castSucc]
      simp_rw [typeBShortRootMatrix_def, typeBLongRootMatrix_def]
      rcases j₀ with ⟨j, hj⟩
      have hjn : j ≠ n := by omega
      have hnj : n ≠ j := hjn.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff, pow_two, Module.End.mul_apply] <;>
        omega
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleRootMatrix_last]
      simp_rw [typeBLongRootMatrix_def, typeBShortRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      have hin : i ≠ n := by omega
      have hni : n ≠ i := hin.symm
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.of_apply]
      split_ifs <;> simp_all [LieAlgebra.ad_apply, lie_sub, sub_lie,
        lie_single_single, Fin.ext_iff] <;>
        omega
    · simp only [typeBSimpleRootMatrix_castSucc]
      simp_rw [typeBLongRootMatrix_def]
      rcases i₀ with ⟨i, hi⟩
      rcases j₀ with ⟨j, hj⟩
      simp only [Fin.castSucc_mk, CartanMatrix.B, Matrix.of_apply]
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

/-- The coordinate equivalence that fixes the middle coordinate and swaps the signed blocks. -/
private def typeBSignEquiv (ι : Type*) : Unit ⊕ ι ⊕ ι ≃ Unit ⊕ ι ⊕ ι :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumComm ι ι)

/-- Reindexing matrices along `typeBSignEquiv`, as an equivalence of Lie algebras. -/
private def typeBSignReindex (ι : Type*) [DecidableEq ι] [Fintype ι] :
    Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K ≃ₗ⁅K⁆
      Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K :=
  (Matrix.reindexAlgEquiv K K (typeBSignEquiv ι)).toLieEquiv

private theorem typeBSignReindex_typeBSimpleRootMatrix (i : Fin (n + 1)) :
    typeBSignReindex (K := K) (Fin (n + 1)) (typeBSimpleRootMatrix (K := K) i) =
      -typeBSimpleNegativeRootMatrix (K := K) i := by
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · simp only [typeBSimpleRootMatrix_last, typeBSimpleNegativeRootMatrix_last]
    ext (a | (a | a)) (b | (b | b)) <;>
      simp [typeBSignReindex, typeBSignEquiv, Matrix.reindex_apply,
        typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def, Matrix.single_apply]
  · simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_castSucc]
    ext (a | (a | a)) (b | (b | b)) <;>
      simp [typeBSignReindex, typeBSignEquiv, Matrix.reindex_apply,
        typeBLongRootMatrix_def, Matrix.single_apply]

private theorem lieEquiv_map_ad_pow {L L' : Type*} [LieRing L] [LieAlgebra K L]
    [LieRing L'] [LieAlgebra K L'] (e : L ≃ₗ⁅K⁆ L') (x y : L) (m : ℕ) :
    e (((ad K L x) ^ m) y) = ((ad K L' (e x)) ^ m) (e y) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, e.map_lie, ih,
        pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]

private theorem ad_pow_lie_typeBSimpleNegativeRootMatrix (i j : Fin (n + 1)) :
    (ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
        (typeBSimpleNegativeRootMatrix (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleNegativeRootMatrix (K := K) i,
          typeBSimpleNegativeRootMatrix (K := K) j⁆ = 0 := by
  let e := typeBSignReindex (K := K) (Fin (n + 1))
  have h := congrArg e (ad_pow_lie_typeBSimpleRootMatrix (K := K) i j)
  rw [map_zero, lieEquiv_map_ad_pow, e.map_lie,
    typeBSignReindex_typeBSimpleRootMatrix,
    typeBSignReindex_typeBSimpleRootMatrix] at h
  simp only [neg_lie, lie_neg, neg_neg] at h
  have had :
      ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
          (-typeBSimpleNegativeRootMatrix (K := K) i) =
        -ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
          (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
            (typeBSimpleNegativeRootMatrix (K := K) i) := by
    exact map_neg (ad K _) _
  rw [had] at h
  rcases Nat.even_or_odd (-CartanMatrix.B (n + 1) j i).toNat with he | ho
  · simpa only [he.neg_pow] using h
  · simpa only [ho.neg_pow, LinearMap.neg_apply, neg_eq_zero] using h

/-- The higher Serre relation for the positive simple-root generators of the standard split
type-`B` Lie algebra. The reversed Cartan-matrix indices match the coroot-first convention in the
Cartan-action relations. -/
@[simp]
theorem ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator
    (i j : Fin (n + 1)) :
    (ad K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (typeBSimpleRootGenerator (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleRootGenerator (K := K) i, typeBSimpleRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket,
    coe_typeBSimpleRootGenerator, coe_typeBSimpleRootGenerator]
  simp only [ZeroMemClass.coe_zero]
  exact ad_pow_lie_typeBSimpleRootMatrix i j

/-- The higher Serre relation for the negative simple-root generators of the standard split
type-`B` Lie algebra. -/
@[simp]
theorem ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
    (i j : Fin (n + 1)) :
    (ad K (LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K)
        (typeBSimpleNegativeRootGenerator (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleNegativeRootGenerator (K := K) i,
          typeBSimpleNegativeRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_ad_pow, LieSubalgebra.coe_bracket,
    coe_typeBSimpleNegativeRootGenerator, coe_typeBSimpleNegativeRootGenerator]
  simp only [ZeroMemClass.coe_zero]
  exact ad_pow_lie_typeBSimpleNegativeRootMatrix i j

end TauCeti
