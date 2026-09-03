/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.GeneratorRelations
import TauCeti.Algebra.Lie.GeneralLinear.Basic
public import TauCeti.Algebra.Lie.Presentation.Serre

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

All results hold over an arbitrary commutative ring, including in characteristic two. Together
with the Cartan-action relations, they package the standard matrices as a
`TauCeti.IsSerreSystem`, the input for mapping the integral Kostant form into the standard
type-`B` representation.

## Main results

* `TauCeti.typeBSimpleRootGenerator_lie_negative_of_ne`: distinct positive and negative
  simple-root generators commute.
* `TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator`: the higher positive
  Serre relations.
* `TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator`: the
  higher negative Serre relations.
* `TauCeti.isSerreSystem_typeBSimpleRootGenerator`: the standard type-`B` generators form a Serre
  system for the transposed type-`B` Cartan matrix.

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
          rcases j₀ with ⟨j, hj⟩
          rw [typeBShortRootMatrix_lie_longRootMatrix]
          simp only [Fin.succ_mk, Fin.castSucc_mk, neg_eq_zero]
          split_ifs with h
          · simp only [Fin.ext_iff, Fin.val_last] at h
            omega
          · rfl
  | cast i₀ =>
      induction j using Fin.lastCases with
      | last =>
          simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_last]
          rcases i₀ with ⟨i, hi⟩
          calc
            ⁅typeBLongRootMatrix (K := K) (⟨i, hi⟩ : Fin n).castSucc
                (⟨i, hi⟩ : Fin n).succ (ne_of_lt Fin.castSucc_lt_succ),
                typeBShortNegativeRootMatrix (Fin.last n)⁆ =
                -⁅typeBShortNegativeRootMatrix (K := K) (Fin.last n),
                  typeBLongRootMatrix (⟨i, hi⟩ : Fin n).castSucc
                    (⟨i, hi⟩ : Fin n).succ (ne_of_lt Fin.castSucc_lt_succ)⁆ :=
                      (lie_skew _ _).symm
            _ = 0 := by
              rw [typeBShortNegativeRootMatrix_lie_longRootMatrix]
              simp only [neg_eq_zero]
              split_ifs with h
              · exact (hij h.symm).elim
              · rfl
      | cast j₀ =>
          have hij₀ : i₀ ≠ j₀ := fun h ↦ hij (congrArg Fin.castSucc h)
          simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_castSucc]
          apply typeBLongRootMatrix_lie_longRootMatrix_of_ne
          · intro h
            apply hij₀
            apply Fin.ext
            have hval := congrArg (fun x : Fin (n + 1) ↦ x.val) h
            simp only [Fin.val_succ] at hval
            omega
          · intro h
            apply hij₀
            apply Fin.ext
            exact congrArg (fun x : Fin (n + 1) ↦ x.val) h

/-- Positive and negative simple-root generators at distinct Bourbaki nodes commute. -/
@[simp]
theorem typeBSimpleRootGenerator_lie_negative_of_ne
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ⁅typeBSimpleRootGenerator (K := K) i, typeBSimpleNegativeRootGenerator (K := K) j⁆ = 0 := by
  apply Subtype.ext
  simpa only [coe_typeBSimpleRootGenerator, coe_typeBSimpleNegativeRootGenerator,
    LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using
      lie_typeBSimpleRootMatrix_typeBSimpleNegativeRootMatrix_of_ne (K := K) i j hij

private theorem lie_typeBSimpleRootMatrix_castSucc_of_nonadjacent
    (i j : Fin n) (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      typeBSimpleRootMatrix (K := K) j.castSucc⁆ = 0 := by
  simp only [typeBSimpleRootMatrix_castSucc]
  apply typeBLongRootMatrix_lie_longRootMatrix_of_ne
  · intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    exact hij hval
  · intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    exact hji hval.symm

private theorem lie_typeBSimpleRootMatrix_castSucc_of_adjacent
    (i j : Fin n) (hij : i.val + 1 = j.val) (hout : i.castSucc ≠ j.succ) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      typeBSimpleRootMatrix (K := K) j.castSucc⁆ =
        typeBLongRootMatrix i.castSucc j.succ hout := by
  simp only [typeBSimpleRootMatrix_castSucc]
  exact typeBLongRootMatrix_lie_longRootMatrix_chain (K := K)
    i.castSucc i.succ j.castSucc j.succ (ne_of_lt i.castSucc_lt_succ)
    (ne_of_lt j.castSucc_lt_succ) (Fin.ext hij) hout

private theorem lie_lie_typeBSimpleRootMatrix_castSucc (i j : Fin n) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
        typeBSimpleRootMatrix (K := K) j.castSucc⁆⁆ = 0 := by
  by_cases hij : i.val + 1 = j.val
  · have hout : i.castSucc ≠ j.succ := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hval
      omega
    rw [lie_typeBSimpleRootMatrix_castSucc_of_adjacent (K := K) i j hij hout]
    simp only [typeBSimpleRootMatrix_castSucc]
    apply typeBLongRootMatrix_lie_longRootMatrix_of_ne
    · intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hval
      omega
    · exact hout
  · by_cases hji : j.val + 1 = i.val
    · have hout : j.castSucc ≠ i.succ := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        omega
      have hinner :
          ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
            typeBSimpleRootMatrix (K := K) j.castSucc⁆ =
              -typeBLongRootMatrix j.castSucc i.succ hout := by
        rw [← lie_typeBSimpleRootMatrix_castSucc_of_adjacent (K := K) j i hji hout]
        exact (lie_skew _ _).symm
      rw [hinner, lie_neg]
      simp only [typeBSimpleRootMatrix_castSucc, neg_eq_zero]
      apply typeBLongRootMatrix_lie_longRootMatrix_of_ne
      · intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_castSucc] at hval
        omega
      · exact ne_of_lt i.castSucc_lt_succ
    · rw [lie_typeBSimpleRootMatrix_castSucc_of_nonadjacent (K := K) i j hij hji,
        lie_zero]

private theorem neg_typeBCartan_castSucc_castSucc_toNat (i j : Fin n) :
    (-CartanMatrix.B (n + 1) j.castSucc i.castSucc).toNat =
      if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc]
  split_ifs <;> omega

private theorem neg_typeBCartan_last_castSucc_toNat (j : Fin n) :
    (-CartanMatrix.B (n + 1) j.castSucc (Fin.last n)).toNat =
      if j.val + 1 = n then 2 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_last]
  split_ifs <;> omega

private theorem neg_typeBCartan_castSucc_last_toNat (i : Fin n) :
    (-CartanMatrix.B (n + 1) (Fin.last n) i.castSucc).toNat =
      if i.val + 1 = n then 1 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_last]
  split_ifs <;> omega

private theorem lie_typeBSimpleRootMatrix_last_castSucc_of_nonadjacent
    (j : Fin n) (hj : j.val + 1 ≠ n) :
    ⁅typeBSimpleRootMatrix (K := K) (Fin.last n),
      typeBSimpleRootMatrix (K := K) j.castSucc⁆ = 0 := by
  simp only [typeBSimpleRootMatrix_last, typeBSimpleRootMatrix_castSucc]
  rw [typeBShortRootMatrix_lie_longRootMatrix]
  simp only [neg_eq_zero]
  split_ifs with h
  · have hval := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_succ] at hval
    exact (hj hval.symm).elim
  · rfl

private theorem lie_typeBSimpleRootMatrix_castSucc_last_of_nonadjacent
    (i : Fin n) (hi : i.val + 1 ≠ n) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      typeBSimpleRootMatrix (K := K) (Fin.last n)⁆ = 0 := by
  calc
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
        typeBSimpleRootMatrix (K := K) (Fin.last n)⁆ =
        -⁅typeBSimpleRootMatrix (K := K) (Fin.last n),
          typeBSimpleRootMatrix (K := K) i.castSucc⁆ := (lie_skew _ _).symm
    _ = 0 := neg_eq_zero.mpr
      (lie_typeBSimpleRootMatrix_last_castSucc_of_nonadjacent (K := K) i hi)

private theorem ad_sq_lie_typeBSimpleRootMatrix_last_castSucc
    (j : Fin n) (hj : j.val + 1 = n) :
    (ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
        (typeBSimpleRootMatrix (K := K) (Fin.last n)) ^ 2)
      ⁅typeBSimpleRootMatrix (K := K) (Fin.last n),
        typeBSimpleRootMatrix (K := K) j.castSucc⁆ = 0 := by
  simp only [pow_two, Module.End.mul_apply, LieAlgebra.ad_apply,
    typeBSimpleRootMatrix_last, typeBSimpleRootMatrix_castSucc]
  rw [typeBShortRootMatrix_lie_longRootMatrix]
  have hlast : Fin.last n = j.succ := Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
  rw [ite_eq_left hlast]
  simp only [lie_neg, neg_eq_zero]
  simp [typeBShortRootMatrix_def, lie_sub, sub_lie, lie_single_single]

private theorem lie_lie_typeBSimpleRootMatrix_castSucc_last
    (i : Fin n) (hi : i.val + 1 = n) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
        typeBSimpleRootMatrix (K := K) (Fin.last n)⁆⁆ = 0 := by
  have hlast : Fin.last n = i.succ := Fin.ext (by simp only [Fin.val_last, Fin.val_succ]; omega)
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  have hinner :
      ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
        typeBSimpleRootMatrix (K := K) (Fin.last n)⁆ =
          typeBShortRootMatrix i.castSucc := by
    simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleRootMatrix_last]
    calc
      ⁅typeBLongRootMatrix (K := K) i.castSucc i.succ hne,
          typeBShortRootMatrix (Fin.last n)⁆ =
          -⁅typeBShortRootMatrix (K := K) (Fin.last n),
            typeBLongRootMatrix i.castSucc i.succ hne⁆ := (lie_skew _ _).symm
      _ = typeBShortRootMatrix i.castSucc := by
        rw [typeBShortRootMatrix_lie_longRootMatrix, ite_eq_left hlast]
        simp
  rw [hinner]
  simp only [typeBSimpleRootMatrix_castSucc]
  calc
    ⁅typeBLongRootMatrix (K := K) i.castSucc i.succ hne,
        typeBShortRootMatrix i.castSucc⁆ =
        -⁅typeBShortRootMatrix (K := K) i.castSucc,
          typeBLongRootMatrix i.castSucc i.succ hne⁆ := (lie_skew _ _).symm
    _ = 0 := by rw [typeBShortRootMatrix_lie_longRootMatrix]; simp [hne]

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
    · rw [neg_typeBCartan_last_castSucc_toNat]
      by_cases hj : j₀.val + 1 = n
      · rw [ite_eq_left hj]
        exact ad_sq_lie_typeBSimpleRootMatrix_last_castSucc (K := K) j₀ hj
      · rw [ite_eq_right hj, pow_zero, Module.End.one_apply]
        exact lie_typeBSimpleRootMatrix_last_castSucc_of_nonadjacent (K := K) j₀ hj
  · refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
    · rw [neg_typeBCartan_castSucc_last_toNat]
      by_cases hi : i₀.val + 1 = n
      · rw [ite_eq_left hi, pow_one, LieAlgebra.ad_apply]
        exact lie_lie_typeBSimpleRootMatrix_castSucc_last (K := K) i₀ hi
      · rw [ite_eq_right hi, pow_zero, Module.End.one_apply]
        exact lie_typeBSimpleRootMatrix_castSucc_last_of_nonadjacent (K := K) i₀ hi
    · rw [neg_typeBCartan_castSucc_castSucc_toNat]
      by_cases hij : i₀.val + 1 = j₀.val ∨ j₀.val + 1 = i₀.val
      · rw [ite_eq_left hij, pow_one, LieAlgebra.ad_apply]
        exact lie_lie_typeBSimpleRootMatrix_castSucc (K := K) i₀ j₀
      · rw [ite_eq_right hij, pow_zero, Module.End.one_apply]
        exact lie_typeBSimpleRootMatrix_castSucc_of_nonadjacent (K := K) i₀ j₀
          (not_or.mp hij).1 (not_or.mp hij).2

/-- The coordinate equivalence that fixes the middle coordinate and swaps the signed blocks. -/
private def typeBSignEquiv (ι : Type*) : Unit ⊕ ι ⊕ ι ≃ Unit ⊕ ι ⊕ ι :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumComm ι ι)

private theorem typeBSignReindex_typeBSimpleRootMatrix (i : Fin (n + 1)) :
    Matrix.reindexLieEquiv (R := K) (typeBSignEquiv (Fin (n + 1)))
        (typeBSimpleRootMatrix (K := K) i) = -typeBSimpleNegativeRootMatrix (K := K) i := by
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · simp only [typeBSimpleRootMatrix_last, typeBSimpleNegativeRootMatrix_last]
    simp [typeBSignEquiv, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.submatrix_single_equiv, typeBShortRootMatrix_def,
      typeBShortNegativeRootMatrix_def]
  · simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_castSucc]
    simp [typeBSignEquiv, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.submatrix_single_equiv, typeBLongRootMatrix_def]

private theorem ad_pow_lie_typeBSimpleNegativeRootMatrix (i j : Fin (n + 1)) :
    (ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
        (typeBSimpleNegativeRootMatrix (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleNegativeRootMatrix (K := K) i,
          typeBSimpleNegativeRootMatrix (K := K) j⁆ = 0 := by
  let e := Matrix.reindexLieEquiv (R := K) (typeBSignEquiv (Fin (n + 1)))
  have h := congrArg e.toLieHom (ad_pow_lie_typeBSimpleRootMatrix (K := K) i j)
  have he (k : Fin (n + 1)) :
      e.toLieHom (typeBSimpleRootMatrix (K := K) k) =
        -typeBSimpleNegativeRootMatrix (K := K) k := by
    simpa only [LieEquiv.coe_toLieHom, e] using
      typeBSignReindex_typeBSimpleRootMatrix (K := K) k
  rw [map_zero, LieHom.map_ad_pow, LieHom.map_lie,
    he i, he j] at h
  simp only [neg_lie, lie_neg, neg_neg] at h
  simpa only [neg_neg] using ad_neg_pow_apply_eq_zero h

/-- The higher Serre relation for the positive simple-root generators of the standard split
type-`B` Lie algebra. -/
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

/-- The standard type-`B` Chevalley generators satisfy the Serre relations for the transposed
type-`B` Cartan matrix, in the convention used by `IsSerreSystem`. -/
theorem isSerreSystem_typeBSimpleRootGenerator :
    IsSerreSystem K (CartanMatrix.B (n + 1))ᵀ
      (typeBSimpleCorootGenerator (K := K))
      (typeBSimpleRootGenerator (K := K))
      (typeBSimpleNegativeRootGenerator (K := K)) where
  lie_H_H := typeBSimpleCorootGenerator_lie_eq_zero
  lie_E_F_self := typeBSimpleRootGenerator_lie_negative
  lie_E_F_of_ne := typeBSimpleRootGenerator_lie_negative_of_ne
  lie_H_E i j := by
    simpa only [Matrix.transpose_apply] using typeBSimpleCorootGenerator_lie_root (K := K) i j
  lie_H_F i j := by
    simpa only [Matrix.transpose_apply] using
      typeBSimpleCorootGenerator_lie_negativeRoot (K := K) i j
  ad_pow_lie_E_E i j := by
    simpa only [Matrix.transpose_apply] using
      ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator (K := K) i j
  ad_pow_lie_F_F i j := by
    simpa only [Matrix.transpose_apply] using
      ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator (K := K) i j

end TauCeti
