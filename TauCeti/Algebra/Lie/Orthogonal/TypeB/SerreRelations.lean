/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.GeneratorRelations
public import TauCeti.Algebra.Lie.Presentation.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.Presentation.Serre

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

* `TauCeti.typeBSimpleRootGenerator_lie_negative_of_ne`: distinct positive and negative
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
  have hij' : i.val ≠ j.val + 1 := by omega
  have hji' : j.val ≠ i.val + 1 := by omega
  simp only [typeBSimpleRootMatrix_castSucc]
  simp [typeBLongRootMatrix_def, lie_sub, sub_lie, lie_single_single,
    Fin.ext_iff, hij, hji, hij', hji']

private theorem lie_lie_typeBSimpleRootMatrix_castSucc_of_adjacent
    (i j : Fin n) (hij : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
      ⁅typeBSimpleRootMatrix (K := K) i.castSucc,
        typeBSimpleRootMatrix (K := K) j.castSucc⁆⁆ = 0 := by
  simp only [typeBSimpleRootMatrix_castSucc]
  rcases hij with hij | hji
  · have hne : i.val ≠ j.val := by omega
    have hne' : j.val ≠ i.val := hne.symm
    have hreverse : j.val + 1 ≠ i.val := by omega
    have hreverse' : i.val ≠ j.val + 1 := by omega
    simp [typeBLongRootMatrix_def, lie_sub, sub_lie, lie_single_single,
      Fin.ext_iff, hij, hne, hne', hreverse, hreverse']
  · have hreverse : i.val + 1 ≠ j.val := by omega
    have hreverse' : j.val ≠ i.val + 1 := by omega
    simp [typeBLongRootMatrix_def, lie_sub, sub_lie, lie_single_single,
      Fin.ext_iff, hji, hreverse, hreverse']

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
    · rcases i₀ with ⟨i, hi⟩
      rcases j₀ with ⟨j, hj⟩
      by_cases hij : i = j
      · subst j
        simp only [lie_self, map_zero]
      · by_cases hij' : i + 1 = j
        · have hpow :
              (-CartanMatrix.B (n + 1) (⟨j, hj⟩ : Fin n).castSucc
                (⟨i, hi⟩ : Fin n).castSucc).toNat = 1 := by
            simp [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
            omega
          rw [hpow, pow_one, LieAlgebra.ad_apply]
          exact lie_lie_typeBSimpleRootMatrix_castSucc_of_adjacent
            (K := K) ⟨i, hi⟩ ⟨j, hj⟩ (Or.inl hij')
        · by_cases hji' : j + 1 = i
          · have hpow :
                (-CartanMatrix.B (n + 1) (⟨j, hj⟩ : Fin n).castSucc
                  (⟨i, hi⟩ : Fin n).castSucc).toNat = 1 := by
              simp [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
              omega
            rw [hpow, pow_one, LieAlgebra.ad_apply]
            exact lie_lie_typeBSimpleRootMatrix_castSucc_of_adjacent
              (K := K) ⟨i, hi⟩ ⟨j, hj⟩ (Or.inr hji')
          · have hpow :
                (-CartanMatrix.B (n + 1) (⟨j, hj⟩ : Fin n).castSucc
                  (⟨i, hi⟩ : Fin n).castSucc).toNat = 0 := by
              simp [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
              omega
            rw [hpow, pow_zero, Module.End.one_apply]
            exact lie_typeBSimpleRootMatrix_castSucc_of_nonadjacent
              (K := K) ⟨i, hi⟩ ⟨j, hj⟩ hij' hji'

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
    simp [typeBSignReindex, typeBSignEquiv, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.submatrix_single_equiv, typeBShortRootMatrix_def,
      typeBShortNegativeRootMatrix_def]
  · simp only [typeBSimpleRootMatrix_castSucc, typeBSimpleNegativeRootMatrix_castSucc]
    simp [typeBSignReindex, typeBSignEquiv, Matrix.reindex_apply,
      Matrix.submatrix_sub, Matrix.submatrix_single_equiv, typeBLongRootMatrix_def]

private theorem ad_pow_lie_typeBSimpleNegativeRootMatrix (i j : Fin (n + 1)) :
    (ad K (Matrix (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1))
        (Unit ⊕ Fin (n + 1) ⊕ Fin (n + 1)) K)
        (typeBSimpleNegativeRootMatrix (K := K) i) ^
      (-CartanMatrix.B (n + 1) j i).toNat)
        ⁅typeBSimpleNegativeRootMatrix (K := K) i,
          typeBSimpleNegativeRootMatrix (K := K) j⁆ = 0 := by
  let e := typeBSignReindex (K := K) (Fin (n + 1))
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
