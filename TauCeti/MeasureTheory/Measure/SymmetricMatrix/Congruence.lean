/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Congruence and the change of variables on the symmetric subspace

For an invertible matrix `C`, the congruence `A ↦ C * A * Cᵀ` is a continuous linear
automorphism of the symmetric subspace. In the upper-triangular coordinates its determinant is
`(det C) ^ (p + 1)`, so the congruence image of a set has `|det C| ^ (p + 1)` times its
`TauCeti.symmetricLebesgue` volume, and the pushforward of `symmetricLebesgue` is
`(|det C| ^ (p + 1))⁻¹ • symmetricLebesgue`. This change of variables supplies the
general-scale Wishart formulas.

The determinant is computed for an arbitrary square matrix `M`, not only invertible ones: the
map `M ↦ det (A ↦ M * A * Mᵀ)` is multiplicative, so by the transvection decomposition it
suffices to treat triangular `M`, covering both transvections and diagonal matrices. For
triangular `M`, the coordinate matrix is triangular for the ranking `p * i + j` of the
on-or-above-diagonal positions, with diagonal entries `M i i * M j j` over `i ≤ j`, whose
product is `(det M) ^ (p + 1)`.

## Main declarations

* `TauCeti.symmetricCongruenceLinearMap` — congruence by an arbitrary square matrix, as a
  linear endomorphism of the symmetric subspace.
* `TauCeti.det_symmetricCongruenceLinearMap` — its determinant is `(det M) ^ (p + 1)`.
* `TauCeti.symmetricCongruence` — congruence by an invertible matrix, as a continuous linear
  automorphism.
* `TauCeti.map_symmetricCongruence_symmetricLebesgue` — the induced change of variables for
  `symmetricLebesgue`.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open MeasureTheory Matrix Module

namespace TauCeti

variable {p : ℕ}

/-- Congruence `A ↦ M * A * Mᵀ` by an arbitrary square matrix, as a linear endomorphism of the
symmetric subspace. -/
@[expose]
def symmetricCongruenceLinearMap (M : Matrix (Fin p) (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) where
  toFun A :=
    ⟨M * (A : Matrix (Fin p) (Fin p) ℝ) * Mᵀ, by
      have h := Matrix.isHermitian_mul_mul_conjTranspose M (isHermitian_coe A)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h⟩
  map_add' A B := by
    refine Subtype.ext ?_
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    refine Subtype.ext ?_
    simp

@[simp]
theorem coe_symmetricCongruenceLinearMap_apply (M : Matrix (Fin p) (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricCongruenceLinearMap M A : Matrix (Fin p) (Fin p) ℝ) =
      M * (A : Matrix (Fin p) (Fin p) ℝ) * Mᵀ :=
  rfl

theorem symmetricCongruenceLinearMap_mul (M N : Matrix (Fin p) (Fin p) ℝ) :
    symmetricCongruenceLinearMap (M * N) =
      (symmetricCongruenceLinearMap M).comp (symmetricCongruenceLinearMap N) := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

@[simp]
theorem symmetricCongruenceLinearMap_one :
    symmetricCongruenceLinearMap (1 : Matrix (Fin p) (Fin p) ℝ) = LinearMap.id := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp

/-! ### The determinant of congruence -/

/-- A matrix that is block triangular for an injective integer ranking of the indices has
determinant the product of its diagonal entries: an injective ranking cuts it into singleton
blocks. -/
private theorem det_eq_prod_diag_of_blockTriangular {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : Matrix ι ι ℝ} {f : ι → ℕ} (hf : Function.Injective f) (h : N.BlockTriangular f) :
    N.det = ∏ i, N i i := by
  rw [h.det, Finset.prod_image fun x _ y _ hxy => hf hxy]
  refine Finset.prod_congr rfl fun i _ => ?_
  let _ : Unique {j // f j = f i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext (hf j.2)⟩
  exact Matrix.det_unique _

/-- Counting how often each index occurs in an on-or-above-diagonal pair: the index `i` occurs
`p - i` times as the first entry and `i + 1` times as the second, so `p + 1` times in all. -/
private theorem prod_upperTriangle_mul (d : Fin p → ℝ) :
    ∏ c : upperTriangle p, d c.1.1 * d c.1.2 = (∏ i, d i) ^ (p + 1) := by
  have key : ∏ c : upperTriangle p, d c.1.1 * d c.1.2 =
      ∏ i : Fin p, ∏ j ∈ Finset.Ici i, d i * d j := by
    rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin p × Fin p => ij.1 ≤ ij.2)
      (by simp) fun ij => d ij.1 * d ij.2]
    exact Finset.prod_finset_product'
      (Finset.univ.filter fun ij : Fin p × Fin p => ij.1 ≤ ij.2) Finset.univ
      (fun i => Finset.Ici i) (by simp) (f := fun i j => d i * d j)
  rw [key]
  have hsplit : ∀ i : Fin p, ∏ j ∈ Finset.Ici i, d i * d j =
      d i ^ (Finset.Ici i).card * ∏ j ∈ Finset.Ici i, d j := by
    intro i
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_congr rfl fun i _ => hsplit i, Finset.prod_mul_distrib]
  have hswap : ∏ i : Fin p, ∏ j ∈ Finset.Ici i, d j =
      ∏ j : Fin p, d j ^ (Finset.Iic j).card := by
    rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j : Fin p => Finset.Iic j) (by simp)]
    exact Finset.prod_congr rfl fun j _ => Finset.prod_const _
  rw [hswap, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, Fin.card_Ici, Fin.card_Iic]
  have := i.isLt
  congr 1
  omega

private theorem symmetricBasis_repr (p : ℕ)
    (x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (r : upperTriangle p) :
    (symmetricBasis p).repr x r = (x : Matrix (Fin p) (Fin p) ℝ) r.1.1 r.1.2 := by
  simp [symmetricBasis]

/-- The coordinate basis vector at an on-or-above-diagonal pair is the matrix with a single one
there, symmetrized off the diagonal. -/
private theorem coe_symmetricBasis_eq_single_add (p : ℕ) (c : upperTriangle p) :
    ((symmetricBasis p c : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) =
      Matrix.single c.1.1 c.1.2 1 +
        (if c.1.1 = c.1.2 then 0 else Matrix.single c.1.2 c.1.1 1) := by
  obtain ⟨⟨i, j⟩, hij⟩ := c
  by_cases hd : i = j
  · subst hd
    rw [ite_eq_left rfl, add_zero]
    exact coe_symmetricBasis_diag p i
  · rw [ite_eq_right hd]
    exact coe_symmetricBasis_offDiag p hij hd

private theorem mul_single_mul_transpose_apply (M : Matrix (Fin p) (Fin p) ℝ) (a b i j : Fin p) :
    (M * Matrix.single a b (1 : ℝ) * Mᵀ) i j = M i a * M j b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- The coordinate matrix of congruence by `M`: the entry at the pair of positions `r` and `c`
records how the input entry at `c` (and its mirror image) contributes to the output entry
at `r`. -/
private theorem toMatrix_symmetricCongruenceLinearMap (M : Matrix (Fin p) (Fin p) ℝ)
    (r c : upperTriangle p) :
    LinearMap.toMatrix (symmetricBasis p) (symmetricBasis p)
        (symmetricCongruenceLinearMap M) r c =
      M r.1.1 c.1.1 * M r.1.2 c.1.2 +
        (if c.1.1 = c.1.2 then 0 else M r.1.1 c.1.2 * M r.1.2 c.1.1) := by
  rw [LinearMap.toMatrix_apply, symmetricBasis_repr, coe_symmetricCongruenceLinearMap_apply,
    coe_symmetricBasis_eq_single_add]
  by_cases hd : c.1.1 = c.1.2
  · rw [ite_eq_left hd, ite_eq_left hd, add_zero, add_zero, mul_single_mul_transpose_apply]
  · rw [ite_eq_right hd, ite_eq_right hd, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
      mul_single_mul_transpose_apply, mul_single_mul_transpose_apply]

/-- The coordinate positions are ranked by `p * i + j`. The ranking is injective, and it is
monotone for the componentwise order on positions, which is what makes the coordinate matrix of
a triangular congruence triangular. -/
private theorem injective_upperRank (p : ℕ) :
    Function.Injective fun c : upperTriangle p => p * c.1.1.1 + c.1.2.1 := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ heq
  have heq' : p * i.1 + j.1 = p * i'.1 + j'.1 := heq
  have hj := j.isLt
  have hj' := j'.isLt
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le _) hj
  have hi : i.1 = i'.1 := by
    have h := congrArg (· / p) heq'
    simpa [Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj'] using h
  have hj2 : j.1 = j'.1 := by
    have h := congrArg (· % p) heq'
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] using h
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  exact ⟨Fin.ext hi, Fin.ext hj2⟩

/-- The entries of `M` making up a coordinate of the congruence matrix: if the nonzero entries of
`M` all sit weakly above the diagonal, then the first product being nonzero, or the entry
`M r.1.2 c.1.1` from the second product being nonzero, forces the output position `r` to lie
weakly below the input position `c` in both components. In the second case this uses that both
pairs are ordered, `r.1.1 ≤ r.1.2` and `c.1.1 ≤ c.1.2`. -/
private theorem le_of_congruence_products_ne_zero {M : Matrix (Fin p) (Fin p) ℝ}
    (hle : ∀ i j : Fin p, M i j ≠ 0 → i ≤ j) {r c : upperTriangle p}
    (h : M r.1.1 c.1.1 * M r.1.2 c.1.2 ≠ 0 ∨ M r.1.2 c.1.1 ≠ 0) :
    r.1.1 ≤ c.1.1 ∧ r.1.2 ≤ c.1.2 := by
  rcases h with h | h
  · exact ⟨hle _ _ (left_ne_zero_of_mul h), hle _ _ (right_ne_zero_of_mul h)⟩
  · have h2 : r.1.2 ≤ c.1.1 := hle _ _ h
    exact ⟨r.2.trans h2, h2.trans c.2⟩

/-- If a coordinate of the congruence matrix is nonzero, then so is one of the two entry products
making it up. -/
private theorem ne_zero_or_ne_zero_of_add_ite_ne_zero {x y : ℝ} {P : Prop} [Decidable P]
    (h : x + (if P then 0 else y) ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  by_contra hcon
  rw [not_or, not_ne_iff, not_ne_iff] at hcon
  rw [hcon.1, hcon.2, ite_self, add_zero] at h
  exact h rfl

/-- The determinant of a coordinate matrix that is triangular for the ranking of positions and
carries the products `d i * d j` on its diagonal. -/
private theorem det_eq_of_blockTriangular_upperRank
    {N : Matrix (upperTriangle p) (upperTriangle p) ℝ} (d : Fin p → ℝ)
    (hN : N.BlockTriangular fun c : upperTriangle p => p * c.1.1.1 + c.1.2.1)
    (hdiag : ∀ r : upperTriangle p, N r r = d r.1.1 * d r.1.2) :
    N.det = (∏ i, d i) ^ (p + 1) := by
  rw [det_eq_prod_diag_of_blockTriangular (injective_upperRank p) hN,
    Finset.prod_congr rfl fun r _ => hdiag r, prod_upperTriangle_mul d]

/-- For a triangular `M` the coordinate matrix of the congruence is triangular for the ranking of
positions, with diagonal entries `M i i * M j j` over the positions `i ≤ j`. Multiplying those out
gives `(∏ i, M i i) ^ (p + 1)`, which is `(det M) ^ (p + 1)`. -/
private theorem det_symmetricCongruenceLinearMap_of_isUpperTriangular
    (M : Matrix (Fin p) (Fin p) ℝ) (hM : M.IsUpperTriangular) :
    LinearMap.det (symmetricCongruenceLinearMap M) = M.det ^ (p + 1) := by
  have hle : ∀ i j : Fin p, M i j ≠ 0 → i ≤ j := fun _ _ h => not_lt.1 fun hlt => h (hM hlt)
  rw [← LinearMap.det_toMatrix (symmetricBasis p), Matrix.det_of_isUpperTriangular hM]
  refine det_eq_of_blockTriangular_upperRank (fun i => M i i) (fun r c hlt => ?_) fun r => ?_
  · by_contra hne
    rw [toMatrix_symmetricCongruenceLinearMap] at hne
    obtain ⟨h1, h2⟩ := le_of_congruence_products_ne_zero hle
      ((ne_zero_or_ne_zero_of_add_ite_ne_zero hne).imp_right right_ne_zero_of_mul)
    exact absurd (Nat.add_le_add (Nat.mul_le_mul_left p h1) h2) (not_le.2 hlt)
  · rw [toMatrix_symmetricCongruenceLinearMap]
    by_cases hd : r.1.1 = r.1.2
    · rw [ite_eq_left hd, add_zero]
    · rw [ite_eq_right hd, hM (lt_of_le_of_ne r.2 hd), mul_zero, add_zero]

/-- The lower-triangular counterpart: now the transposed coordinate matrix is the triangular one
for the same ranking of positions, and it has the same diagonal. -/
private theorem det_symmetricCongruenceLinearMap_of_isLowerTriangular
    (M : Matrix (Fin p) (Fin p) ℝ) (hM : M.IsLowerTriangular) :
    LinearMap.det (symmetricCongruenceLinearMap M) = M.det ^ (p + 1) := by
  have hle : ∀ i j : Fin p, Mᵀ i j ≠ 0 → i ≤ j := fun _ _ h =>
    not_lt.1 fun hlt => h (by rw [Matrix.transpose_apply, hM hlt])
  rw [← LinearMap.det_toMatrix (symmetricBasis p), ← Matrix.det_transpose,
    Matrix.det_of_isLowerTriangular M hM]
  refine det_eq_of_blockTriangular_upperRank (fun i => M i i) (fun r c hlt => ?_) fun r => ?_
  · by_contra hne
    rw [Matrix.transpose_apply, toMatrix_symmetricCongruenceLinearMap] at hne
    obtain ⟨h1, h2⟩ := le_of_congruence_products_ne_zero hle
      ((ne_zero_or_ne_zero_of_add_ite_ne_zero hne).imp_right left_ne_zero_of_mul)
    exact absurd (Nat.add_le_add (Nat.mul_le_mul_left p h1) h2) (not_le.2 hlt)
  · rw [Matrix.transpose_apply, toMatrix_symmetricCongruenceLinearMap]
    by_cases hd : r.1.1 = r.1.2
    · rw [ite_eq_left hd, add_zero]
    · rw [ite_eq_right hd, hM (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_ne r.2 hd)), zero_mul,
        add_zero]

private theorem det_symmetricCongruenceLinearMap_mul {A B : Matrix (Fin p) (Fin p) ℝ}
    (hA : LinearMap.det (symmetricCongruenceLinearMap A) = A.det ^ (p + 1))
    (hB : LinearMap.det (symmetricCongruenceLinearMap B) = B.det ^ (p + 1)) :
    LinearMap.det (symmetricCongruenceLinearMap (A * B)) = (A * B).det ^ (p + 1) := by
  rw [symmetricCongruenceLinearMap_mul, LinearMap.det_comp, hA, hB, Matrix.det_mul, mul_pow]

private theorem det_symmetricCongruenceLinearMap_transvection
    (t : Matrix.TransvectionStruct (Fin p) ℝ) :
    LinearMap.det (symmetricCongruenceLinearMap t.toMatrix) = t.toMatrix.det ^ (p + 1) := by
  have hentry : ∀ a b : Fin p, a ≠ b → ¬(t.i = a ∧ t.j = b) → t.toMatrix a b = 0 := by
    intro a b hab hne
    change ((1 : Matrix (Fin p) (Fin p) ℝ) + Matrix.single t.i t.j t.c) a b = 0
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, ite_eq_right hne, add_zero]
  rcases lt_or_gt_of_ne t.hij with h | h
  · refine det_symmetricCongruenceLinearMap_of_isUpperTriangular _ fun a b hab => ?_
    refine hentry a b (ne_of_gt hab) ?_
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hab.le)
  · refine det_symmetricCongruenceLinearMap_of_isLowerTriangular _ fun a b hab => ?_
    refine hentry a b (ne_of_lt hab) ?_
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hab.le)

private theorem det_symmetricCongruenceLinearMap_listProd
    (L : List (Matrix.TransvectionStruct (Fin p) ℝ)) :
    LinearMap.det
        (symmetricCongruenceLinearMap (L.map Matrix.TransvectionStruct.toMatrix).prod) =
      (L.map Matrix.TransvectionStruct.toMatrix).prod.det ^ (p + 1) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    exact det_symmetricCongruenceLinearMap_mul
      (det_symmetricCongruenceLinearMap_transvection t) ih

/-- The determinant of congruence by `M` on the symmetric subspace is `(det M) ^ (p + 1)`. -/
theorem det_symmetricCongruenceLinearMap (M : Matrix (Fin p) (Fin p) ℝ) :
    LinearMap.det (symmetricCongruenceLinearMap M) = M.det ^ (p + 1) := by
  obtain ⟨L, L', D, rfl⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  refine det_symmetricCongruenceLinearMap_mul
    (det_symmetricCongruenceLinearMap_mul (det_symmetricCongruenceLinearMap_listProd L) ?_)
    (det_symmetricCongruenceLinearMap_listProd L')
  exact det_symmetricCongruenceLinearMap_of_isUpperTriangular _ fun _ _ h =>
    Matrix.diagonal_apply_ne D (ne_of_gt h)

/-! ### Congruence by an invertible matrix -/

/-- Congruence `A ↦ C * A * Cᵀ` by an invertible matrix, as a continuous linear automorphism
of the symmetric subspace. -/
@[expose]
def symmetricCongruence (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃L[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (symmetricCongruenceLinearMap (C : Matrix (Fin p) (Fin p) ℝ))
      (symmetricCongruenceLinearMap ((C⁻¹ : Matrix.GeneralLinearGroup (Fin p) ℝ) :
        Matrix (Fin p) (Fin p) ℝ))
      (by rw [← symmetricCongruenceLinearMap_mul, C.mul_inv, symmetricCongruenceLinearMap_one])
      (by rw [← symmetricCongruenceLinearMap_mul, C.inv_mul, symmetricCongruenceLinearMap_one]))

@[simp]
theorem coe_symmetricCongruence_apply (C : Matrix.GeneralLinearGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricCongruence C A : Matrix (Fin p) (Fin p) ℝ) =
      (C : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ) *
        (C : Matrix (Fin p) (Fin p) ℝ)ᵀ :=
  rfl

@[simp]
theorem symmetricCongruence_toLinearMap (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    ((symmetricCongruence C).toLinearMap :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _) =
      symmetricCongruenceLinearMap (C : Matrix (Fin p) (Fin p) ℝ) :=
  rfl

/-- In the upper-triangular coordinates, congruence by `C` has determinant `(det C) ^ (p + 1)`. -/
theorem det_symmetricCongruence (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    LinearMap.det ((symmetricCongruence C).toLinearMap :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _) =
      Matrix.det (C : Matrix (Fin p) (Fin p) ℝ) ^ (p + 1) := by
  rw [symmetricCongruence_toLinearMap, det_symmetricCongruenceLinearMap]

/-- The pushforward of `symmetricLebesgue` under congruence by `C` is
`(|det C| ^ (p + 1))⁻¹ • symmetricLebesgue`; equivalently, the congruence image of a set has
`|det C| ^ (p + 1)` times its volume. This change of variables supplies the general-scale
Wishart formulas. -/
theorem map_symmetricCongruence_symmetricLebesgue (C : Matrix.GeneralLinearGroup (Fin p) ℝ) :
    (symmetricLebesgue p).map (symmetricCongruence C) =
      (ENNReal.ofReal |Matrix.det (C : Matrix (Fin p) (Fin p) ℝ)| ^ (p + 1))⁻¹ •
        symmetricLebesgue p := by
  have hC : (0 : ℝ) < |Matrix.det (C : Matrix (Fin p) (Fin p) ℝ)| :=
    abs_pos.2 (Matrix.GeneralLinearGroup.det_ne_zero C)
  have hdet : LinearMap.det ((symmetricCongruence C).toLinearMap :
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _) =
      Matrix.det (C : Matrix (Fin p) (Fin p) ℝ) ^ (p + 1) := det_symmetricCongruence C
  have hne : LinearMap.det ((symmetricCongruence C).toLinearMap :
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (Matrix.GeneralLinearGroup.det_ne_zero C)
  have h : (symmetricLebesgue p).map (symmetricCongruence C) =
      ENNReal.ofReal |(LinearMap.det ((symmetricCongruence C).toLinearMap :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _))⁻¹| • symmetricLebesgue p :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hne
  rw [h, hdet, abs_inv, abs_pow, ENNReal.ofReal_inv_of_pos (pow_pos hC _),
    ENNReal.ofReal_pow hC.le]

end TauCeti
