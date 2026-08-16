/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Smith normal form over `ℤ` with special linear transformations

Every square integer matrix with positive determinant can be brought to diagonal form with
positive diagonal entries in which each entry divides the next, using row and column
operations of determinant one:

* `Matrix.exists_smith_normal_form_of_det_pos`: for `A : Matrix (Fin n) (Fin n) ℤ` with
  `0 < A.det` there are `L R : SpecialLinearGroup (Fin n) ℤ` and a positive `d : Fin n → ℤ`,
  monotone under divisibility, with `L * A * R = diagonal d`.
* `Matrix.smith_normal_form_unique`: two nonnegative chained diagonals in the same
  `GL_n(ℤ)`-equivalence class are equal, so the invariant factors of `A` are well defined.

Mathlib's `Submodule.smithNormalForm` provides basis-level diagonalization over a PID; this
file supplies the matrix-level statement over `ℤ`, refined in three ways that the basis-level
result does not give: the transforming matrices have determinant `1` (not merely unit
determinant), the diagonal entries are positive, and successive entries divide each other
(the invariant-factor chain).  The proof first diagonalises using the basis-level theorem,
corrects signs, and then establishes the divisibility chain by repeated Bézout pivot steps
on `2 × 2` blocks.

This is the elementary divisor theorem in the form needed for the theory of Hecke rings of
`GL_n`: it produces the diagonal double coset representatives of Shimura, chapter 3.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck) — the pure-matrix half of that file; the Hecke-theoretic half is ported
separately on top of the arithmetic Hecke triple.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2
-/

public section

namespace Matrix

variable {n : ℕ}

/-! ## Diagonalisation with special linear transformations -/

private lemma mulVecLin_injective_of_det_ne_zero (A : Matrix (Fin n) (Fin n) ℤ)
    (hdet : A.det ≠ 0) : Function.Injective A.mulVecLin := fun x y h ↦
  mulVec_injective_of_det_ne_zero hdet (by simpa using h)

private lemma finrank_range_mulVecLin (A : Matrix (Fin n) (Fin n) ℤ) (hdet : A.det ≠ 0) :
    Module.finrank ℤ (LinearMap.range A.mulVecLin) = Module.finrank ℤ (Fin n → ℤ) :=
  LinearMap.finrank_range_of_inj (mulVecLin_injective_of_det_ne_zero A hdet)

/-- Given `L * A * Q = diag(d)` with `d` positive and `det(L) * det(Q) = 1`, produce
`SL_n(ℤ)` matrices `L', Q'` with `L' * A * Q' = diag(d)`. When both determinants are
already `+1` the original matrices work; when both are `-1` a coordinate-flip corrects
the signs. -/
private lemma sign_correct_unit_transform (A : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ)
    (L_mat Q_mat : Matrix (Fin n) (Fin n) ℤ)
    (hL_eq : L_mat * A * Q_mat = Matrix.diagonal d) (hLQ_one : L_mat.det * Q_mat.det = 1) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  have hL_unit : IsUnit L_mat.det := IsUnit.of_mul_eq_one _ hLQ_one
  have hQ_unit : IsUnit Q_mat.det :=
    IsUnit.of_mul_eq_one _ ((mul_comm Q_mat.det L_mat.det).trans hLQ_one)
  rcases Int.isUnit_iff.mp hL_unit with hLd | hLd <;>
    rcases Int.isUnit_iff.mp hQ_unit with hQd | hQd
  · exact ⟨⟨L_mat, hLd⟩, ⟨Q_mat, hQd⟩, hL_eq⟩
  · exfalso; nlinarith [hLQ_one]
  · exfalso; nlinarith [hLQ_one]
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [det_isEmpty] at hLd
      · exact hn
    have : NeZero n := ⟨by omega⟩
    set flip : Matrix (Fin n) (Fin n) ℤ := Matrix.diagonal (Function.update 1 0 (-1))
    have hflip_det : flip.det = -1 := by
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ 0)]; simp
    have hflip_sq : flip * flip = 1 := by
      rw [Matrix.diagonal_mul_diagonal]; ext i j
      simp only [Matrix.diagonal_apply, Matrix.one_apply]
      by_cases h : i = j
      · subst h; by_cases hi : i = 0 <;> simp [hi]
      · simp [h]
    have hflip_diag : flip * Matrix.diagonal d * flip = Matrix.diagonal d := by
      have hcomm : flip * Matrix.diagonal d = Matrix.diagonal d * flip := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]; congr 1; ext i
        simp only [Function.update_apply]; by_cases hi : i = 0 <;> simp [hi, mul_comm]
      rw [hcomm, Matrix.mul_assoc, hflip_sq, Matrix.mul_one]
    have hflip_L_det : (flip * L_mat).det = 1 := by rw [det_mul, hflip_det, hLd]; norm_num
    have hflip_Q_det : (Q_mat * flip).det = 1 := by rw [det_mul, hQd, hflip_det]; norm_num
    refine ⟨⟨flip * L_mat, hflip_L_det⟩, ⟨Q_mat * flip, hflip_Q_det⟩, ?_⟩
    -- reassociate so the flip conjugation surrounds the diagonalised core
    rw [show flip * L_mat * A * (Q_mat * flip) = flip * (L_mat * A * Q_mat) * flip from by
      simp only [Matrix.mul_assoc], hL_eq, hflip_diag]

/-- **A diagonal matrix with nonzero entries in a strictly ordered commutative ring splits as a
self-inverse matrix of unit determinant times a positive diagonal.** -/
private lemma exists_involution_isUnit_det_mul_diagonal_pos {ι R : Type*} [Fintype ι]
    [DecidableEq ι] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a : ι → R}
    (ha_ne : ∀ i, a i ≠ 0) :
    ∃ (s : Matrix ι ι R) (d : ι → R), (∀ i, 0 < d i) ∧ s * s = 1 ∧
      IsUnit s.det ∧ Matrix.diagonal a = s * Matrix.diagonal d := by
  set sv := fun i ↦ ((SignType.sign (a i) : SignType) : R) with hsv_def
  have hsv_sq : ∀ i, sv i * sv i = 1 := fun i ↦ by
    have h : SignType.sign (a i) * SignType.sign (a i) = 1 := by
      simpa [pow_two] using
        SignType.pow_even (SignType.sign (a i)) (by decide : Even 2)
          (sign_ne_zero.mpr (ha_ne i))
    simp only [hsv_def, ← SignType.coe_mul, h, SignType.coe_one]
  have hss : Matrix.diagonal sv * Matrix.diagonal sv = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    ext i
    exact hsv_sq i
  refine ⟨Matrix.diagonal sv, fun i ↦ |a i|, fun i ↦ abs_pos.mpr (ha_ne i), hss,
    Matrix.isUnit_det_of_right_inverse hss, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact (sign_mul_abs (a i)).symm

/-- Refine a unit-determinant diagonalization `P⁻¹ * A * Q = diag a` (with `a i ≠ 0`) of a
positive-determinant matrix to an `SL_n(ℤ)`-diagonalization with the positive diagonal `|a|`:
absorb the signs of `a` into a diagonal `±1` matrix, then sign-correct the unit factors. -/
private lemma exists_SL_diagonal_of_unit_diagonalization (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (a : Fin n → ℤ) (hdet : 0 < A.det) (ha_ne : ∀ i, a i ≠ 0) (hP_unit : IsUnit P.det)
    (hQ_unit : IsUnit Q.det) (hdiag : P⁻¹ * A * Q = Matrix.diagonal a) :
    ∃ (d : Fin n → ℤ) (_ : ∀ i, 0 < d i), ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  obtain ⟨s, d, hd_pos, hss, hs_det_unit, h_sd⟩ :=
    exists_involution_isUnit_det_mul_diagonal_pos ha_ne
  set L_mat := s * P⁻¹ with hL_def
  have hL_eq : L_mat * A * Q = Matrix.diagonal d := by
    calc L_mat * A * Q
        = s * (P⁻¹ * A * Q) := by rw [hL_def]; simp only [Matrix.mul_assoc]
      _ = s * Matrix.diagonal a := by rw [hdiag]
      _ = s * (s * Matrix.diagonal d) := by rw [h_sd]
      _ = (s * s) * Matrix.diagonal d := by rw [Matrix.mul_assoc]
      _ = Matrix.diagonal d := by rw [hss, Matrix.one_mul]
  have hL_unit : IsUnit L_mat.det := by
    rw [hL_def, det_mul]; exact IsUnit.mul hs_det_unit (isUnit_nonsing_inv_det _ hP_unit)
  have hLQ_one : L_mat.det * Q.det = 1 := by
    have h_prod : L_mat.det * A.det * Q.det = ∏ i, d i := by
      rw [← det_mul, ← det_mul, hL_eq, Matrix.det_diagonal]
    rcases Int.isUnit_iff.mp (IsUnit.mul hL_unit hQ_unit) with hone | hneg
    · exact hone
    · exfalso
      have hmul_eq : L_mat.det * Q.det * A.det = ∏ i, d i := by
        rw [mul_right_comm]; exact h_prod
      rw [hneg] at hmul_eq
      have hprod_pos : (0 : ℤ) < ∏ i, d i := Finset.prod_pos fun i _ ↦ hd_pos i
      nlinarith
  exact ⟨d, hd_pos, sign_correct_unit_transform A d L_mat Q hL_eq hLQ_one⟩

/-- **Preimages of a basis of the range under an injective `A` have unit determinant as columns.**
`A.mulVecLin` restricts to a linear equivalence onto its range, and transporting the basis `ab'`
back along it is the family `r`. -/
private theorem isUnit_det_cols_of_mulVecLin_eq_basis (A : Matrix (Fin n) (Fin n) ℤ)
    (hinj : Function.Injective A.mulVecLin)
    {ab' : Module.Basis (Fin n) ℤ ↥(LinearMap.range A.mulVecLin)} {r : Fin n → Fin n → ℤ}
    (hr : ∀ i, A.mulVecLin (r i) = ↑(ab' i)) :
    IsUnit (Matrix.of (fun k j ↦ r j k) : Matrix (Fin n) (Fin n) ℤ).det := by
  set r_basis : Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
    ab'.map (LinearEquiv.ofInjective A.mulVecLin hinj).symm with hr_basis
  have hrb : ⇑r_basis = r := funext fun i ↦ hinj (by
    rw [hr i, hr_basis, Module.Basis.map_apply]
    simp)
  rw [← hrb]
  set e := Pi.basisFun ℤ (Fin n) with he
  have hb : (Matrix.of (fun k j ↦ r_basis j k) : Matrix (Fin n) (Fin n) ℤ)
      = e.toMatrix r_basis := by
    rw [he]
    exact (congrFun Module.Basis.coePiBasisFun.toMatrix_eq_transpose _).symm
  rw [hb]
  simpa [Module.Basis.det_apply] using e.isUnit_det r_basis

/-- **The column matrices of `r` and `b'` intertwine `A` with the diagonal of `a`**, given that `A`
carries each `r j` to `a j • b' j`. -/
private theorem mul_cols_eq_cols_mul_diagonal_of_mulVec_eq_smul
    (A : Matrix (Fin n) (Fin n) ℤ) {a : Fin n → ℤ} {b' r : Fin n → Fin n → ℤ}
    (hkey : ∀ j, A *ᵥ r j = a j • b' j) :
    A * Matrix.of (fun k j ↦ r j k) =
      (Matrix.of fun k j ↦ b' j k) * Matrix.diagonal a := by
  ext k j
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← A.mulVec_apply_eq_sum (r j) k, hkey j]
  simp [mul_comm]

/-- Every integer matrix with positive determinant is `SL_n(ℤ)`-equivalent to a positive
diagonal. -/
private theorem exists_diagonal_of_det_pos (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    ∃ (d : Fin n → ℤ) (_ : ∀ i, 0 < d i), ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
      Matrix.diagonal d := by
  have hdet_ne : A.det ≠ 0 := ne_of_gt hdet
  obtain ⟨b', a, ab', hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun ℤ (Fin n))
      (finrank_range_mulVecLin A hdet_ne)
  have ha_ne : ∀ i, a i ≠ 0 := by
    intro i hi
    have : (ab' i : Fin n → ℤ) = 0 := by rw [hsnf i, hi, zero_smul]
    exact ab'.ne_zero i (Subtype.ext this)
  choose r hr using fun i ↦ LinearMap.mem_range.mp (ab' i).2
  have hkey : ∀ j, A *ᵥ r j = a j • b' j := fun j ↦ by
    rw [← Matrix.mulVecLin_apply, hr j, hsnf j]
  set P_mat : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun k j ↦ b' j k)
  set Q_mat : Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun k j ↦ r j k)
  have hmat_eq : A * Q_mat = P_mat * Matrix.diagonal a :=
    mul_cols_eq_cols_mul_diagonal_of_mulVec_eq_smul A hkey
  have hP_unit : IsUnit P_mat.det := by
    set e := Pi.basisFun ℤ (Fin n) with he
    have hb : P_mat = e.toMatrix b' := by
      rw [he]
      exact (congrFun Module.Basis.coePiBasisFun.toMatrix_eq_transpose _).symm
    rw [hb]
    simpa [Module.Basis.det_apply] using e.isUnit_det b'
  have hQ_unit : IsUnit Q_mat.det :=
    isUnit_det_cols_of_mulVecLin_eq_basis A
      (mulVecLin_injective_of_det_ne_zero A hdet_ne) hr
  have h_diag_eq : P_mat⁻¹ * A * Q_mat = Matrix.diagonal a := by
    rw [Matrix.mul_assoc, hmat_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP_unit,
      Matrix.one_mul]
  exact exists_SL_diagonal_of_unit_diagonalization A P_mat Q_mat a hdet ha_ne hP_unit
    hQ_unit h_diag_eq

/-! ## The divisibility chain

Bézout pivot steps on `2 × 2` blocks replace a pair of diagonal entries `a, b` by
`gcd a b` and `(a / g) * (b / g) * g`, strictly decreasing the head entry unless it already
divides `b`.  Iterating produces a diagonal in which each entry divides the next. -/

private noncomputable def finEquivSum (k : ℕ) : Fin (k + 2) ≃ Fin 2 ⊕ Fin k :=
  (Fin.castOrderIso (by omega : k + 2 = 2 + k)).toEquiv.trans finSumFinEquiv.symm

private lemma gcd_2x2_det_L (a b : ℤ) (ha : 0 < a) :
    let g : ℤ := ↑(a.gcd b); let s := a.gcdA b; let t := a.gcdB b
    (!![s, t; -(b / g), a / g] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp only [det_fin_two_of, mul_neg, sub_neg_eq_add]
  have hg_pos : (0 : ℤ) < ↑(a.gcd b) := by positivity
  suffices h : (a.gcdA b * (a / ↑(a.gcd b)) + a.gcdB b * (b / ↑(a.gcd b))) * ↑(a.gcd b) =
      1 * ↑(a.gcd b) from mul_right_cancel₀ (ne_of_gt hg_pos) h
  rw [one_mul]
  calc (a.gcdA b * (a / ↑(a.gcd b)) + a.gcdB b * (b / ↑(a.gcd b))) * ↑(a.gcd b)
      = a.gcdA b * (a / ↑(a.gcd b) * ↑(a.gcd b)) +
        a.gcdB b * (b / ↑(a.gcd b) * ↑(a.gcd b)) := by ring
    _ = a.gcdA b * a + a.gcdB b * b := by
        rw [Int.ediv_mul_cancel (Int.gcd_dvd_left a b),
          Int.ediv_mul_cancel (Int.gcd_dvd_right a b)]
    _ = a * a.gcdA b + b * a.gcdB b := by ring
    _ = ↑(a.gcd b) := (Int.gcd_eq_gcd_ab a b).symm

private lemma gcd_2x2_det_R (a b : ℤ) :
    let g : ℤ := ↑(a.gcd b); let t := a.gcdB b; let q := b / g
    (!![(1 : ℤ), -(t * q); 1, 1 - t * q] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp [det_fin_two]

private lemma gcd_2x2_mul (a b : ℤ) :
    let g : ℤ := ↑(a.gcd b); let s := a.gcdA b; let t := a.gcdB b
    let p := a / g; let q := b / g
    !![s, t; -q, p] * !![a, (0 : ℤ); 0, b] * !![1, -(t * q); 1, 1 - t * q] =
    (!![g, 0; 0, p * q * g] : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro g s t p q
  have hpg : p * g = a := Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hqg : q * g = b := Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  have hbez : s * a + t * b = g := by linarith [Int.gcd_eq_gcd_ab a b]
  have h1 : !![s, t; -q, p] * (!![a, (0 : ℤ); 0, b] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![s * a, t * b; -(q * a), p * b] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two, mul_zero, add_zero,
        zero_add, neg_mul]
  rw [h1]; ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, Fin.sum_univ_two, mul_one, mul_neg,
      neg_mul, neg_neg]
  · linarith
  · have key : -(s * a * (t * q)) + t * b * (1 - t * q) =
        (1 - (s * p + t * q)) * (t * q * g) := by rw [← hpg, ← hqg]; ring
    rw [key]
    have h2 : (1 - (s * p + t * q)) * g = 0 := by
      have : (s * p + t * q) * g = g := by
        calc (s * p + t * q) * g = s * (p * g) + t * (q * g) := by ring
          _ = s * a + t * b := by rw [hpg, hqg]
          _ = g := hbez
      linarith
    calc (1 - (s * p + t * q)) * (t * q * g) =
          t * q * ((1 - (s * p + t * q)) * g) := by ring
      _ = t * q * 0 := by rw [h2]
      _ = 0 := by ring
  · rw [← hpg, ← hqg]; ring
  · rw [← hpg, ← hqg]; ring

private lemma gcd_natAbs_le_left (a b : ℤ) (ha : 0 < a) :
    (↑(a.gcd b) : ℤ).natAbs ≤ a.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr (ne_of_gt ha))
    (Int.natAbs_dvd_natAbs.mpr (Int.gcd_dvd_left a b))

private lemma gcd_natAbs_lt_left_of_not_dvd (a b : ℤ) (ha : 0 < a) (hndvd : ¬ a ∣ b) :
    (↑(a.gcd b) : ℤ).natAbs < a.natAbs :=
  lt_of_le_of_ne (gcd_natAbs_le_left a b ha) (fun heq ↦ hndvd (by
    have h1 : (↑(a.gcd b) : ℤ).natAbs = a.gcd b := by simp
    have h2 : a.gcd b = a.natAbs := by omega
    exact Int.natAbs_dvd_natAbs.mp (h2 ▸ Nat.gcd_dvd_right a.natAbs b.natAbs)))

/-- Embedding a `2 × 2` left/right multiplication into `Fin (k + 2)` via an equivalence `e`:
the block matrices `(fromBlocks L22 0 0 1).submatrix e e` act on `diagonal d` exactly as `L22`,
`R22` act on the `2 × 2` head block (selected by `e.symm ∘ inl`), leaving the tail untouched. -/
private lemma blockEmbed_mul_diagonal_eq (k : ℕ) (e : Fin (k + 2) ≃ Fin 2 ⊕ Fin k)
    (d d' : Fin (k + 2) → ℤ) (L22 R22 H H' : Matrix (Fin 2) (Fin 2) ℤ)
    (hH : Matrix.diagonal (fun i : Fin 2 ↦ (d ∘ e.symm) (Sum.inl i)) = H)
    (hH' : Matrix.diagonal (fun i : Fin 2 ↦ (d' ∘ e.symm) (Sum.inl i)) = H')
    (hmul : L22 * H * R22 = H')
    (htail : ∀ i : Fin k, (d' ∘ e.symm) (Sum.inr i) = (d ∘ e.symm) (Sum.inr i)) :
    ((fromBlocks L22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e) * Matrix.diagonal d *
      ((fromBlocks R22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e) =
    Matrix.diagonal d' := by
  have hsub : ∀ f : Fin (k + 2) → ℤ,
      (Matrix.diagonal (f ∘ e.symm)).submatrix e e = Matrix.diagonal f := fun f ↦ by
    simp [Function.comp_def]
  -- re-express the diagonal through the reindexing, via the named identity `hsub`
  rw [show Matrix.diagonal d = (Matrix.diagonal (d ∘ e.symm)).submatrix e e from (hsub d).symm]
  simp only [Matrix.submatrix_mul_equiv]
  -- re-express the target diagonal through the same reindexing
  rw [show Matrix.diagonal d' = (Matrix.diagonal (d' ∘ e.symm)).submatrix e e from (hsub d').symm]
  congr 1
  have hdecomp : ∀ f : Fin (k + 2) → ℤ, Matrix.diagonal (f ∘ e.symm) =
      fromBlocks (Matrix.diagonal (fun i : Fin 2 ↦ (f ∘ e.symm) (Sum.inl i)))
        0 0 (Matrix.diagonal (fun i : Fin k ↦ (f ∘ e.symm) (Sum.inr i))) := by
    intro f
    rw [Matrix.fromBlocks_diagonal]
    congr 1
    funext x
    cases x <;> rfl
  rw [hdecomp d, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  rw [hdecomp d']; congr 1
  · rw [hH, hmul, hH']
  · congr 1; ext i; exact (htail i).symm

/-- The pivot step on positions `0` and `j₁` (chosen by an equivalence `e` sending
`0 ↦ inl 0`, `j₁ ↦ inl 1`): conjugating `diagonal d` by the embedded Bézout matrices replaces the
entries `a = d 0`, `b = d j₁` by `gcd a b` and `(a/g)(b/g)g`, leaving all other entries fixed. -/
private lemma gcd_step_matrix_eq (k : ℕ) (e : Fin (k + 2) ≃ Fin 2 ⊕ Fin k) (j₁ : Fin (k + 2))
    (d d' : Fin (k + 2) → ℤ) (a b : ℤ) (hda : d (0 : Fin (k + 2)) = a) (hdb : d j₁ = b)
    (hd'0 : d' (0 : Fin (k + 2)) = ↑(a.gcd b))
    (hd'j : d' j₁ = (a / ↑(a.gcd b)) * (b / ↑(a.gcd b)) * ↑(a.gcd b))
    (hrest : ∀ i, i ≠ (0 : Fin (k + 2)) → i ≠ j₁ → d' i = d i)
    (he0 : e.symm (Sum.inl (0 : Fin 2)) = (0 : Fin (k + 2)))
    (he1 : e.symm (Sum.inl (1 : Fin 2)) = j₁)
    (hinr0 : ∀ i : Fin k, e.symm (Sum.inr i) ≠ (0 : Fin (k + 2)))
    (hinrj : ∀ i : Fin k, e.symm (Sum.inr i) ≠ j₁) :
    ((fromBlocks !![a.gcdA b, a.gcdB b; -(b / ↑(a.gcd b)), a / ↑(a.gcd b)] 0 0
        (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e) * Matrix.diagonal d *
      ((fromBlocks !![(1 : ℤ), -(a.gcdB b * (b / ↑(a.gcd b)));
        1, 1 - a.gcdB b * (b / ↑(a.gcd b))] 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e) =
    Matrix.diagonal d' := by
  have hH : Matrix.diagonal (fun i : Fin 2 ↦ (d ∘ e.symm) (Sum.inl i)) =
      !![a, (0 : ℤ); 0, b] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [Function.comp, he0, he1, hda, hdb]
  have hH' : Matrix.diagonal (fun i : Fin 2 ↦ (d' ∘ e.symm) (Sum.inl i)) =
      !![↑(a.gcd b), (0 : ℤ); 0, (a / ↑(a.gcd b)) * (b / ↑(a.gcd b)) * ↑(a.gcd b)] := by
    ext i m; fin_cases i <;> fin_cases m <;> simp [Function.comp, he0, he1, hd'0, hd'j]
  exact blockEmbed_mul_diagonal_eq k e d d' _ _ _ _ hH hH' (gcd_2x2_mul a b)
    (fun i ↦ by simp only [Function.comp]; exact hrest _ (hinr0 i) (hinrj i))

private noncomputable def genEquiv (k : ℕ) (j : Fin (k + 2)) (_hj : j.val ≠ 0) :
    Fin (k + 2) ≃ Fin 2 ⊕ Fin k :=
  (Equiv.swap (⟨1, by omega⟩ : Fin (k + 2)) j).trans (finEquivSum k)

private lemma genEquiv_zero (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    genEquiv k j hj ⟨0, by omega⟩ = Sum.inl ⟨0, by omega⟩ := by
  simp only [genEquiv, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne (by intro h; simp at h) (fun h ↦ hj (by rw [← h]))]
  -- the swap fixes `0`, so the composite reduces to `finEquivSum k` definitionally
  show finEquivSum k ⟨0, by omega⟩ = _
  unfold finEquivSum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma genEquiv_j (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    genEquiv k j hj j = Sum.inl ⟨1, by omega⟩ := by
  simp only [genEquiv, Equiv.trans_apply, Equiv.swap_apply_right]
  -- the swap sends `j` to `⟨1, _⟩`, so the composite reduces to `finEquivSum k`
  change finEquivSum k ⟨1, by omega⟩ = _; unfold finEquivSum
  simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma genEquiv_symm_inl0 (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    (genEquiv k j hj).symm (Sum.inl (0 : Fin 2)) = (0 : Fin (k + 2)) :=
  (genEquiv k j hj).symm_apply_eq.mpr (genEquiv_zero k j hj).symm

private lemma genEquiv_symm_inl1 (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    (genEquiv k j hj).symm (Sum.inl (1 : Fin 2)) = j :=
  (genEquiv k j hj).symm_apply_eq.mpr (genEquiv_j k j hj).symm

private lemma genEquiv_symm_inr_ne_zero (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) (i : Fin k) :
    (genEquiv k j hj).symm (Sum.inr i) ≠ ⟨0, by omega⟩ := fun h ↦ by
  have := Equiv.apply_symm_apply (genEquiv k j hj) (Sum.inr i)
  rw [h, genEquiv_zero] at this; nomatch this

private lemma genEquiv_symm_inr_ne_j (k : ℕ) (j : Fin (k + 2)) (hj : j.val ≠ 0) (i : Fin k) :
    (genEquiv k j hj).symm (Sum.inr i) ≠ j := fun h ↦ by
  have := Equiv.apply_symm_apply (genEquiv k j hj) (Sum.inr i)
  rw [h, genEquiv_j] at this; nomatch this

private lemma gcd_step_general (k : ℕ) (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i)
    (j : Fin (k + 2)) (hj : j.val ≠ 0) :
    let a := d ⟨0, by omega⟩; let b := d j; let g : ℤ := ↑(a.gcd b)
    ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ) (d' : Fin (k + 2) → ℤ),
      (∀ i, 0 < d' i) ∧ d' ⟨0, by omega⟩ = g ∧
      (∀ i, i ≠ ⟨0, by omega⟩ → i ≠ j → d' i = d i) ∧
      (g.natAbs ≤ a.natAbs) ∧ (¬(a ∣ b) → g.natAbs < a.natAbs) ∧
      (L : Matrix _ _ ℤ) * Matrix.diagonal d * (R : Matrix _ _ ℤ) = Matrix.diagonal d' := by
  intro a b g
  set e := genEquiv k j hj
  set p := a / g; set q := b / g
  set d' : Fin (k + 2) → ℤ := fun i ↦
    if i = (0 : Fin (k + 2)) then g else if i = j then p * q * g else d i
  have ha : 0 < a := hd ⟨0, by omega⟩; have hb : 0 < b := hd j
  have hg_pos : (0 : ℤ) < g :=
    Int.natCast_pos.mpr (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (ne_of_gt ha)))
  have hp_pos : 0 < p := Int.ediv_pos_of_pos_of_dvd ha (le_of_lt hg_pos) (Int.gcd_dvd_left a b)
  have hq_pos : 0 < q := Int.ediv_pos_of_pos_of_dvd hb (le_of_lt hg_pos) (Int.gcd_dvd_right a b)
  have hd'_pos : ∀ i, 0 < d' i := fun i ↦ by
    simp only [d']; split_ifs <;> [exact hg_pos; positivity; exact hd i]
  set L22 := !![a.gcdA b, a.gcdB b; -(b / g), a / g]
  set R22 := !![(1 : ℤ), -(a.gcdB b * (b / g)); 1, 1 - a.gcdB b * (b / g)]
  set L_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks L22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  set R_big : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    (fromBlocks R22 0 0 (1 : Matrix (Fin k) (Fin k) ℤ)).submatrix e e
  have hL_det_big : L_big.det = 1 := by
    simp only [L_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_L a b ha]
  have hR_det_big : R_big.det = 1 := by
    simp only [R_big]; rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one,
      gcd_2x2_det_R a b]
  refine ⟨⟨L_big, hL_det_big⟩, ⟨R_big, hR_det_big⟩, d', hd'_pos,
    by simp [d'], ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2
    simp only [d']; rw [ite_eq_right (show i ≠ (0 : Fin (k + 2)) from hi1), ite_eq_right hi2]
  · exact gcd_natAbs_le_left a b ha
  · exact gcd_natAbs_lt_left_of_not_dvd a b ha
  -- definitional: the values of the constructed `SL` elements are `L_big` and `R_big`
  · change L_big * Matrix.diagonal d * R_big = Matrix.diagonal d'
    refine gcd_step_matrix_eq k e j d d' a b rfl rfl rfl ?_ ?_
      (by simp only [e]; exact genEquiv_symm_inl0 k j hj)
      (by simp only [e]; exact genEquiv_symm_inl1 k j hj)
      (fun i ↦ by simp only [e]; exact genEquiv_symm_inr_ne_zero k j hj i)
      (fun i ↦ by simp only [e]; exact genEquiv_symm_inr_ne_j k j hj i)
    -- definitional: unfold the local abbreviation `d'` at the pivot index
    · change (if j = (0 : Fin (k + 2)) then g else if j = j then p * q * g else d j) = _
      rw [ite_eq_right (fun h ↦ hj (by rw [h]; rfl)), ite_eq_left rfl]
    · intro i hi0 hij; simp only [d', ite_eq_right hi0, ite_eq_right hij]

private lemma dvd_diag_of_SL_transform (m : ℕ) (d d' : Fin m → ℤ) (c : ℤ) (hc : ∀ i, c ∣ d i)
    (L R : Matrix (Fin m) (Fin m) ℤ) (heq : L * Matrix.diagonal d * R = Matrix.diagonal d') :
    ∀ i, c ∣ d' i := by
  -- read the value off the diagonal so the product identity `heq` applies entrywise
  intro i; rw [show d' i = (Matrix.diagonal d') i i by simp, ← heq, mul_apply]
  apply Finset.dvd_sum; intro k _; rw [mul_apply]; apply dvd_mul_of_dvd_left
  apply Finset.dvd_sum; intro l _; simp only [diagonal_apply]; split_ifs with h
  · subst h; exact dvd_mul_of_dvd_right (hc l) _
  · simp

private noncomputable def fin1Sum (k : ℕ) : Fin (k + 1) ≃ Fin 1 ⊕ Fin k :=
  (Fin.castOrderIso (show k + 1 = 1 + k by omega)).toEquiv.trans finSumFinEquiv.symm

private lemma fin1Sum_zero (k : ℕ) : fin1Sum k (0 : Fin (k + 1)) = Sum.inl (0 : Fin 1) := by
  unfold fin1Sum; simp [Equiv.trans_apply, Fin.castOrderIso]; rfl

private lemma fin1Sum_succ (k : ℕ) (i : Fin k) :
    fin1Sum k ⟨i.val + 1, by omega⟩ = Sum.inr i := by
  unfold fin1Sum; simp only [Equiv.trans_apply, Fin.castOrderIso]; rw [Equiv.symm_apply_eq]
  simp only [finSumFinEquiv, Fin.addCases, Equiv.coe_fn_mk, Fin.cast_mk, Order.lt_one_iff,
    Fin.val_eq_zero_iff, eq_rec_constant, Sum.elim_inr]
  ext; simp only [Fin.val_natAdd]; omega

private lemma fin1Sum_symm_inl (k : ℕ) :
    (fin1Sum k).symm (Sum.inl (0 : Fin 1)) = (0 : Fin (k + 1)) :=
  (fin1Sum k).symm_apply_eq.mpr (fin1Sum_zero k).symm

private lemma fin1Sum_symm_inr (k : ℕ) (i : Fin k) :
    (fin1Sum k).symm (Sum.inr i) = ⟨i.val + 1, by omega⟩ :=
  (fin1Sum k).symm_apply_eq.mpr (fin1Sum_succ k i).symm

/-- **A diagonal reindexed by the head-tail splitting is the block diagonal of its head entry and
its tail.** Under `fin1Sum k`, the diagonal matrix of `f ∘ (fin1Sum k).symm` is the block diagonal
with the `1 × 1` block `f 0` and the tail block `fun i ↦ f (i + 1)`. -/
private lemma diagonal_comp_fin1Sum_symm {α : Type*} [Zero α] {k : ℕ} (f : Fin (k + 1) → α) :
    Matrix.diagonal (f ∘ (fin1Sum k).symm) =
      fromBlocks (Matrix.diagonal (fun _ : Fin 1 ↦ f 0)) 0 0
        (Matrix.diagonal (fun i : Fin k ↦ f ⟨i.val + 1, by omega⟩)) := by
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  cases x with
  | inl i => fin_cases i; simp [fin1Sum_symm_inl]
  | inr i => simp [fin1Sum_symm_inr]

private lemma make_first_divide_all (k : ℕ) (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i) :
    ∃ (d' : Fin (k + 2) → ℤ) (_ : ∀ i, 0 < d' i) (_ : ∀ j, d' (0 : Fin (k + 2)) ∣ d' j),
    ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ),
      (L : Matrix _ _ ℤ) * Matrix.diagonal d * (R : Matrix _ _ ℤ) = Matrix.diagonal d' := by
  have ha_pos : 0 < d (0 : Fin (k + 2)) := hd 0
  obtain ⟨N, hN⟩ : ∃ N, (d (0 : Fin (k + 2))).natAbs = N := ⟨_, rfl⟩
  revert d hd ha_pos
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro d hd ha_pos hN
    by_cases hall : ∀ j, d (0 : Fin (k + 2)) ∣ d j
    · exact ⟨d, hd, hall, 1, 1, by simp⟩
    · push Not at hall
      obtain ⟨j, hj_ndvd⟩ := hall
      have hj_ne : j.val ≠ 0 := fun h ↦ hj_ndvd ((Fin.ext h : j = 0) ▸ dvd_refl _)
      obtain ⟨L₁, R₁, d₁, hd₁_pos, hd₁_zero, hd₁_rest, _, hlt, hmul₁⟩ :=
        gcd_step_general k d hd j hj_ne
      have hN₁ : (d₁ (0 : Fin (k + 2))).natAbs < N := by
        -- definitional: the literal `0` and the constructor `⟨0, _⟩` coincide in `Fin (k + 2)`
        rw [show d₁ (0 : Fin (k + 2)) = d₁ ⟨0, by omega⟩ from rfl, hd₁_zero, ← hN]
        exact hlt hj_ndvd
      obtain ⟨d₂, hd₂_pos, hd₂_div, L₂, R₂, hmul₂⟩ :=
        ih _ hN₁ d₁ hd₁_pos (hd₁_pos 0) rfl
      refine ⟨d₂, hd₂_pos, hd₂_div, L₂ * L₁, R₁ * R₂, ?_⟩
      simp only [SpecialLinearGroup.coe_mul]
      -- reassociate to expose `L₁ * diagonal d * R₁`, the shape `hmul₁` rewrites
      rw [show ((L₂ : Matrix _ _ ℤ) * (L₁ : Matrix _ _ ℤ)) * Matrix.diagonal d *
        ((R₁ : Matrix _ _ ℤ) * (R₂ : Matrix _ _ ℤ)) = (L₂ : Matrix _ _ ℤ) *
        ((L₁ : Matrix _ _ ℤ) * Matrix.diagonal d * (R₁ : Matrix _ _ ℤ)) * (R₂ : Matrix _ _ ℤ)
        by simp [Matrix.mul_assoc], hmul₁, hmul₂]

private noncomputable def slSuccEmbed {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  let e := fin1Sum (k + 1)
  refine ⟨(fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).submatrix e e, ?_⟩
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, one_mul, M.prop]

private lemma slSuccEmbed_mul_diagonal (k : ℕ) (d : Fin (k + 2) → ℤ)
    (L R : SpecialLinearGroup (Fin (k + 1)) ℤ) (d'_tail : Fin (k + 1) → ℤ) (hmul :
    (L : Matrix _ _ ℤ) * Matrix.diagonal (fun i : Fin (k + 1) ↦ d ⟨i.val + 1, by omega⟩) *
    (R : Matrix _ _ ℤ) = Matrix.diagonal d'_tail) :
    let d_out : Fin (k + 2) → ℤ := fun i ↦
      if i = (0 : Fin (k + 2)) then d 0 else d'_tail ⟨i.val - 1, by omega⟩
    (slSuccEmbed L : Matrix _ _ ℤ) * Matrix.diagonal d *
      (slSuccEmbed R : Matrix _ _ ℤ) = Matrix.diagonal d_out := by
  intro d_out
  -- no `set` for the splitting: `diagonal_comp_fin1Sum_symm` spells `fin1Sum (k + 1)` out
  have hsub : ∀ f : Fin (k + 2) → ℤ,
      (Matrix.diagonal (f ∘ (fin1Sum (k + 1)).symm)).submatrix (fin1Sum (k + 1))
        (fin1Sum (k + 1)) = Matrix.diagonal f := fun f ↦ by
    simp [Function.comp_def]
  -- re-express the diagonal through the reindexing, via the named identity `hsub`
  rw [show Matrix.diagonal d =
      (Matrix.diagonal (d ∘ (fin1Sum (k + 1)).symm)).submatrix (fin1Sum (k + 1)) (fin1Sum (k + 1))
      from (hsub d).symm]
  -- definitional: `slSuccEmbed` is the embedded block matrix
  change (fromBlocks 1 0 0 (L : Matrix _ _ ℤ)).submatrix (fin1Sum (k + 1)) (fin1Sum (k + 1)) *
    (Matrix.diagonal (d ∘ (fin1Sum (k + 1)).symm)).submatrix (fin1Sum (k + 1)) (fin1Sum (k + 1)) *
    (fromBlocks 1 0 0 (R : Matrix _ _ ℤ)).submatrix (fin1Sum (k + 1)) (fin1Sum (k + 1)) = _
  simp only [Matrix.submatrix_mul_equiv]
  rw [diagonal_comp_fin1Sum_symm d]
  rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul]
  rw [fromBlocks_multiply]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one]
  -- re-express the output diagonal through the reindexing before comparing blocks
  rw [show Matrix.diagonal d_out =
      (Matrix.diagonal (d_out ∘ (fin1Sum (k + 1)).symm)).submatrix (fin1Sum (k + 1))
        (fin1Sum (k + 1))
      from (hsub d_out).symm]; congr 1
  have h_out_decomp : Matrix.diagonal (d_out ∘ (fin1Sum (k + 1)).symm) =
      fromBlocks (Matrix.diagonal (fun _ : Fin 1 ↦ d 0)) 0 0 (Matrix.diagonal d'_tail) := by
    rw [diagonal_comp_fin1Sum_symm d_out]
    have h0 : d_out 0 = d 0 := by simp [d_out]
    have htail : (fun i : Fin (k + 1) ↦ d_out ⟨i.val + 1, by omega⟩) = d'_tail := by
      funext i; simp [d_out]
    rw [h0, htail]
  rw [h_out_decomp, hmul]

/-- Prepending a head entry `c` that divides every entry of `d_tail'` to a divisibility chain
again yields a divisibility chain: the head step is `c ∣ d_tail' 0`, the later steps are the
tail chain. -/
private lemma divChain_prepend (k : ℕ) (c : ℤ) (d_tail' : Fin (k + 1) → ℤ)
    (hc : ∀ i, c ∣ d_tail' i)
    (htail : ∀ (i : ℕ) (hi : i + 1 < k + 1), d_tail' ⟨i, by omega⟩ ∣ d_tail' ⟨i + 1, hi⟩)
    (i : ℕ) (hi : i + 1 < k + 2) :
    (if (⟨i, by omega⟩ : Fin (k + 2)) = 0 then c else d_tail' ⟨i - 1, by omega⟩) ∣
    (if (⟨i + 1, hi⟩ : Fin (k + 2)) = 0 then c else d_tail' ⟨i + 1 - 1, by omega⟩) := by
  cases i with
  | zero =>
    -- definitional: the constructor `⟨0, _⟩` is the literal `0` in `Fin (k + 2)`
    rw [ite_eq_left (show (⟨0, by omega⟩ : Fin (k + 2)) = 0 from rfl),
      ite_eq_right (show (⟨1, hi⟩ : Fin (k + 2)) ≠ 0 from
        fun h ↦ absurd (Fin.ext_iff.mp h) (by simp))]
    exact hc ⟨0, by omega⟩
  | succ i =>
    rw [ite_eq_right (show (⟨i + 1, by omega⟩ : Fin (k + 2)) ≠ 0 from
        fun h ↦ absurd (Fin.ext_iff.mp h) (by simp)),
      ite_eq_right (show (⟨i + 2, hi⟩ : Fin (k + 2)) ≠ 0 from
        fun h ↦ absurd (Fin.ext_iff.mp h) (by simp))]
    -- definitional: `i + 1 - 1` reduces to `i`
    change d_tail' ⟨i, by omega⟩ ∣ d_tail' ⟨i + 1, by omega⟩
    exact htail i (by omega)

/-- Assuming the divisibility-chain normalisation in dimension `k + 1`, every positive diagonal of
length `k + 2` is `SL`-equivalent to a positive diagonal in divisibility-chain form. -/
private lemma exists_divChain_of_pos_diagonal_succ {k : ℕ}
    (ih : ∀ d : Fin (k + 1) → ℤ, (∀ i, 0 < d i) →
      ∃ (d' : Fin (k + 1) → ℤ) (_ : ∀ i, 0 < d' i)
        (_ : ∀ (i : ℕ) (hi : i + 1 < k + 1), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
      ∃ (L R : SpecialLinearGroup (Fin (k + 1)) ℤ),
        (L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) * Matrix.diagonal d *
          (R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) = Matrix.diagonal d')
    (d : Fin (k + 2) → ℤ) (hd : ∀ i, 0 < d i) :
      ∃ (d' : Fin (k + 2) → ℤ) (_ : ∀ i, 0 < d' i)
        (_ : ∀ (i : ℕ) (hi : i + 1 < k + 2), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
      ∃ (L R : SpecialLinearGroup (Fin (k + 2)) ℤ),
        (L : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) * Matrix.diagonal d *
          (R : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) = Matrix.diagonal d' := by
  obtain ⟨d₁, hd₁_pos, hd₁_div, L₁, R₁, hmul₁⟩ := make_first_divide_all k d hd
  obtain ⟨d_tail', hd_tail'_pos, hd_tail'_chain, L_tail, R_tail, hmul_tail⟩ :=
    ih (fun i : Fin (k + 1) ↦ d₁ ⟨i.val + 1, by omega⟩)
      (fun i ↦ hd₁_pos ⟨i.val + 1, by omega⟩)
  set d₂ : Fin (k + 2) → ℤ := fun i ↦
    if i = (0 : Fin (k + 2)) then d₁ 0
    else d_tail' ⟨i.val - 1, by omega⟩
  have hd₂_pos : ∀ i, 0 < d₂ i := by
    intro i; simp only [d₂]; split_ifs <;> [exact hd₁_pos 0; exact hd_tail'_pos _]
  have hd₂_chain : ∀ (i : ℕ) (hi : i + 1 < k + 2),
      d₂ ⟨i, by omega⟩ ∣ d₂ ⟨i + 1, hi⟩ :=
    divChain_prepend k (d₁ 0) d_tail'
      (dvd_diag_of_SL_transform (k + 1) (fun i : Fin (k + 1) ↦ d₁ ⟨i.val + 1, by omega⟩)
        d_tail' (d₁ 0) (fun i ↦ hd₁_div ⟨i.val + 1, by omega⟩)
        (L_tail : Matrix _ _ ℤ) (R_tail : Matrix _ _ ℤ) hmul_tail) hd_tail'_chain
  refine ⟨d₂, hd₂_pos, hd₂_chain, slSuccEmbed L_tail * L₁, R₁ * slSuccEmbed R_tail, ?_⟩
  simp only [SpecialLinearGroup.coe_mul]
  -- reassociate to expose `L₁ * diagonal d * R₁`, the shape `hmul₁` rewrites
  rw [show ((slSuccEmbed L_tail : Matrix _ _ ℤ) * (L₁ : Matrix _ _ ℤ)) * Matrix.diagonal d *
    ((R₁ : Matrix _ _ ℤ) * (slSuccEmbed R_tail : Matrix _ _ ℤ)) =
    (slSuccEmbed L_tail : Matrix _ _ ℤ) * ((L₁ : Matrix _ _ ℤ) * Matrix.diagonal d *
    (R₁ : Matrix _ _ ℤ)) * (slSuccEmbed R_tail : Matrix _ _ ℤ)
    by simp [Matrix.mul_assoc], hmul₁,
    slSuccEmbed_mul_diagonal k d₁ L_tail R_tail d_tail' hmul_tail]

private lemma exists_divChain_of_pos_diagonal (d : Fin n → ℤ) (hd : ∀ i, 0 < d i) :
    ∃ (d' : Fin n → ℤ) (_ : ∀ i, 0 < d' i)
      (_ : ∀ (i : ℕ) (hi : i + 1 < n), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ),
      (L : Matrix (Fin n) (Fin n) ℤ) * Matrix.diagonal d *
        (R : Matrix (Fin n) (Fin n) ℤ) = Matrix.diagonal d' := by
  suffices h : ∀ (m : ℕ) (d : Fin m → ℤ), (∀ i, 0 < d i) →
    ∃ (d' : Fin m → ℤ) (_ : ∀ i, 0 < d' i)
      (_ : ∀ (i : ℕ) (hi : i + 1 < m), d' ⟨i, by omega⟩ ∣ d' ⟨i + 1, hi⟩),
    ∃ (L R : SpecialLinearGroup (Fin m) ℤ),
      (L : Matrix (Fin m) (Fin m) ℤ) * Matrix.diagonal d *
        (R : Matrix (Fin m) (Fin m) ℤ) = Matrix.diagonal d' from h n d hd
  intro m
  induction m with
  | zero => exact fun d hd ↦ ⟨d, hd, fun i hi ↦ by omega, 1, 1, by simp⟩
  | succ m ih =>
    cases m with
    | zero => exact fun d hd ↦ ⟨d, hd, fun i hi ↦ by omega, 1, 1, by simp⟩
    | succ k => exact exists_divChain_of_pos_diagonal_succ ih

/-- Successive divisibility upgrades to divisibility along any `i ≤ j`. -/
private lemma dvd_of_le_of_chain {d : Fin n → ℤ}
    (hchain : ∀ (i : ℕ) (hi : i + 1 < n), d ⟨i, by omega⟩ ∣ d ⟨i + 1, hi⟩)
    {i j : Fin n} (hij : i ≤ j) : d i ∣ d j := by
  suffices h : ∀ (t : ℕ) (ht : i.val + t < n), d i ∣ d ⟨i.val + t, ht⟩ by
    simpa [Nat.add_sub_cancel' (Fin.val_le_of_le hij)] using h (j.val - i.val) (by omega)
  intro t
  induction t with
  | zero => intro ht; exact dvd_rfl
  | succ m ih => exact fun ht ↦ dvd_trans (ih (by omega)) (hchain (i.val + m) ht)

/-- **Smith normal form over `ℤ` with special linear transformations.** Every square integer
matrix `A` with positive determinant can be brought to diagonal form by determinant-one row and
column operations, with positive diagonal entries each dividing the next (the invariant
factors of `A`). -/
theorem exists_smith_normal_form_of_det_pos (A : Matrix (Fin n) (Fin n) ℤ) (hA : 0 < A.det) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ) (d : Fin n → ℤ), (∀ i, 0 < d i) ∧
      (∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j) ∧
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
        Matrix.diagonal d := by
  obtain ⟨d₀, hd₀_pos, L₀, R₀, hLR₀⟩ := exists_diagonal_of_det_pos A hA
  obtain ⟨d, hd_pos, hd_chain, L₁, R₁, hLR₁⟩ := exists_divChain_of_pos_diagonal d₀ hd₀_pos
  refine ⟨L₁ * L₀, R₀ * R₁, d, hd_pos, fun i j hij ↦ dvd_of_le_of_chain hd_chain hij, ?_⟩
  simp only [SpecialLinearGroup.coe_mul]
  calc (↑L₁ : Matrix _ _ ℤ) * ↑L₀ * A * (↑R₀ * ↑R₁)
      = ↑L₁ * (↑L₀ * A * ↑R₀) * ↑R₁ := by simp only [Matrix.mul_assoc]
    _ = ↑L₁ * Matrix.diagonal d₀ * ↑R₁ := by rw [hLR₀]
    _ = Matrix.diagonal d := hLR₁

/-! ## Uniqueness of the invariant factors

The partial products `d 0 * ⋯ * d (k-1)` of a chained diagonal are determined by the
`GL_n(ℤ)`-equivalence class, by a Cauchy–Binet expansion of the leading `k × k` minor. -/

/-- Along a divisibility chain, the product of the first `k` entries divides the product of
the entries at any `k` distinct positions. -/
private lemma prod_dvd_prod_of_injective {d : Fin n → ℤ}
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j) (k : ℕ) (hk : k ≤ n) (f : Fin k → Fin n)
    (hf : Function.Injective f) :
    (∏ j : Fin k, d ⟨j.val, by omega⟩) ∣ (∏ j : Fin k, d (f j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨j₀, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun j ↦ (f j).val) Finset.univ_nonempty
    have hge : k ≤ (f j₀).val := by
      by_contra hlt; push Not at hlt
      have : Fintype.card (Fin (k + 1)) ≤ Fintype.card (Fin k) :=
        Fintype.card_le_of_injective
          (fun j : Fin (k + 1) ↦ (⟨(f j).val, by
            exact Nat.lt_of_le_of_lt (hmax j (Finset.mem_univ _)) hlt⟩ : Fin k))
          (fun j₁ j₂ heq ↦ by simp only [Fin.mk.injEq] at heq; exact hf (Fin.ext heq))
      simp at this
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succAbove _ j₀, mul_comm (d (f j₀)) _]
    exact mul_dvd_mul (ih (by omega) (f ∘ j₀.succAbove)
      (hf.comp Fin.succAbove_right_injective)) (hd (by simpa [Fin.le_def] using hge))

/-- One direction of the invariant-factor comparison, by Cauchy–Binet on the leading minor. -/
private lemma prod_take_dvd_of_mul_diagonal_mul_eq {c d : Fin n → ℤ}
    (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j) (P Q : Matrix (Fin n) (Fin n) ℤ)
    (hcd : P * Matrix.diagonal c * Q = Matrix.diagonal d) (k : ℕ) (hk : k ≤ n) :
    (∏ j : Fin k, c ⟨j.val, by omega⟩) ∣ (∏ j : Fin k, d ⟨j.val, by omega⟩) := by
  set e : Fin k → Fin n := fun j ↦ ⟨j.val, by omega⟩ with he_def
  have he_inj : Function.Injective e := fun _ _ h ↦ Fin.ext (Fin.mk.inj h)
  have hprod_d : ∏ j : Fin k, d (e j) =
      det ((P * Matrix.diagonal c * Q).submatrix e e) := by
    rw [hcd]
    -- a diagonal reindexed by an equiv is the diagonal of the composed function
    rw [show (Matrix.diagonal d).submatrix e e =
        Matrix.diagonal (fun j : Fin k ↦ d (e j)) from by
      ext i j; simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, he_inj.eq_iff]]
    exact Matrix.det_diagonal.symm
  rw [hprod_d]
  have hcb : det ((P * Matrix.diagonal c * Q).submatrix e e) =
      ∑ g : Fin k → Fin n, (∏ i : Fin k, c (g i)) *
        ((∏ i : Fin k, Q (g i) (e i)) * det (P.submatrix e g)) := by
    simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
    rw [Finset.sum_comm]; congr 1; ext g; congr 1; ext σ
    simp only [Finset.prod_mul_distrib]; ring
  rw [hcb]
  apply Finset.dvd_sum; intro g _
  by_cases hg : Function.Injective g
  · exact dvd_mul_of_dvd_left (prod_dvd_prod_of_injective hc k hk g hg) _
  · simp only [Function.not_injective_iff] at hg; obtain ⟨j₁, j₂, hgeq, hjne⟩ := hg
    have : det (P.submatrix e g) = 0 := Matrix.det_zero_of_column_eq hjne (fun i ↦ by
      simp only [Matrix.submatrix_apply, hgeq])
    simp [this]

/-- **Uniqueness of the Smith normal form**: two nonnegative diagonals with divisibility
chains in the same `GL_n(ℤ)`-equivalence class are equal — including singular forms, whose
chains vanish from the first zero on.  Together with
`Matrix.exists_smith_normal_form_of_det_pos` this makes the invariant factors of a
positive-determinant integer matrix well defined. -/
theorem smith_normal_form_unique {c d : Fin n → ℤ} (hc_pos : ∀ i, 0 ≤ c i)
    (hd_pos : ∀ i, 0 ≤ d i) (hc : ∀ ⦃i j : Fin n⦄, i ≤ j → c i ∣ c j)
    (hd : ∀ ⦃i j : Fin n⦄, i ≤ j → d i ∣ d j) (L R : GeneralLinearGroup (Fin n) ℤ)
    (h : (L : Matrix (Fin n) (Fin n) ℤ) * Matrix.diagonal c *
      (R : Matrix (Fin n) (Fin n) ℤ) = Matrix.diagonal d) : c = d := by
  have h' : (↑L⁻¹ : Matrix (Fin n) (Fin n) ℤ) * Matrix.diagonal d *
      (↑R⁻¹ : Matrix (Fin n) (Fin n) ℤ) = Matrix.diagonal c := by
    rw [← h]
    simp [Matrix.mul_assoc]
  have key : ∀ k (hk : k ≤ n),
      ∏ j : Fin k, c ⟨j.val, by omega⟩ = ∏ j : Fin k, d ⟨j.val, by omega⟩ := fun k hk ↦
    Int.dvd_antisymm
      (Finset.prod_nonneg fun j _ ↦ hc_pos _)
      (Finset.prod_nonneg fun j _ ↦ hd_pos _)
      (prod_take_dvd_of_mul_diagonal_mul_eq hc _ _ h k hk)
      (prod_take_dvd_of_mul_diagonal_mul_eq hd _ _ h' k hk)
  have split_eq : ∀ (a : Fin n → ℤ) (i : Fin n),
      ∏ j : Fin (i.val + 1), a ⟨j.val, by omega⟩ =
      (∏ j : Fin i.val, a ⟨j.val, by omega⟩) * a i := by
    intro a i; rw [Fin.prod_univ_castSucc]; congr 1
  -- entries agree below the first zero by cancellation, and a chained sequence vanishes
  -- from its first zero on; equal partial products force the same vanishing threshold
  have chain_zero : ∀ {a : Fin n → ℤ}, (∀ ⦃i j : Fin n⦄, i ≤ j → a i ∣ a j) →
      ∀ {i : Fin n}, (∏ j : Fin i.val, a ⟨j.val, by omega⟩) = 0 → a i = 0 := by
    intro a ha i hpre
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hpre
    have := ha (show (⟨l.val, by omega⟩ : Fin n) ≤ i from by
      simp [Fin.le_def, l.isLt.le])
    rw [hl] at this
    simpa using this
  funext i
  have hprod₁ := key (i.val + 1) (by omega)
  rw [split_eq c i, split_eq d i, key i.val (by omega)] at hprod₁
  by_cases hpre : (∏ j : Fin i.val, d ⟨j.val, by omega⟩) = 0
  · rw [chain_zero hd hpre, chain_zero hc (by rw [key i.val (by omega)]; exact hpre)]
  · exact mul_left_cancel₀ hpre hprod₁

end Matrix
