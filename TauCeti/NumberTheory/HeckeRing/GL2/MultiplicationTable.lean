/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Degree

/-!
# The `GL₂` multiplication table: telescoping identities

The first multiplication identity of Shimura's Theorem 3.24 for the `GL₂` Hecke ring:
`T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^(k−2))` for `k ≥ 2`, by telescoping the divisor-pair
expansion of `T(pᵏ)` against the index shift `T(p,p) · T(pʲ, p^d) = T(p^(j+1), p^(d+1))`.

The file also proves `heckeT_prime_mul_heckeTDiag_one_prime_pow`, Shimura's Theorem 3.24(5):
`T(p) · T(1, pᵏ) = T(1, p^(k+1)) + m · T(p, pᵏ)`, with multiplicity `m = p + 1` at
`k = 1` and `m = p` otherwise. No positivity hypothesis on `k` is needed: at `k = 0` the
identity reads `T(p) = T(1, p)`, since `T(1,1) = 1` and `T(p,1) = 0` for prime `p`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), first section.

## Main results

* `HeckeRing.GL2.heckeTDiag_one_prime_pow_eq`: `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^(k−2))`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing DoubleCoset Finset HeckeRing.GLn Matrix.SpecialLinearGroup

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

/-- Scaling a diagonal Hecke element in the good range: `T(c,c) · T(a,d) = T(c·a, c·d)` when
`a ∣ d` and all three are positive. -/
private lemma heckeTScalar_mul_heckeTDiag_of_pos {c a d : ℕ} (hc : 0 < c) (ha : 0 < a)
    (hd : 0 < d) (had : a ∣ d) :
    heckeTScalar c * heckeTDiag a d = heckeTDiag (c * a) (c * d) := by
  rw [heckeTDiag_eq_diagElem ha hd had,
    heckeTDiag_eq_diagElem (Nat.mul_pos hc ha) (Nat.mul_pos hc hd) (mul_dvd_mul_left c had),
    HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
      (transposeAntiInvolution_onHeckeCoset_eq_self 2),
    heckeTScalar_of_pos hc,
    diagElem_mul_const 2 ![a, d] (fun i ↦ by fin_cases i <;> assumption) c hc]
  exact congrArg diagElem (funext fun i ↦ by fin_cases i <;> simp [Pi.mul_apply, Nat.mul_comm])

/-- Scaling a diagonal Hecke element: `T(c,c) · T(a,d) = T(c·a, c·d)`, with **no hypotheses**.

`heckeTDiag` is zero-extended off the divisor-pair range, and that extension is compatible with
scaling: outside the range both sides vanish, since `0 < c·a` forces `0 < a`, and for `0 < c` the
divisibility `c·a ∣ c·d` is equivalent to `a ∣ d`. Primality plays no role, and neither does the
shape of `a` and `d`. -/
@[simp]
lemma heckeTScalar_mul_heckeTDiag (c a d : ℕ) :
    heckeTScalar c * heckeTDiag a d = heckeTDiag (c * a) (c * d) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [heckeTScalar_def, heckeTDiag_def]
  by_cases hcond : 0 < a ∧ 0 < d ∧ a ∣ d
  · exact heckeTScalar_mul_heckeTDiag_of_pos hc hcond.1 hcond.2.1 hcond.2.2
  · have hzero : heckeTDiag a d = 0 := by rw [heckeTDiag_def]; exact ite_eq_right hcond
    have hzero' : heckeTDiag (c * a) (c * d) = 0 := by
      rw [heckeTDiag_def]
      refine ite_eq_right fun h ↦ hcond ⟨?_, ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp at h
        · exact ha
      · rcases Nat.eq_zero_or_pos d with rfl | hd
        · simp at h
        · exact hd
      · exact (Nat.mul_dvd_mul_iff_left hc).mp h.2.2
    rw [hzero, hzero', mul_zero]

/-- The index shift: `T(p,p) · T(pʲ, p^d) = T(p^(j+1), p^(d+1))`, for arbitrary `p`, `j`, `d`.

The prime-power case of `heckeTScalar_mul_heckeTDiag`; like it, unconditional.

Deliberately *not* `@[simp]`: the general rule carries the attribute, and it already rewrites
this left-hand side (to `T(p·pʲ, p·p^d)`), so annotating the specialisation too would leave its
left-hand side outside simp normal form — `simpNF` rejects exactly that. Callers wanting the
`p^(j+1)` form rewrite with this lemma by name. -/
lemma heckeTScalar_mul_heckeTDiag_prime_pow (j d : ℕ) :
    heckeTScalar p * heckeTDiag (p ^ j) (p ^ d) =
      heckeTDiag (p ^ (j + 1)) (p ^ (d + 1)) := by
  rw [heckeTScalar_mul_heckeTDiag, ← pow_succ' p j, ← pow_succ' p d]

include hp in
/-- **Shimura, Theorem 3.24(2)**: `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^(k−2))` for `k ≥ 2`:
the divisor-pair expansion of `T(pᵏ)` telescopes against the index shift. -/
theorem heckeTDiag_one_prime_pow_eq (k : ℕ) (hk : 2 ≤ k) :
    heckeTDiag 1 (p ^ k) = heckeT ⟨p ^ k, pow_pos hp.pos k⟩ -
      heckeTScalar p * heckeT ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ := by
  suffices h : heckeTDiag 1 (p ^ k) +
      heckeTScalar p * heckeT ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ =
      heckeT ⟨p ^ k, pow_pos hp.pos k⟩ from eq_sub_iff_add_eq.mpr h
  rw [heckeT_prime_pow_expansion p hp k, heckeT_prime_pow_expansion p hp (k - 2), Finset.mul_sum]
  have shift : ∀ j ∈ Finset.range ((k - 2) / 2 + 1),
      heckeTScalar p * heckeTDiag (p ^ j) (p ^ (k - 2 - j)) =
      heckeTDiag (p ^ (j + 1)) (p ^ (k - (j + 1))) := fun j hj ↦ by
    rw [Finset.mem_range] at hj
    have harith : k - 2 - j + 1 = k - (j + 1) := by omega
    rw [heckeTScalar_mul_heckeTDiag_prime_pow p j (k - 2 - j), harith]
  -- The two ranges are equal but not syntactically so — `(k - 2) / 2 + 1` and `k / 2` involve
  -- truncated subtraction and division, which only `omega` sees through, so `rw` needs the
  -- equality supplied explicitly before `sum_range_succ'` can peel off the first term.
  rw [Finset.sum_congr rfl shift,
    show Finset.range ((k - 2) / 2 + 1) = Finset.range (k / 2) from by congr 1; omega,
    Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero]
  abel

section SupportAnalysis

/-! ## Support analysis for `T(1,p) · T(1,pᵏ)`

Every double coset in the support of the product `T(1,p) · T(1,pᵏ)` is `T(1, p^(k+1))` or
`T(p, pᵏ)`: the determinant balances to `p^(k+1)`, and the first invariant factor divides
`p` because the conjugated middle matrix stays integral. -/

private lemma matrix_isolate_middle (L_ℤ M R_ℤ D : Matrix (Fin 2) (Fin 2) ℤ)
    (hLadj : L_ℤ.adjugate * L_ℤ = 1) (hRadj : R_ℤ * R_ℤ.adjugate = 1)
    (heq_LMR : L_ℤ * M * R_ℤ = D) : M = L_ℤ.adjugate * D * R_ℤ.adjugate := by
  have hassoc : L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate =
      L_ℤ.adjugate * L_ℤ * M * (R_ℤ * R_ℤ.adjugate) := by
    simp [mul_assoc]
  rw [← heq_LMR, hassoc, hLadj, hRadj, one_mul, mul_one]

private lemma first_invariant_dvd_p_of_product (p : ℕ) (S : SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (hdiv : IsDvdChain a) (L R : SpecialLinearGroup (Fin 2) ℤ) (k : ℕ)
    (heq : (L : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (S : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (R : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i ↦ (a i : ℤ))) : a 0 ∣ p := by
  set dp := Matrix.diagonal (![1, p] : Fin 2 → ℤ)
  set dpk := Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ)
  set S_ℤ := (S : Matrix (Fin 2) (Fin 2) ℤ)
  set M := dp * S_ℤ * dpk
  set L_ℤ := (L : Matrix (Fin 2) (Fin 2) ℤ)
  set R_ℤ := (R : Matrix (Fin 2) (Fin 2) ℤ)
  have hLadj : L_ℤ.adjugate * L_ℤ = 1 := by rw [Matrix.adjugate_mul, L.prop, one_smul]
  have hRadj : R_ℤ * R_ℤ.adjugate = 1 := by rw [Matrix.mul_adjugate, R.prop, one_smul]
  have hM_eq : M = L_ℤ.adjugate * Matrix.diagonal (fun i ↦ (a i : ℤ)) * R_ℤ.adjugate :=
    matrix_isolate_middle L_ℤ M R_ℤ _ hLadj hRadj (by
      simpa only [M, mul_assoc] using heq)
  have h_dvd_entry : ∀ i j : Fin 2, (a 0 : ℤ) ∣ M i j := by
    intro i j
    rw [hM_eq]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply dvd_add
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl _) _) _
    -- The chain hypothesis is about ℕ-divisibility, but this goal is over ℤ; the `show` names
    -- the cast form so `Int.natCast_dvd_natCast` has something to transport it into.
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
        (show (a 0 : ℤ) ∣ (a 1 : ℤ) from
          Int.natCast_dvd_natCast.mpr (isDvdChain_iff.mp hdiv (Fin.zero_le 1))) _) _
  have h_M00 : M 0 0 = S_ℤ 0 0 := by
    simp [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two]
  have h_M10 : M 1 0 = (p : ℤ) * S_ℤ 1 0 := by
    simp [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have h_cop : IsCoprime (S_ℤ 0 0) (S_ℤ 1 0) := S.isCoprime_col 0
  have h1 : (a 0 : ℤ) ∣ S_ℤ 0 0 := h_M00 ▸ h_dvd_entry 0 0
  have h2 : (a 0 : ℤ) ∣ (p : ℤ) * S_ℤ 1 0 := h_M10 ▸ h_dvd_entry 1 0
  have h_cop_a : IsCoprime (a 0 : ℤ) (S_ℤ 1 0) := h_cop.of_isCoprime_of_dvd_left h1
  exact_mod_cast h_cop_a.dvd_of_dvd_mul_right h2

/-- Determinant balance: if a `T(1,p) · T(1,pᵏ)`-shaped product lies in the double coset
of `diag a`, then `a 0 * a 1 = p ^ (k + 1)`. -/
private lemma diag_entries_mul_eq_pow_succ (p : ℕ) (k : ℕ) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (g₁ g₂ g₃ g₄ : GL (Fin 2) ℚ) (h1 : g₁.val.det = 1) (h2 : g₂.val.det = (p : ℚ))
    (h3 : g₃.val.det = 1) (h4 : g₄.val.det = (p : ℚ) ^ k)
    (SL_La SL_Ra : SpecialLinearGroup (Fin 2) ℤ)
    (h_eq : g₁ * g₂ * (g₃ * g₄) =
      mapGL ℚ SL_La * natDiagGL 2 a * mapGL ℚ SL_Ra) :
    a 0 * a 1 = p ^ (k + 1) := by
  have h_lhs : (g₁ * g₂ * (g₃ * g₄)).val.det = (p : ℚ) ^ (k + 1) := by
    simp only [Units.val_mul, Matrix.det_mul, h1, h2, h3, h4]
    ring
  have h_rhs : (g₁ * g₂ * (g₃ * g₄)).val.det = (a 0 : ℚ) * (a 1 : ℚ) := by
    rw [h_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    -- `det_mapGL` is about the *unit* determinant, so `← val_det_apply` moves the matrix
    -- determinant into that form before it can fire.
    simp only [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one, natDiagGL_det 2 a ha_pos, Fin.prod_univ_two, one_mul, mul_one]
  exact_mod_cast h_rhs.symm.trans h_lhs

private lemma mulSupport_pp_dvd_p_aux (p : ℕ) (hp : p.Prime)
    (S_mid L' R' : SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (hdiv : IsDvdChain a) (k : ℕ)
    (h_gl : mapGL ℚ L' * natDiagGL 2 (![1, p]) * mapGL ℚ S_mid *
      natDiagGL 2 (![1, p ^ k]) * mapGL ℚ R' = natDiagGL 2 a) : a 0 ∣ p := by
  have h1p : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp [hp.pos]
  have h1pk : ∀ i : Fin 2, 0 < (![1, p ^ k] : Fin 2 → ℕ) i := by
    intro i
    fin_cases i <;> simp [pow_pos hp.pos k]
  have h_int : (L' : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (S_mid : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (R' : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i ↦ (a i : ℤ)) := by
    ext i j
    have h := congr_arg (fun g : GL (Fin 2) ℚ ↦ (↑g : Matrix (Fin 2) (Fin 2) ℚ) i j) h_gl
    simp only [natDiagGL_coe 2 _ ha_pos, natDiagGL_coe 2 _ h1p, natDiagGL_coe 2 _ h1pk,
      Matrix.diagonal_apply, Units.val_mul, mapGL_coe_matrix, Matrix.mul_apply,
      map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, algebraMap_int_eq,
      Int.coe_castRingHom] at h
    simp only [Matrix.diagonal_apply, Matrix.mul_apply]
    exact_mod_cast h
  exact first_invariant_dvd_p_of_product p S_mid a hdiv L' R' k h_int

/-- Divisibility constraint: if a `T(1,p) · T(1,pᵏ)`-shaped product lies in the double
coset of `diag a`, the first invariant `a 0` divides `p`. -/
private lemma mulSupport_pp_dvd_p (p : ℕ) (hp : p.Prime) (k : ℕ) (a : Fin 2 → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hdiv : IsDvdChain a) (D1c D2c i₀_gl j₀_gl : GL (Fin 2) ℚ)
    (SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀ : SpecialLinearGroup (Fin 2) ℤ)
    (hD1_eq : D1c = mapGL ℚ SL_L₁ * natDiagGL 2 (![1, p]) * mapGL ℚ SL_R₁)
    (hD2_eq : D2c = mapGL ℚ SL_L₂ * natDiagGL 2 (![1, p ^ k]) * mapGL ℚ SL_R₂)
    (hi₀ : i₀_gl = mapGL ℚ SL_i₀) (hj₀ : j₀_gl = mapGL ℚ SL_j₀)
    (h_prod_eq_a : i₀_gl * D1c * (j₀_gl * D2c) =
      mapGL ℚ SL_La * natDiagGL 2 a * mapGL ℚ SL_Ra) : a 0 ∣ p := by
  apply mulSupport_pp_dvd_p_aux p hp (SL_R₁ * SL_j₀ * SL_L₂) (SL_La⁻¹ * SL_i₀ * SL_L₁)
    (SL_R₂ * SL_Ra⁻¹) a ha_pos hdiv k
  have hprod : mapGL ℚ SL_i₀ * (mapGL ℚ SL_L₁ * natDiagGL 2 (![1, p]) * mapGL ℚ SL_R₁) *
      (mapGL ℚ SL_j₀ * (mapGL ℚ SL_L₂ * natDiagGL 2 (![1, p ^ k]) * mapGL ℚ SL_R₂)) =
      mapGL ℚ SL_La * natDiagGL 2 a * mapGL ℚ SL_Ra := by
    rwa [← hi₀, ← hj₀, ← hD1_eq, ← hD2_eq]
  have hiso := congr_arg (· * (mapGL ℚ SL_Ra)⁻¹)
    (congr_arg ((mapGL ℚ SL_La)⁻¹ * ·) hprod)
  simp only [mul_assoc, inv_mul_cancel_left] at hiso
  simp only [map_mul, map_inv]
  convert hiso using 1
  group

/-- The two-way case split: determinant balance and the invariant-divisibility force any
support coset of `T(1,p) · T(1,pᵏ)` to be `T(1, p^(k+1))` or `T(p, pᵏ)`. -/
private lemma mulSupport_pp_case_split (p : ℕ) (hp : p.Prime) (k : ℕ) (a : Fin 2 → ℕ)
    (h_det_prod : a 0 * a 1 = p ^ (k + 1)) (h_dvd_p : a 0 ∣ p) :
    diagCoset a = diagCoset (![1, p ^ (k + 1)]) ∨ diagCoset a = diagCoset (![p, p ^ k]) := by
  rcases hp.eq_one_or_self_of_dvd (a 0) h_dvd_p with ha0_1 | ha0_p
  · left
    congr 1
    ext i
    fin_cases i
    · exact ha0_1
    · rw [ha0_1, one_mul] at h_det_prod
      simpa using h_det_prod
  · right
    congr 1
    ext i
    fin_cases i
    · exact ha0_p
    -- `a 1` and the goal's coordinate projection are the same term up to defeq;
    -- no rewrite exposes it, so state the coordinate directly
    · change a 1 = p ^ k
      have h1 : p * a 1 = p ^ (k + 1) := by rwa [ha0_p] at h_det_prod
      refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
      rw [h1, pow_succ]
      ring

end SupportAnalysis

section DegreeCount

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]

/-- Counting degrees through the degree homomorphism: when the product of two double cosets
is supported on exactly two cosets, the multiplicity-weighted degrees of the two outputs
add up to the product of the input degrees. -/
private lemma multiplicity_degree_sum_eq (D₁ D₂ Dout₁ Dout₂ : HeckeCoset Δ H H)
    (hne : Dout₁ ≠ Dout₂)
    (hzero : ∀ A : HeckeCoset Δ H H, A ≠ Dout₁ → A ≠ Dout₂ →
      multiplicity H H H (D₁.rep : G) (D₂.rep : G) (A.rep : G) = 0) :
    multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) * Dout₁.degree +
      multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) * Dout₂.degree =
      D₁.degree * D₂.degree := by
  classical
  have hSC2 : HeckeCosetModule.structureConstants ℤ H H H D₁.rep D₂.rep =
      HeckeCosetModule.single ℤ Dout₁
        (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) : ℤ) +
      HeckeCosetModule.single ℤ Dout₂
        (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) : ℤ) := by
    ext A
    rw [HeckeCosetModule.structureConstants_apply, HeckeCosetModule.add_apply,
      HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
    by_cases h1 : Dout₁ = A
    · rw [ite_eq_left h1, ite_eq_right (h1 ▸ fun h ↦ hne h.symm), add_zero, ← h1]
    · rw [ite_eq_right h1]
      by_cases h2 : Dout₂ = A
      · rw [ite_eq_left h2, zero_add, ← h2]
      · rw [ite_eq_right h2, add_zero,
          hzero A (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm), Nat.cast_zero]
  have h1 : LeftCosetModule.deg Δ H ℤ
      (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      (D₁.degree : ℤ) * D₂.degree := by
    rw [map_mul, LeftCosetModule.deg_single, LeftCosetModule.deg_single]
    simp
  have h2 : LeftCosetModule.deg Δ H ℤ
      (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) : ℤ) * Dout₁.degree +
      (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) : ℤ) * Dout₂.degree := by
    -- `single_mul_single` yields `1 • 1 • …` on the `Module ℤ` instance transported to
    -- `HeckeCosetModule`, which is not the instance `one_smul` picks for `ℤ`, so neither `rw`
    -- nor `simp` matches it. Stating the product `•`-free lets unification supply the instance.
    have hmul : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1 =
        HeckeCosetModule.structureConstants ℤ H H H D₁.rep D₂.rep := by
      rw [HeckeCosetModule.single_mul_single]
      exact (one_smul ℤ _).trans (one_smul ℤ _)
    rw [hmul, hSC2, map_add, LeftCosetModule.deg_single, LeftCosetModule.deg_single]
    simp [mul_comm]
  exact_mod_cast (h1.symm.trans h2).symm

end DegreeCount

section SupportSubset

include hp in
/-- The support of `T(1,p) · T(1,pᵏ)` is contained in `{T(1,p^(k+1)), T(p,pᵏ)}`. -/
private lemma mulSupport_pp_subset (k : ℕ)
    (A : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    (hA : multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)) ((A.rep : GL (Fin 2) ℚ)) ≠ 0) :
    A = diagCoset ![1, p ^ (k + 1)] ∨ A = diagCoset ![p, p ^ k] := by
  classical
  -- the matrix determinant of an `SL₂(ℤ)` element, used four times in stage 4's bookkeeping
  have hdet : ∀ S : SpecialLinearGroup (Fin 2) ℤ, (mapGL ℚ S).val.det = 1 := fun S ↦
    det_eq_one_of_mem_SLnZ 2 ((mem_SLnZ_iff 2).2 ⟨S, rfl⟩)
  -- Stage 1: positivity of the two input diagonals, and a diagonal representative `a` for `A`.
  have h1p_pos : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos]
  have h1pk_pos : ∀ i : Fin 2, 0 < (![1, p ^ k] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos k]
  obtain ⟨a, ha_pos, hdiv, hA_eq⟩ := exists_diagonal_representative A
  -- Stage 2: `A` occurs in the product, so some pair `q` of coset representatives multiplies
  -- into the double coset of `natDiagGL 2 a`; unpack that into an explicit `La · D · Ra`.
  have hmem := (HeckeCoset.mem_image_mulMap_iff (diagCoset ![1, p]).rep
    (diagCoset ![1, p ^ k]).rep A).mpr hA
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨q, hq⟩ := hmem
  have h_prod_mem : ((q.1.out : GL (Fin 2) ℚ) * ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) *
      ((q.2.out : GL (Fin 2) ℚ) * ((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))) ∈
      doubleCoset (natDiagGL 2 a) (SLnZ 2) (SLnZ 2) := by
    have hself : ((q.1.out : GL (Fin 2) ℚ) * ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) *
        ((q.2.out : GL (Fin 2) ℚ) * ((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))) ∈
        (HeckeCoset.mulMap (SLnZ 2) (SLnZ 2) (SLnZ 2)
          (diagCoset ![1, p]).rep (diagCoset ![1, p ^ k]).rep q).toSet := by
      rw [HeckeCoset.mulMap_eq_mk, HeckeCoset.toSet_mk]
      exact mem_doubleCoset_self _ _ _
    rwa [hq, hA_eq, diagCoset_toSet] at hself
  rw [mem_doubleCoset] at h_prod_mem
  obtain ⟨La, hLa, Ra, hRa, h_prod_eq⟩ := h_prod_mem
  -- Stage 3: every `SLnZ 2` element appearing above is `mapGL ℚ` of an honest integral `SL₂`
  -- matrix; name those lifts, and likewise for the two input cosets' own decompositions.
  obtain ⟨SL_La, hSL_La⟩ := (mem_SLnZ_iff 2).mp hLa
  obtain ⟨SL_Ra, hSL_Ra⟩ := (mem_SLnZ_iff 2).mp hRa
  obtain ⟨SL_i₀, hSL_i₀⟩ := (mem_SLnZ_iff 2).mp q.1.out.2
  obtain ⟨SL_j₀, hSL_j₀⟩ := (mem_SLnZ_iff 2).mp q.2.out.2
  obtain ⟨L₁, hL₁, R₁, hR₁, hD1⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (![1, p])
  obtain ⟨SL_L₁, hSL_L₁⟩ := (mem_SLnZ_iff 2).mp hL₁
  obtain ⟨SL_R₁, hSL_R₁⟩ := (mem_SLnZ_iff 2).mp hR₁
  obtain ⟨L₂, hL₂, R₂, hR₂, hD2⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (![1, p ^ k])
  obtain ⟨SL_L₂, hSL_L₂⟩ := (mem_SLnZ_iff 2).mp hL₂
  obtain ⟨SL_R₂, hSL_R₂⟩ := (mem_SLnZ_iff 2).mp hR₂
  have h_prod_eq' : (q.1.out : GL (Fin 2) ℚ) *
      ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) *
      ((q.2.out : GL (Fin 2) ℚ) * ((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)) =
      mapGL ℚ SL_La * natDiagGL 2 a * mapGL ℚ SL_Ra := by
    rw [hSL_La, hSL_Ra]
    exact h_prod_eq
  -- Stage 4: determinants. Both sides of the product have determinant `p^(k+1)`, which pins
  -- `a 0 * a 1`; the four `hdet` uses discharge the `SL₂` factors' determinants.
  have h_det := diag_entries_mul_eq_pow_succ p k a ha_pos (q.1.out : GL (Fin 2) ℚ)
    ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) (q.2.out : GL (Fin 2) ℚ)
    ((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)
    (by rw [← hSL_i₀]; exact hdet SL_i₀)
    (by rw [hD1, ← hSL_L₁, ← hSL_R₁, Units.val_mul, Units.val_mul, Matrix.det_mul,
          Matrix.det_mul, hdet, hdet, natDiagGL_det 2 _ h1p_pos]
        simp [Fin.prod_univ_two])
    (by rw [← hSL_j₀]; exact hdet SL_j₀)
    (by rw [hD2, ← hSL_L₂, ← hSL_R₂, Units.val_mul, Units.val_mul, Matrix.det_mul,
          Matrix.det_mul, hdet, hdet, natDiagGL_det 2 _ h1pk_pos]
        simp [Fin.prod_univ_two])
    SL_La SL_Ra h_prod_eq'
  -- Stage 5: the first invariant factor divides `p`, because conjugating the middle matrix
  -- keeps it integral. With `a 0 * a 1 = p^(k+1)` that leaves only the two claimed cosets.
  have h_dvd := mulSupport_pp_dvd_p p hp k a ha_pos hdiv
    ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) ((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)
    (q.1.out : GL (Fin 2) ℚ) (q.2.out : GL (Fin 2) ℚ)
    SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀
    (by rw [hD1, hSL_L₁, hSL_R₁]) (by rw [hD2, hSL_L₂, hSL_R₂])
    hSL_i₀.symm hSL_j₀.symm h_prod_eq'
  rw [hA_eq]
  exact mulSupport_pp_case_split p hp k a h_det h_dvd

include hp in
/-- The two support cosets are distinct: their invariant factors differ at the top. -/
private lemma diagCoset_one_prime_pow_succ_ne (k : ℕ) (hk : 0 < k) :
    diagCoset (![1, p ^ (k + 1)] : Fin 2 → ℕ) ≠ diagCoset (![p, p ^ k] : Fin 2 → ℕ) := by
  intro heq
  have ha := eq_of_diagCoset_eq
    (fun i : Fin 2 ↦ by fin_cases i <;> simp [pow_pos hp.pos])
    (fun i : Fin 2 ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (isDvdChain_iff.mpr fun i j' hij ↦ by
      fin_cases i <;> fin_cases j' <;> first | exact absurd hij (by decide) | simp)
    (isDvdChain_iff.mpr fun i j' hij ↦ by
      fin_cases i <;> fin_cases j' <;>
        first
        | exact absurd hij (by decide)
        | simp [dvd_pow_self p (show k ≠ 0 by omega)])
    heq
  exact hp.one_lt.ne' (by simpa using (congr_fun ha 0).symm)

/-- Arithmetic core, `k ≥ 2`: the degree balance forces `m₁ = 1` and `m₂ = P`. -/
private lemma m1_eq_one_and_m2_eq_of_two_le (P m1 m2 : ℤ) (k : ℕ) (hk2 : 2 ≤ k)
    (hP : 2 ≤ P) (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ k * (P + 1)) + m2 * (P ^ (k - 2) * (P + 1)) =
      (P + 1) * (P ^ (k - 1) * (P + 1))) :
    m1 = 1 ∧ m2 = P := by
  have hpk : P ^ k = P ^ (k - 2) * P ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpk1 : P ^ (k - 1) = P ^ (k - 2) * P := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have h_eq : m1 * P ^ 2 + m2 = P * (P + 1) := by
    have h := h_deg
    rw [hpk, hpk1] at h
    have key : P ^ (k - 2) * (P + 1) ≠ 0 := by positivity
    have hcancel := mul_right_cancel₀ key (show
      (m1 * P ^ 2 + m2) * (P ^ (k - 2) * (P + 1)) =
      (P * (P + 1)) * (P ^ (k - 2) * (P + 1)) by nlinarith)
    linarith
  have h_m1_eq : m1 = 1 := by
    have h_le : m1 * P ^ 2 ≤ P ^ 2 + P := by linarith
    nlinarith [show P ^ 2 ≥ 4 by nlinarith]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_eq; linarith⟩

/-- Arithmetic core, `k = 1`: the degree balance forces `m₁ = 1` and `m₂ = P + 1`. -/
private lemma m1_eq_one_and_m2_eq_of_eq_one (P m1 m2 : ℤ) (hP : 2 ≤ P)
    (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ 1 * (P + 1)) + m2 * 1 = (P + 1) * (P + 1)) :
    m1 = 1 ∧ m2 = P + 1 := by
  have h_m1_eq : m1 = 1 := by nlinarith [mul_self_nonneg (P - 1)]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_deg; nlinarith⟩

include hp in
/-- The diagonal elements multiply as expected: `diag(1, p) · diag(1, pᵏ) = diag(1, p^(k+1))`. -/
private lemma natDiagGL_one_p_mul_one_prime_pow (k : ℕ) :
    natDiagGL 2 (![1, p]) * natDiagGL 2 (![1, p ^ k]) = natDiagGL 2 (![1, p ^ (k + 1)]) := by
  rw [natDiagGL_mul 2 _ _ (fun i ↦ by fin_cases i <;> simp [hp.pos])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos k])]
  exact congrArg (natDiagGL 2) (funext fun i ↦ by
    fin_cases i <;> simp [Pi.mul_apply, pow_succ'])

include hp in
/-- `T(1, p^(k+1))` genuinely occurs in `T(1,p) · T(1,pᵏ)`: its representative is the product
of the two representatives, up to `SL₂(ℤ)` factors on either side. -/
private lemma multiplicity_one_prime_pow_succ_pos (k : ℕ) :
    0 < multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ (k + 1)]).rep : GL (Fin 2) ℚ)) := by
  refine Nat.pos_of_ne_zero (multiplicity_ne_zero_iff.mpr ?_)
  obtain ⟨L₁, hL₁, R₁, hR₁, hD1⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (![1, p])
  obtain ⟨L₂, hL₂, R₂, hR₂, hD2⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (![1, p ^ k])
  obtain ⟨L, hL, R, hR, hD⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul (![1, p ^ (k + 1)])
  rw [mem_doubleCoset]
  refine ⟨L * L₁⁻¹ * ((diagCoset ![1, p]).rep : GL (Fin 2) ℚ) * (R₁⁻¹ * L₂⁻¹),
    mem_doubleCoset.mpr ⟨L * L₁⁻¹,
      (SLnZ 2).mul_mem hL ((SLnZ 2).inv_mem hL₁),
      R₁⁻¹ * L₂⁻¹,
      (SLnZ 2).mul_mem ((SLnZ 2).inv_mem hR₁) ((SLnZ 2).inv_mem hL₂), rfl⟩,
    R₂⁻¹ * R, (SLnZ 2).mul_mem ((SLnZ 2).inv_mem hR₂) hR, ?_⟩
  rw [hD, hD1, hD2, ← natDiagGL_one_p_mul_one_prime_pow p hp k]
  group

include hp in
/-- The multiplicities in `T(1,p) · T(1,pᵏ)`: the coset `T(1, p^(k+1))` appears once, and
`T(p, pᵏ)` appears `p + 1` times for `k = 1` and `p` times for `k ≥ 2`. -/
private lemma multiplicity_values (k : ℕ) (hk : 0 < k) :
    multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ (k + 1)]).rep : GL (Fin 2) ℚ)) = 1 ∧
    multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
      (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))
      (((diagCoset ![p, p ^ k]).rep : GL (Fin 2) ℚ)) =
      if k = 1 then p + 1 else p := by
  classical
  set m1 := multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
    (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
    (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))
    (((diagCoset ![1, p ^ (k + 1)]).rep : GL (Fin 2) ℚ)) with hm1_def
  set m2 := multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
    (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
    (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ))
    (((diagCoset ![p, p ^ k]).rep : GL (Fin 2) ℚ)) with hm2_def
  have h_ne := diagCoset_one_prime_pow_succ_ne p hp k hk
  have h_zero : ∀ A : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2),
      A ≠ diagCoset ![1, p ^ (k + 1)] → A ≠ diagCoset ![p, p ^ k] →
      multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
        (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)) ((A.rep : GL (Fin 2) ℚ)) = 0 := by
    intro A h1 h2
    by_contra h0
    exact ((mulSupport_pp_subset p hp k A h0).elim h1 h2)
  have h_deg := multiplicity_degree_sum_eq (diagCoset ![1, p]) (diagCoset ![1, p ^ k])
    (diagCoset ![1, p ^ (k + 1)]) (diagCoset ![p, p ^ k]) h_ne h_zero
  rw [← hm1_def, ← hm2_def] at h_deg
  -- All three degrees are the `i = 0` case of `degree_diagCoset_prime_pow`; `simpa` absorbs
  -- the `p ^ 0 = 1` and `0 + j = j` normalisations.
  rw [show (diagCoset (![1, p] : Fin 2 → ℕ)).degree = p ^ 0 * (p + 1) by
      simpa using degree_diagCoset_prime_pow p hp 0 1 one_pos,
    show (diagCoset (![1, p ^ k] : Fin 2 → ℕ)).degree = p ^ (k - 1) * (p + 1) by
      simpa using degree_diagCoset_prime_pow p hp 0 k hk,
    show (diagCoset (![1, p ^ (k + 1)] : Fin 2 → ℕ)).degree = p ^ k * (p + 1) by
      simpa using degree_diagCoset_prime_pow p hp 0 (k + 1) (by omega)] at h_deg
  have hm1_pos : 0 < m1 := multiplicity_one_prime_pow_succ_pos p hp k
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  by_cases hk1 : k = 1
  · subst hk1
    -- `![p, p ^ 1]` is the constant vector, so the generic `degree_diagCoset_const` applies.
    rw [show (![p, p ^ 1] : Fin 2 → ℕ) = fun _ ↦ p from by funext i; fin_cases i <;> simp,
      degree_diagCoset_const 2 p] at h_deg
    have h_degZ : (m1 : ℤ) * ((p : ℤ) ^ 1 * ((p : ℤ) + 1)) + (m2 : ℤ) * 1 =
        ((p : ℤ) + 1) * ((p : ℤ) + 1) := by
      have := h_deg
      push_cast at this ⊢
      norm_num at this ⊢
      linarith
    obtain ⟨h1, h2⟩ := m1_eq_one_and_m2_eq_of_eq_one (p : ℤ) (m1 : ℤ) (m2 : ℤ) hp2
      (by exact_mod_cast hm1_pos) (by positivity) h_degZ
    simp only [ite_true]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have hk2 : 2 ≤ k := by omega
    -- The `i = 1` case of `degree_diagCoset_prime_pow`, re-indexed from `1 + (k - 1)` to `k`.
    rw [show (diagCoset (![p, p ^ k] : Fin 2 → ℕ)).degree = p ^ (k - 2) * (p + 1) by
        have h := degree_diagCoset_prime_pow p hp 1 (k - 1) (by omega)
        rw [show 1 + (k - 1) = k by omega, pow_one] at h
        rw [h, show k - 1 - 1 = k - 2 by omega]] at h_deg
    have h_degZ : (m1 : ℤ) * ((p : ℤ) ^ k * ((p : ℤ) + 1)) +
        (m2 : ℤ) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) =
        ((p : ℤ) + 1) * ((p : ℤ) ^ (k - 1) * ((p : ℤ) + 1)) := by
      have := h_deg
      zify at this
      ring_nf at this ⊢
      linarith
    obtain ⟨h1, h2⟩ := m1_eq_one_and_m2_eq_of_two_le (p : ℤ) (m1 : ℤ) (m2 : ℤ) k hk2 hp2
      (by exact_mod_cast hm1_pos) (by positivity) h_degZ
    simp only [hk1, ite_false]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

include hp in
/-- **Shimura, Theorem 3.24(5)**: `T(p) · T(1, pᵏ) = T(1, p^(k+1)) + m · T(p, pᵏ)`, where
the multiplicity `m` is `p + 1` for `k = 1` and `p` for `k ≥ 2`. -/
theorem heckeT_prime_mul_heckeTDiag_one_prime_pow (k : ℕ) :
    heckeT ⟨p, hp.pos⟩ * heckeTDiag 1 (p ^ k) =
      heckeTDiag 1 (p ^ (k + 1)) +
        (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) • heckeTDiag p (p ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `T(p) · T(1,1) = T(p) = T(1,p)`, and `T(p,1) = 0` because `p ∤ 1`
    have hp1 : heckeTDiag p 1 = 0 :=
      heckeTDiag_eq_zero fun h ↦ hp.ne_one (Nat.dvd_one.mp h.2.2)
    simp [heckeT_prime p hp, hp1]
  classical
  obtain ⟨hm1, hm2⟩ := multiplicity_values p hp k hk
  have hne := diagCoset_one_prime_pow_succ_ne p hp k hk
  have hzero : ∀ A : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2),
      A ≠ diagCoset ![1, p ^ (k + 1)] → A ≠ diagCoset ![p, p ^ k] →
      multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (((diagCoset ![1, p]).rep : GL (Fin 2) ℚ))
        (((diagCoset ![1, p ^ k]).rep : GL (Fin 2) ℚ)) ((A.rep : GL (Fin 2) ℚ)) = 0 := by
    intro A h1 h2
    by_contra h0
    exact ((mulSupport_pp_subset p hp k A h0).elim h1 h2)
  rw [heckeT_prime p hp,
    heckeTDiag_eq_diagElem one_pos hp.pos (one_dvd _),
    heckeTDiag_eq_diagElem one_pos (pow_pos hp.pos k) (one_dvd _),
    heckeTDiag_eq_diagElem one_pos (pow_pos hp.pos (k + 1)) (one_dvd _),
    heckeTDiag_eq_diagElem hp.pos (pow_pos hp.pos k) (dvd_pow_self p (by omega))]
  -- As in `multiplicity_degree_sum_eq`, the `1 • 1 •` that `single_mul_single` produces sits on
  -- the transported `Module ℤ` instance, which `one_smul` does not match by `rw`/`simp`; a
  -- `•`-free restatement lets unification supply it.
  have hmul : HeckeCosetModule.single ℤ (diagCoset (![1, p] : Fin 2 → ℕ)) 1 *
      HeckeCosetModule.single ℤ (diagCoset (![1, p ^ k] : Fin 2 → ℕ)) 1 =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (diagCoset (![1, p] : Fin 2 → ℕ)).rep (diagCoset (![1, p ^ k] : Fin 2 → ℕ)).rep := by
    rw [HeckeCosetModule.single_mul_single]
    exact (one_smul ℤ _).trans (one_smul ℤ _)
  rw [diagElem_def, diagElem_def, diagElem_def, diagElem_def, hmul]
  ext A
  rw [HeckeCosetModule.structureConstants_apply, HeckeCosetModule.add_apply]
  -- The `ℤ`-action here reaches `HeckeCosetModule` by a different instance path than the
  -- transported `Module R` that `HeckeCosetModule.smul_apply` is stated for, so `rw` and
  -- `simp only` both fail to match it. Naming the instance in a `have` applies the public
  -- lemma anyway, which is why no private restatement is needed.
  have hsmul : ((if k = 1 then (p : ℤ) + 1 else (p : ℤ)) •
      HeckeCosetModule.single ℤ (diagCoset (![p, p ^ k] : Fin 2 → ℕ)) 1) A
      = (if k = 1 then (p : ℤ) + 1 else (p : ℤ)) *
        HeckeCosetModule.single ℤ (diagCoset (![p, p ^ k] : Fin 2 → ℕ)) 1 A :=
    HeckeCosetModule.smul_apply _ _ _
  rw [hsmul, HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
  by_cases h1 : diagCoset (![1, p ^ (k + 1)] : Fin 2 → ℕ) = A
  · have h12 : diagCoset (![p, p ^ k] : Fin 2 → ℕ) ≠ A := fun h ↦ hne (h1.trans h.symm)
    rw [ite_eq_left h1, ite_eq_right h12, mul_zero, add_zero, ← h1, hm1, Nat.cast_one]
  · rw [ite_eq_right h1]
    by_cases h2 : diagCoset (![p, p ^ k] : Fin 2 → ℕ) = A
    · rw [ite_eq_left h2, mul_one, zero_add, ← h2, hm2]
      split_ifs <;> push_cast <;> ring
    · rw [ite_eq_right h2, mul_zero, add_zero,
        hzero A (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm), Nat.cast_zero]

end SupportSubset

include hp in
/-- The characteristic product rule in simp normal form:
`T(1, p) · T(1, pᵏ) = T(1, p^(k+1)) + m · T(p, pᵏ)`.

`heckeT_prime_mul_heckeTDiag_one_prime_pow` states the same identity with `T(p)` on the left,
but `@[simp] heckeT_prime` rewrites that `T(p)` to `T(1, p)` first, so the rule can never fire
during simplification. This restatement is the form simp actually meets, and carries the
attribute. -/
@[simp]
theorem heckeTDiag_one_prime_mul_heckeTDiag_one_prime_pow (k : ℕ) :
    heckeTDiag 1 p * heckeTDiag 1 (p ^ k) =
      heckeTDiag 1 (p ^ (k + 1)) +
        (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) • heckeTDiag p (p ^ k) := by
  rw [← heckeT_prime p hp]
  exact heckeT_prime_mul_heckeTDiag_one_prime_pow p hp k


end HeckeRing.GL2
