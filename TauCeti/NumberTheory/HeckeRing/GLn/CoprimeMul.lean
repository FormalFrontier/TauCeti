/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

import Mathlib.LinearAlgebra.Matrix.Integer
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.CongruenceSplit
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Support

/-!
# Coprime multiplication in the `GL_n` Hecke ring

One row of the multiplication table of the integral Hecke ring of the arithmetic Hecke
triple (Shimura, Proposition 3.16): when the determinants `∏ aᵢ`, `∏ bᵢ` are coprime, the
product of the two diagonal double cosets is again a single diagonal coset,
`T(a) · T(b) = T(a * b)`.

The two levels differ in what they assume. The **set-level** results — the double-coset
statements and their supporting lemmas — carry `∀ i, 0 < a i` explicitly, because
`natDiagGL` sends a tuple with a zero entry to its junk value `1` and those statements are
about genuine diagonal representatives. The **ring-level** theorem
`diagElem_mul_of_coprime` needs no positivity at all: on a tuple with a zero entry both
sides degenerate, and coprimality forces the *other* tuple to be all ones (a zero entry makes
that determinant `0`, and `Nat.Coprime 0 m` holds only for `m = 1`), so the identity survives.
It does assume `[NeZero n]`, which is what the arithmetic Hecke triple instance — and hence
multiplication in `IntegralHeckeRing n` — requires.

The scalar row (Shimura 3.17) lives in `GLn/ScalarMul.lean`.

The coprime case runs on a Chinese-remainder factorization of `SL_n(ℤ)`: modulo coprime
`p`, `q` an element splits as a product of one element congruent to the identity mod `p` and
one congruent to the identity mod `q`
(`Matrix.SpecialLinearGroup.exists_mul_modEq_one_of_coprime`), which is what makes the two
diagonal sandwiches commute past each other.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main results

* `HeckeRing.GLn.mul_mem_doubleCoset_of_coprime`: the set-level statement — for **positive**
  tuples with coprime determinants, a product of representatives lies in the double coset of
  the product tuple.
* `HeckeRing.GLn.diagElem_mul_of_coprime`: the ring-level statement — `T(a) · T(b) = T(a * b)`
  from **coprimality alone**, given `[NeZero n]`; the zero-entry case degenerates as described
  above.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16.
-/

public section

open Matrix HeckeRing DoubleCoset Finset Matrix.SpecialLinearGroup
open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section Conjugation

/-! ## Conjugating congruent elements across the diagonal

An element of `SL_n(ℤ)` congruent to `1` modulo the full diagonal product conjugates
across `natDiagGL n a` — on either side — to an integral matrix of determinant one. -/

private lemma conjugate_congruent_mem_SLnZ (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      mapGL ℚ σ = natDiagGL n a * mapGL ℚ τ * (natDiagGL n a)⁻¹ := by
  have hdvd : ∀ i j, (a j : ℤ) ∣ (a i : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (by simpa [hij] using hcong i j)) _
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (a i : ℤ) * τ.val i j / (a j : ℤ)
  set diag_a := Matrix.diagonal fun i ↦ (a i : ℤ)
  have h_int_eq : diag_a * τ.val = M * diag_a := by
    ext i j
    simpa only [diag_a, M, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply] using
      (Int.ediv_mul_cancel (hdvd i j)).symm
  have h_det_ne : diag_a.det ≠ 0 := by
    simpa only [diag_a, Matrix.det_diagonal] using
      ne_of_gt (Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (ha i))
  have hM_det : M.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, mul_one] at h
    exact (mul_left_cancel₀ h_det_ne (by rwa [mul_one, mul_comm])).symm
  refine ⟨⟨M, hM_det⟩, ?_⟩
  have h_Q_eq : natDiagGL n a * mapGL ℚ τ =
      mapGL ℚ (⟨M, hM_det⟩ : SpecialLinearGroup (Fin n) ℤ) * natDiagGL n a := by
    apply Units.ext
    simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n a ha]
    have h_diag_map : (Matrix.diagonal fun i ↦ (a i : ℤ)).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal fun i ↦ (a i : ℚ) := Matrix.diagonal_map (by simp)
    have hmap : (↑(mapGL ℚ (⟨M, hM_det⟩ : SpecialLinearGroup (Fin n) ℤ)) :
        Matrix (Fin n) (Fin n) ℚ) = M.map ⇑(Int.castRingHom ℚ) :=
      mapGL_coe_matrix _
    rw [← h_diag_map]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq, Matrix.map_mul, hmap]
  exact eq_mul_inv_iff_mul_eq.mpr h_Q_eq.symm

private lemma inv_conjugate_congruent_mem_SLnZ (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      mapGL ℚ σ = (natDiagGL n b)⁻¹ * mapGL ℚ τ * natDiagGL n b := by
  have hdvd : ∀ i j, (b i : ℤ) ∣ (b j : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        (by simpa [hij] using hcong i j)) _
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (b j : ℤ) * τ.val i j / (b i : ℤ)
  set diag_b := Matrix.diagonal fun i ↦ (b i : ℤ)
  have h_int_eq : τ.val * diag_b = diag_b * N := by
    ext i j
    simp only [diag_b, N, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    calc τ.val i j * (b j : ℤ) = (b j : ℤ) * τ.val i j := mul_comm _ _
      _ = (b j : ℤ) * τ.val i j / (b i : ℤ) * (b i : ℤ) :=
          (Int.ediv_mul_cancel (hdvd i j)).symm
      _ = (b i : ℤ) * ((b j : ℤ) * τ.val i j / (b i : ℤ)) := mul_comm _ _
  have h_det_ne : diag_b.det ≠ 0 := by
    simpa only [diag_b, Matrix.det_diagonal] using
      ne_of_gt (Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (hb i))
  have hN_det : N.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, one_mul] at h
    exact (mul_left_cancel₀ h_det_ne (by rwa [mul_one])).symm
  refine ⟨⟨N, hN_det⟩, ?_⟩
  have h_Q_eq : natDiagGL n b * mapGL ℚ (⟨N, hN_det⟩ : SpecialLinearGroup (Fin n) ℤ) =
      mapGL ℚ τ * natDiagGL n b := by
    apply Units.ext
    simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n b hb]
    have h_diag_map : (Matrix.diagonal fun i ↦ (b i : ℤ)).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal fun i ↦ (b i : ℚ) := Matrix.diagonal_map (by simp)
    have hmap : (↑(mapGL ℚ (⟨N, hN_det⟩ : SpecialLinearGroup (Fin n) ℤ)) :
        Matrix (Fin n) (Fin n) ℚ) = N.map ⇑(Int.castRingHom ℚ) :=
      mapGL_coe_matrix _
    rw [← h_diag_map]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq, Matrix.map_mul, hmap]
  exact (eq_inv_mul_of_mul_eq h_Q_eq).trans (mul_assoc _ _ _).symm

end Conjugation

section CoprimeCosets

/-- **The set-level coprime product** (Shimura, Proposition 3.16, key step): sandwiching any
`τ ∈ SL_n(ℤ)` between the diagonals of `a` and `b` stays inside the double coset of the
diagonal of `a * b`, when the determinants are coprime. -/
lemma mul_mem_doubleCoset_of_coprime (a b : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) (τ : SpecialLinearGroup (Fin n) ℤ) :
    natDiagGL n a * mapGL ℚ τ * natDiagGL n b ∈
      doubleCoset (natDiagGL n (a * b) : GL (Fin n) ℚ) (SLnZ n) (SLnZ n) := by
  obtain ⟨τ₁, τ₂, hτ, hτ₁, hτ₂⟩ :=
    exists_mul_modEq_one_of_coprime (∏ i, a i) (∏ i, b i) hcop τ
  have hτ₁_cong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := fun i j ↦ by
    rw [← Nat.cast_prod]; exact hτ₁ i j
  obtain ⟨σ₁, hσ₁⟩ := conjugate_congruent_mem_SLnZ n a ha_pos τ₁ hτ₁_cong
  have hτ₂_cong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := fun i j ↦ by
    rw [← Nat.cast_prod]; exact hτ₂ i j
  obtain ⟨σ₂, hσ₂⟩ := inv_conjugate_congruent_mem_SLnZ n b hb_pos τ₂ hτ₂_cong
  rw [mem_doubleCoset]
  refine ⟨mapGL ℚ σ₁, coe_mem_SLnZ n σ₁, mapGL ℚ σ₂, coe_mem_SLnZ n σ₂, ?_⟩
  have hσ₁' : natDiagGL n a * mapGL ℚ τ₁ = mapGL ℚ σ₁ * natDiagGL n a := by
    rw [hσ₁]; group
  have hσ₂' : mapGL ℚ τ₂ * natDiagGL n b = natDiagGL n b * mapGL ℚ σ₂ := by
    rw [hσ₂]; group
  rw [hτ, map_mul (mapGL ℚ)]
  calc natDiagGL n a * (mapGL ℚ τ₁ * mapGL ℚ τ₂) * natDiagGL n b
      = natDiagGL n a * mapGL ℚ τ₁ * (mapGL ℚ τ₂ * natDiagGL n b) := by group
    _ = natDiagGL n a * mapGL ℚ τ₁ * (natDiagGL n b * mapGL ℚ σ₂) := by rw [hσ₂']
    _ = mapGL ℚ σ₁ * natDiagGL n a * (natDiagGL n b * mapGL ℚ σ₂) := by rw [hσ₁']
    _ = mapGL ℚ σ₁ * (natDiagGL n a * natDiagGL n b) * mapGL ℚ σ₂ := by group
    _ = mapGL ℚ σ₁ * natDiagGL n (a * b) * mapGL ℚ σ₂ := by
        rw [natDiagGL_mul n a b ha_pos hb_pos]

variable [NeZero n]

private lemma mulMap_coprime_eq (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (p : DecompQuotient (SLnZ n) (SLnZ n) (((diagCoset a).rep : GL (Fin n) ℚ)) ×
      DecompQuotient (SLnZ n) (SLnZ n) (((diagCoset b).rep : GL (Fin n) ℚ))) :
    HeckeCoset.mulMap (SLnZ n) (SLnZ n) (SLnZ n) (diagCoset a).rep (diagCoset b).rep p =
      diagCoset (a * b) := by
  obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul a
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  obtain ⟨σ, hσ⟩ := (mem_SLnZ_iff n).mp
    ((SLnZ n).mul_mem ((SLnZ n).mul_mem hh₂a p.2.out.2) hh₁b)
  have h_cop := mul_mem_doubleCoset_of_coprime n a b ha_pos hb_pos hcop σ
  rw [hσ, mem_doubleCoset] at h_cop
  obtain ⟨hc₁, hhc₁, hc₂, hhc₂, h_eq⟩ := h_cop
  have hprod : (p.1.out : GL (Fin n) ℚ) * ((diagCoset a).rep : GL (Fin n) ℚ) *
      ((p.2.out : GL (Fin n) ℚ) * ((diagCoset b).rep : GL (Fin n) ℚ)) =
      ((p.1.out : GL (Fin n) ℚ) * h₁a * hc₁) * natDiagGL n (a * b) * (hc₂ * h₂b) := by
    -- name the coerced representatives so the rewrites do not abstract the sealed `rep`
    set σ₁ := (p.1.out : GL (Fin n) ℚ)
    set σ₂ := (p.2.out : GL (Fin n) ℚ)
    rw [hδa, hδb]
    calc σ₁ * (h₁a * natDiagGL n a * h₂a) * (σ₂ * (h₁b * natDiagGL n b * h₂b))
        = σ₁ * h₁a * (natDiagGL n a * (h₂a * σ₂ * h₁b) * natDiagGL n b) * h₂b := by group
      _ = σ₁ * h₁a * (hc₁ * natDiagGL n (a * b) * hc₂) * h₂b := by rw [h_eq]
      _ = σ₁ * h₁a * hc₁ * natDiagGL n (a * b) * (hc₂ * h₂b) := by group
  rw [HeckeCoset.mulMap_eq_mk]
  exact (HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr
    ⟨(p.1.out : GL (Fin n) ℚ) * h₁a * hc₁,
      (SLnZ n).mul_mem ((SLnZ n).mul_mem p.1.out.2 hh₁a) hhc₁,
      hc₂ * h₂b, (SLnZ n).mul_mem hhc₂ hh₂b, hprod⟩)).trans (diagCoset_def _).symm

end CoprimeCosets

section CoprimeIntegrality

/-- A determinant-one rational matrix whose entries clear coprime denominators `pa` and `pb`
is integral, hence lies in `SL_n(ℤ)`. -/
private lemma mem_SLnZ_of_coprime_scaling (C : GL (Fin n) ℚ)
    (pa pb : ℕ) (hcop : Nat.Coprime pa pb) (h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1)
    (h_a : ∀ i j, ∃ z : ℤ, (pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z)
    (h_b : ∀ i j, ∃ z : ℤ, (pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z) :
    C ∈ SLnZ n := by
  have hcopZ : IsCoprime (pa : ℤ) (pb : ℤ) := by exact_mod_cast hcop.isCoprime
  obtain ⟨s, t, hst⟩ := hcopZ
  have h_int : ∀ i j, ∃ z : ℤ, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = (z : ℚ) := by
    intro i j
    obtain ⟨za, hza⟩ := h_a i j
    obtain ⟨zb, hzb⟩ := h_b i j
    refine ⟨s * za + t * zb, ?_⟩
    have hst_Q : (s : ℚ) * (pa : ℚ) + (t : ℚ) * (pb : ℚ) = 1 := by exact_mod_cast hst
    have h1 : (↑C : Matrix (Fin n) (Fin n) ℚ) i j =
        s * ((pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) +
        t * ((pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) := by
      have h2 := congr_arg (· * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) hst_Q
      simp only [add_mul, one_mul] at h2
      linarith
    rw [h1, hza, hzb]
    push_cast
    ring
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (h_int i j).choose
  have hN_eq : ∀ i j, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ((N i j : ℤ) : ℚ) :=
    fun i j ↦ (h_int i j).choose_spec
  have hN_cast : (↑C : Matrix (Fin n) (Fin n) ℚ) = N.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simpa only [N, Matrix.of_apply, Matrix.map_apply] using hN_eq i j
  have hN_detQ : ((N.det : ℤ) : ℚ) = 1 := by rw [Int.cast_det N, ← hN_cast, h_det]
  have hN_det : N.det = 1 := by exact_mod_cast hN_detQ
  refine (mem_SLnZ_iff n).mpr ⟨⟨N, hN_det⟩, ?_⟩
  apply Units.ext
  exact hN_cast.symm

/-- Conjugating an integral matrix by the inverse-side diagonal scales entries by at worst
the full diagonal product. -/
private lemma diagConj_scaling (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (σ : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (a k : ℚ)) *
      ((↑((natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := (natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a with hC_def
  have h_mul : natDiagGL n a * C = mapGL ℚ σ * natDiagGL n a := by
    rw [hC_def, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have h_entry := congr_arg (fun g : GL (Fin n) ℚ ↦ (↑g : Matrix (Fin n) (Fin n) ℚ) i j) h_mul
  simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n a ha,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply] at h_entry
  have hai_ne : (a i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha i).ne'
  have h_dvd : (a i : ℤ) ∣ ∏ k, (a k : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨(∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ), ?_⟩
  have hsplit : (∏ k, (a k : ℚ)) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j =
      (∏ k, (a k : ℚ)) / (a i : ℚ) * ((a i : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) := by
    field_simp
  have hregroup : ((∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ) : ℤ) =
      (∏ k, (a k : ℤ)) / (a i : ℤ) * (σ.val i j * (a j : ℤ)) := by ring
  rw [hsplit, h_entry, hregroup]
  push_cast [Int.cast_div h_dvd
    (Int.cast_ne_zero.mpr (ne_of_gt (Int.natCast_pos.mpr (ha i))))]
  ring

/-- Sandwiching by the diagonal and its inverse scales entries by at worst the full
diagonal product, uniformly in the three integral factors. -/
private lemma diagSandwich_scaling (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (F G E : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (b k : ℚ)) *
      ((↑(mapGL ℚ F * natDiagGL n b * mapGL ℚ G * (natDiagGL n b)⁻¹ * mapGL ℚ E) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := mapGL ℚ F * natDiagGL n b * mapGL ℚ G * (natDiagGL n b)⁻¹ * mapGL ℚ E with hC_def
  set D := natDiagGL n b * mapGL ℚ G * (natDiagGL n b)⁻¹ with hD_def
  have h_C_entry : (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ∑ p, ∑ q,
      (↑(mapGL ℚ F) : Matrix (Fin n) (Fin n) ℚ) i p *
      (↑D : Matrix (Fin n) (Fin n) ℚ) p q *
      (↑(mapGL ℚ E) : Matrix (Fin n) (Fin n) ℚ) q j := by
    have hCFDE : C = mapGL ℚ F * D * mapGL ℚ E := by
      rw [hC_def, hD_def]
      group
    have h2 := congr_arg (fun g : GL (Fin n) ℚ ↦ (↑g : Matrix (Fin n) (Fin n) ℚ) i j) hCFDE
    simp only [Units.val_mul, Matrix.mul_apply] at h2
    rw [h2]
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have h_D_scale : ∀ p q, ∃ z : ℤ,
      (∏ k, (b k : ℚ)) * (↑D : Matrix (Fin n) (Fin n) ℚ) p q = z := by
    intro p q
    have h_D_entry : (↑D : Matrix (Fin n) (Fin n) ℚ) p q =
        (b p : ℚ) * (G.val p q : ℚ) * ((b q : ℚ)⁻¹) := by
      have h_Db : D * natDiagGL n b = natDiagGL n b * mapGL ℚ G := by
        rw [hD_def]
        group
      have h_entry := congr_arg
        (fun g : GL (Fin n) ℚ ↦ (↑g : Matrix (Fin n) (Fin n) ℚ) p q) h_Db
      simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n b hb,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at h_entry
      have hbq_ne : (b q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hb q).ne'
      field_simp at h_entry ⊢
      linarith
    rw [h_D_entry]
    have h_dvd : (b q : ℤ) ∣ ∏ k, (b k : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ q)
    refine ⟨(∏ k, (b k : ℤ)) / (b q : ℤ) * (b p : ℤ) * G.val p q, ?_⟩
    have h_div_eq : (∏ k, (b k : ℚ)) * ((b p : ℚ) * (G.val p q : ℚ) * ((b q : ℚ)⁻¹)) =
        (∏ k, (b k : ℚ)) / (b q : ℚ) * ((b p : ℚ) * (G.val p q : ℚ)) := by
      rw [div_eq_mul_inv]
      ring
    rw [h_div_eq]
    push_cast [Int.cast_div h_dvd (Int.cast_ne_zero.mpr (Int.natCast_ne_zero.mpr (hb q).ne'))]
    ring
  rw [h_C_entry, Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_assoc]
  refine ⟨∑ p, ∑ q, F.val i p * (h_D_scale p q).choose * E.val q j, ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  have hDpq := (h_D_scale p q).choose_spec
  simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply]
  -- name the chosen integer: its `Exists` argument mentions the term being rewritten,
  -- and rewriting under the bare `choose` breaks the motive
  set z := (h_D_scale p q).choose
  have h1 : (∏ k, (b k : ℚ)) * ((F.val i p : ℚ) *
      ((↑D : Matrix (Fin n) (Fin n) ℚ) p q * (E.val q j : ℚ))) =
      (F.val i p : ℚ) * ((∏ k, (b k : ℚ)) * (↑D : Matrix (Fin n) (Fin n) ℚ) p q) *
        (E.val q j : ℚ) := by ring
  rw [h1, hDpq]

/-- The coupling criterion: a diagonal conjugate that also admits a sandwich presentation
with the coprime diagonal is integral. -/
private lemma coprime_coupling_mem_H (a b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (σ F G E : SpecialLinearGroup (Fin n) ℤ)
    (h_eq : (natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a =
      mapGL ℚ F * natDiagGL n b * mapGL ℚ G * (natDiagGL n b)⁻¹ * mapGL ℚ E) :
    (natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a ∈ SLnZ n := by
  set C := (natDiagGL n a)⁻¹ * mapGL ℚ σ * natDiagGL n a with hC_def
  have h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    have hσ_det : (σ.val.map (Int.cast : ℤ → ℚ)).det = 1 := by
      rw [← Int.cast_det, σ.prop, Int.cast_one]
    simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, hC_def, Units.val_mul, Matrix.det_mul]
    rw [hσ_det, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  have h_scale_a : ∀ i j, ∃ z : ℤ,
      (↑(∏ i, a i) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j
    rw [Nat.cast_prod]
    exact diagConj_scaling n a ha σ i j
  have h_scale_b : ∀ i j, ∃ z : ℤ,
      (↑(∏ i, b i) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j
    rw [h_eq, Nat.cast_prod]
    exact diagSandwich_scaling n b hb F G E i j
  exact mem_SLnZ_of_coprime_scaling n C (∏ i, a i) (∏ i, b i) hcop h_det h_scale_a h_scale_b

/-- The conjugated quotient of two first-component representatives is integral: the key
step of the multiplicity bound, coupling the two coset decompositions through `κ`. -/
private lemma out_conj_diagA_mem_H (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (δa δb p₁ p₂ q₁ q₂ h₁a h₂a h₁b h₂b κ : GL (Fin n) ℚ)
    (hh₂a : h₂a ∈ SLnZ n) (hh₁b : h₁b ∈ SLnZ n) (hh₂b : h₂b ∈ SLnZ n)
    (hq₁ : q₁ ∈ SLnZ n) (hq₂ : q₂ ∈ SLnZ n) (hκ : κ ∈ SLnZ n)
    (hδa : δa = h₁a * natDiagGL n a * h₂a) (hδb : δb = h₁b * natDiagGL n b * h₂b)
    (σ' : SpecialLinearGroup (Fin n) ℤ)
    (hσ' : mapGL ℚ σ' = h₁a⁻¹ * (p₂⁻¹ * p₁) * h₁a)
    (hκ_eq : p₂ * δa * (q₂ * δb) * κ = p₁ * δa * (q₁ * δb)) :
    δa⁻¹ * p₂⁻¹ * p₁ * δa ∈ SLnZ n := by
  have h_beta_eq : δa⁻¹ * p₂⁻¹ * p₁ * δa = q₂ * δb * κ * δb⁻¹ * q₁⁻¹ := by
    apply mul_left_cancel (a := p₂ * δa)
    apply mul_right_cancel (b := q₁ * δb)
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    simp only [mul_assoc] at hκ_eq
    exact hκ_eq.symm
  have h_lhs_eq : δa⁻¹ * p₂⁻¹ * p₁ * δa =
      h₂a⁻¹ * ((natDiagGL n a)⁻¹ * mapGL ℚ σ' * natDiagGL n a) * h₂a := by
    rw [hσ']
    conv_lhs => rw [hδa]
    group
  obtain ⟨F_pre, hF_pre⟩ := (mem_SLnZ_iff n).mp ((SLnZ n).mul_mem hq₂ hh₁b)
  obtain ⟨G_pre, hG_pre⟩ := (mem_SLnZ_iff n).mp
    ((SLnZ n).mul_mem ((SLnZ n).mul_mem hh₂b hκ) ((SLnZ n).inv_mem hh₂b))
  obtain ⟨E_pre, hE_pre⟩ := (mem_SLnZ_iff n).mp
    ((SLnZ n).mul_mem ((SLnZ n).inv_mem hh₁b) ((SLnZ n).inv_mem hq₁))
  have h_rhs_eq : q₂ * δb * κ * δb⁻¹ * q₁⁻¹ =
      mapGL ℚ F_pre * natDiagGL n b * mapGL ℚ G_pre *
        (natDiagGL n b)⁻¹ * mapGL ℚ E_pre := by
    rw [hF_pre, hG_pre, hE_pre]
    conv_lhs => rw [hδb]
    group
  obtain ⟨FF, hFF⟩ := (mem_SLnZ_iff n).mp ((SLnZ n).mul_mem hh₂a (coe_mem_SLnZ n F_pre))
  obtain ⟨EE, hEE⟩ := (mem_SLnZ_iff n).mp
    ((SLnZ n).mul_mem (coe_mem_SLnZ n E_pre) ((SLnZ n).inv_mem hh₂a))
  have h_C_eq : (natDiagGL n a)⁻¹ * mapGL ℚ σ' * natDiagGL n a =
      mapGL ℚ FF * natDiagGL n b * mapGL ℚ G_pre *
        (natDiagGL n b)⁻¹ * mapGL ℚ EE := by
    rw [h_lhs_eq, h_rhs_eq] at h_beta_eq
    apply mul_left_cancel (a := h₂a⁻¹)
    apply mul_right_cancel (b := h₂a)
    rw [hFF, hEE]
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
    simp only [mul_assoc] at h_beta_eq
    exact h_beta_eq
  rw [h_lhs_eq]
  exact (SLnZ n).mul_mem ((SLnZ n).mul_mem ((SLnZ n).inv_mem hh₂a)
    (coprime_coupling_mem_H n a b ha_pos hb_pos hcop σ' FF G_pre EE h_C_eq)) hh₂a

variable [NeZero n]

/-- The multiplicity of any double coset in a coprime product is at most one: two
representative pairs with the same product coset have quotient-equal first components by
the coupling criterion, and then equal second components. -/
private lemma multiplicity_coprime_le_one (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i))
    (A : HeckeCoset (posDetInt n) (SLnZ n) (SLnZ n)) :
    multiplicity (SLnZ n) (SLnZ n) (SLnZ n)
      (((diagCoset a).rep : GL (Fin n) ℚ)) (((diagCoset b).rep : GL (Fin n) ℚ))
      ((A.rep : GL (Fin n) ℚ)) ≤ 1 := by
  classical
  obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul a
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb⟩ := exists_rep_diagCoset_eq_mul_natDiagGL_mul b
  rw [multiplicity_def, Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.mpr ?_
  constructor
  set δa' := ((diagCoset a).rep : GL (Fin n) ℚ) with hδa'_def
  set δb' := ((diagCoset b).rep : GL (Fin n) ℚ) with hδb'_def
  rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
  simp only [Set.mem_ofPred_eq] at hp₁ hp₂
  have h12 : ((i₁.out : GL (Fin n) ℚ) * δa' * ((j₁.out : GL (Fin n) ℚ) * δb') :
      GL (Fin n) ℚ ⧸ SLnZ n) = ((i₂.out : GL (Fin n) ℚ) * δa' * ((j₂.out : GL (Fin n) ℚ) *
      δb') : GL (Fin n) ℚ ⧸ SLnZ n) := hp₁.trans hp₂.symm
  rw [QuotientGroup.eq] at h12
  obtain ⟨σ', hσ'⟩ := (mem_SLnZ_iff n).mp
    ((SLnZ n).mul_mem ((SLnZ n).mul_mem ((SLnZ n).inv_mem hh₁a)
      ((SLnZ n).mul_mem ((SLnZ n).inv_mem i₁.out.2) i₂.out.2)) hh₁a)
  obtain rfl : i₁ = i₂ := by
    refine DoubleCoset.mk_out_mul_injective (SLnZ n) (SLnZ n) δa' ?_
    rw [QuotientGroup.eq]
    have hconj := out_conj_diagA_mem_H n a b ha_pos hb_pos hcop δa' δb'
      (i₂.out : GL (Fin n) ℚ) (i₁.out : GL (Fin n) ℚ)
      (j₂.out : GL (Fin n) ℚ) (j₁.out : GL (Fin n) ℚ) h₁a h₂a h₁b h₂b
      (((i₁.out : GL (Fin n) ℚ) * δa' * ((j₁.out : GL (Fin n) ℚ) * δb'))⁻¹ *
        ((i₂.out : GL (Fin n) ℚ) * δa' * ((j₂.out : GL (Fin n) ℚ) * δb')))
      hh₂a hh₁b hh₂b j₂.out.2 j₁.out.2 h12
      (hδa'_def.trans hδa) (hδb'_def.trans hδb) σ' hσ' (by group)
    have hgoal : ((i₁.out : GL (Fin n) ℚ) * δa')⁻¹ * ((i₂.out : GL (Fin n) ℚ) * δa') =
        δa'⁻¹ * (i₁.out : GL (Fin n) ℚ)⁻¹ * (i₂.out : GL (Fin n) ℚ) * δa' := by group
    rw [hgoal]
    exact hconj
  obtain rfl : j₁ = j₂ := DoubleCoset.snd_eq_of_fst_eq hp₁ hp₂
  rfl

/-- Coprime product in the integral `GL_n` Hecke ring (Shimura, Proposition 3.16):
`T(a) · T(b) = T(a * b)` for entrywise positive `a`, `b` whose determinants `∏ aᵢ`, `∏ bᵢ`
are coprime. Positivity is required — without it `natDiagGL` takes its junk value. The
`[NeZero n]` in scope is what multiplication in `IntegralHeckeRing n` needs.

Deliberately **not** `@[simp]`, unlike the parallel scalar theorem `diagElem_const_mul`. The
`simpNF` linter rejects the attribute here — "left-hand side does not simplify, when using the
simp lemma on itself … this usually means that it will never apply" — because the side
condition is coprimality of two products, which `simp` cannot discharge from the bare
left-hand side. `diagElem_const_mul` differs materially: its side conditions are positivity,
which `simp` can discharge. Cite this one explicitly instead.

This is the positive case; the public `diagElem_mul_of_coprime` below reduces to it. -/
private theorem diagElem_mul_of_coprime_of_pos (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i)
    (hb_pos : ∀ i, 0 < b i) (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) :
    diagElem a * diagElem b = diagElem (a * b) :=
  diagElem_mul_of_mulMap_eq _ _ _ (mulMap_coprime_eq n a b ha_pos hb_pos hcop)
    (multiplicity_coprime_le_one n a b ha_pos hb_pos hcop _)

/-- Coprime product in the integral `GL_n` Hecke ring (Shimura, Proposition 3.16):
`T(a) · T(b) = T(a * b)` whenever the determinants `∏ aᵢ`, `∏ bᵢ` are coprime.

Coprimality is the only hypothesis. `natDiagGL` sends a tuple with a zero entry to its junk
value `1`, and coprimality forces the *other* tuple to be all ones there: a zero entry makes
that determinant `0`, and `Nat.Coprime 0 m` holds only for `m = 1`. Both sides then collapse to
the same element. -/
theorem diagElem_mul_of_coprime (a b : Fin n → ℕ)
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) :
    diagElem a * diagElem b = diagElem (a * b) := by
  have hones : ∀ x y : Fin n → ℕ, Nat.Coprime (∏ i, x i) (∏ i, y i) →
      ¬(∀ i, 0 < x i) → ∀ j, y j = 1 := by
    intro x y hc hx j
    obtain ⟨i, hi⟩ := not_forall.mp hx
    have hx0 : (∏ i, x i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (Nat.eq_zero_of_not_pos hi)
    have hy1 : (∏ i, y i) = 1 := (Nat.coprime_zero_left _).mp (hx0 ▸ hc)
    exact Nat.dvd_one.mp (hy1 ▸ Finset.dvd_prod_of_mem y (Finset.mem_univ j))
  by_cases ha_pos : ∀ i, 0 < a i
  · by_cases hb_pos : ∀ i, 0 < b i
    · exact diagElem_mul_of_coprime_of_pos n a b ha_pos hb_pos hcop
    · -- `b` is not positive, so coprimality forces `a` to be all ones
      have ha1 : a = fun _ ↦ 1 := funext (hones b a hcop.symm hb_pos)
      subst ha1
      have hmul : ((fun _ : Fin n ↦ 1) * b) = b := funext fun i ↦ Nat.one_mul (b i)
      rw [hmul, diagElem_one, one_mul]
  · -- `a` is not positive, so coprimality forces `b` to be all ones
    have hb1 : b = fun _ ↦ 1 := funext (hones a b hcop ha_pos)
    subst hb1
    have hmul : (a * fun _ : Fin n ↦ 1) = a := funext fun i ↦ Nat.mul_one (a i)
    rw [hmul, diagElem_one, mul_one]

end CoprimeIntegrality

end HeckeRing.GLn
