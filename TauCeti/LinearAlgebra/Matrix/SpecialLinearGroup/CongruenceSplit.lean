/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Chinese-remainder splitting of `SL(ι, ℤ)`

For coprime moduli `d, d'`, every `τ ∈ SL(ι, ℤ)` — `ι` any finite index type — factors as
`τ₁ * τ₂` with `τ₁ ≡ 1 (mod d)`
and `τ₂ ≡ 1 (mod d')`. The proof is by generators: `τ` is a product of transvections
(`exists_list_transvec_prod`), a single transvection splits by Bézout, and splittings
multiply.

## Main results

* `Matrix.SpecialLinearGroup.exists_mul_modEq_one_of_coprime`: the factorization.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck), where it is the group-theoretic input to the coprime multiplication rule of
the Hecke ring.
-/

public section

open Matrix

namespace Matrix.SpecialLinearGroup

-- `DecidableEq ι` is not a strengthening we chose: `Matrix.SpecialLinearGroup ι ℤ` is itself
-- defined only for `[DecidableEq ι] [Fintype ι]`, so the statements below cannot be written
-- without it. It is not removable by proving things classically inside.
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Chinese-remainder splitting of `SL(ι, ℤ)`

Every `τ ∈ SL(ι, ℤ)` factors as `τ₁ * τ₂` with `τ₁ ≡ 1 mod d` and `τ₂ ≡ 1 mod d'` for
coprime `d, d'`: transvections split by Bézout, and splittings multiply. -/

/-- `σ ≡ 1 (mod d)`, entrywise: every entry of `σ` is congruent mod `d` to the corresponding
entry of the identity matrix. Spelled with divisibility rather than `Int.ModEq` (`≡ [ZMOD d]`)
because the proofs below work with the difference directly; the two are interchangeable via
`Int.modEq_iff_dvd`. -/
private def modEqOne (d : ℕ) (σ : SpecialLinearGroup ι ℤ) : Prop :=
  ∀ i j, (d : ℤ) ∣ (σ.1 i j - if i = j then 1 else 0)

private lemma modEqOne_transvection (d : ℕ) {i j : ι} (hij : i ≠ j) {c : ℤ}
    (hdc : (d : ℤ) ∣ c) : modEqOne d (SpecialLinearGroup.transvection hij c) := by
  intro k l
  rw [SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply,
    add_sub_cancel_left]
  split_ifs with h
  · exact hdc
  · exact dvd_zero _

private lemma transvection_CRT (d d' : ℕ) (hcop : Nat.Coprime d d')
    {i j : ι} (hij : i ≠ j) (c : ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup ι ℤ,
      SpecialLinearGroup.transvection hij c = τ₁ * τ₂ ∧
        modEqOne d τ₁ ∧ modEqOne d' τ₂ := by
  have hbez : ↑(Nat.gcd d d') = (d : ℤ) * Nat.gcdA d d' + ↑d' * Nat.gcdB d d' :=
    Nat.gcd_eq_gcd_ab d d'
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨SpecialLinearGroup.transvection hij (c * d * Nat.gcdA d d'),
    SpecialLinearGroup.transvection hij (c * d' * Nat.gcdB d d'), ?_, ?_, ?_⟩
  · rw [← SpecialLinearGroup.transvection_add]
    congr 1
    linear_combination c * hbez
  · exact modEqOne_transvection d hij ⟨c * Nat.gcdA d d', by ring⟩
  · exact modEqOne_transvection d' hij ⟨c * Nat.gcdB d d', by ring⟩

private lemma modEqOne_one (d : ℕ) : modEqOne d (1 : SpecialLinearGroup ι ℤ) := fun i j ↦ by
  simp [SpecialLinearGroup.coe_one, Matrix.one_apply]

private lemma modEqOne_mul (d : ℕ) (a b : SpecialLinearGroup ι ℤ)
    (ha : modEqOne d a) (hb : modEqOne d b) : modEqOne d (a * b) := by
  intro i j
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h2 : ∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j =
      (∑ k, a.1 i k * b.1 k j) - b.1 i j := by
    simp [sub_mul, Finset.sum_sub_distrib]
  have h3 : (∑ k, a.1 i k * b.1 k j) - (if i = j then 1 else 0) =
      (∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j) +
      (b.1 i j - if i = j then 1 else 0) := by linarith
  rw [h3]
  exact dvd_add (Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_left (ha i k) _) (hb i j)

private lemma modEqOne_conj (d : ℕ) (σ τ : SpecialLinearGroup ι ℤ)
    (hτ : modEqOne d τ) : modEqOne d (σ⁻¹ * τ * σ) := by
  intro i j
  have hassoc : σ⁻¹ * τ * σ = σ⁻¹ * (τ * σ) := by group
  simp only [hassoc, SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h_inv : ∀ i' j', ∑ k : ι, (σ⁻¹).1 i' k * σ.1 k j' =
      if i' = j' then 1 else 0 := by
    intro i' j'
    have hmul : (σ⁻¹).1 * σ.1 = 1 := by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun hmul i') j'
  have h_inner : ∀ k, ∑ l : ι, τ.1 k l * σ.1 l j =
      (∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) + σ.1 k j := by
    intro k
    have h2 : ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j =
        (∑ l, τ.1 k l * σ.1 l j) - σ.1 k j := by
      simp [sub_mul, Finset.sum_sub_distrib]
    linarith
  have h3 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) =
      (∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) +
      (∑ k, (σ⁻¹).1 i k * σ.1 k j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [h_inner k]
    ring
  have h4 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) - (if i = j then 1 else 0) =
      ∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j := by
    rw [h3, h_inv]
    ring
  rw [h4]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right
    (Finset.dvd_sum fun l _ ↦ dvd_mul_of_dvd_left (hτ k l) _) _

/-- Elements admitting a CRT splitting are closed under products: conjugate the second
`d`-part across the first `d'`-part. -/
private lemma crtProd_mul (d d' : ℕ) (a b : SpecialLinearGroup ι ℤ)
    (ha : ∃ p q, a = p * q ∧ modEqOne d p ∧ modEqOne d' q)
    (hb : ∃ p q, b = p * q ∧ modEqOne d p ∧ modEqOne d' q) :
    ∃ p q, a * b = p * q ∧ modEqOne d p ∧ modEqOne d' q := by
  obtain ⟨p₁, q₁, rfl, hp₁, hq₁⟩ := ha
  obtain ⟨p₂, q₂, rfl, hp₂, hq₂⟩ := hb
  refine ⟨p₁ * (q₁ * p₂ * q₁⁻¹), q₁ * q₂, by group, ?_,
    modEqOne_mul d' _ _ hq₁ hq₂⟩
  have h := modEqOne_conj d q₁⁻¹ p₂ hp₂
  rw [inv_inv] at h
  exact modEqOne_mul d _ _ hp₁ h

/-- **Chinese remainder decomposition of `SL(ι, ℤ)`**: for coprime `d, d'`, every element
factors as `τ₁ * τ₂` with `τ₁ ≡ 1 mod d` and `τ₂ ≡ 1 mod d'`. -/
lemma exists_mul_modEq_one_of_coprime (d d' : ℕ) (hcop : Nat.Coprime d d')
    (τ : SpecialLinearGroup ι ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup ι ℤ, τ = τ₁ * τ₂ ∧
      (∀ i j, (d : ℤ) ∣ ((τ₁ : Matrix (ι) (ι) ℤ) i j - if i = j then 1 else 0)) ∧
      (∀ i j, (d' : ℤ) ∣ ((τ₂ : Matrix (ι) (ι) ℤ) i j - if i = j then 1 else 0)) := by
  obtain ⟨T, hT⟩ := SpecialLinearGroup.exists_list_transvec_prod τ
  rw [hT]
  clear hT
  induction T with
  | nil => exact ⟨1, 1, (one_mul 1).symm, modEqOne_one d, modEqOne_one d'⟩
  | cons t T ihT =>
    simp only [List.map_cons, List.prod_cons]
    refine crtProd_mul d d' _ _ ?_ ihT
    obtain ⟨i, j, hij, c⟩ := t
    rw [TransvectionStruct.toSpecialLinearGroup_def ⟨i, j, hij, c⟩]
    exact transvection_CRT d d' hcop hij c

end Matrix.SpecialLinearGroup
