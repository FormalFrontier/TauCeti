/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Normalizing a `ℤᵐ⁰`-valued valuation of a field

The orders `ord_v f` attained by a `ℤᵐ⁰`-valued valuation `v` of a field form a subgroup of `ℤ`,
so they are the multiples of a single natural number, the *index* `Valuation.ordIndex v`; it is
zero exactly when `v` is trivial. Dividing the order by the index produces the *normalization*
`Valuation.normalization v`: the valuation equivalent to `v` whose value group is all of `ℤᵐ⁰`
(the trivial valuation, when `v` is trivial).

This is the operation that turns the restriction of a discrete valuation along a field extension
back into a normalized one, and the index it divides by is the ramification index of that
extension.

## Main definitions

* `Valuation.ordIndex`: the least positive order attained by `v`, and `0` if there is none.
* `Valuation.normalization`: the normalization of `v`.

## Main results

* `Valuation.ordIndex_dvd_ord`: every order attained by `v` is a multiple of the index.
* `Valuation.ordIndex_eq_mul_of_forall_ord_eq`: indices multiply when one order function is a
  positive integral multiple of another.
* `Valuation.ord_normalization_mul_ordIndex`: the order function of `v` is the index times the
  order function of its normalization — the defining relation between the two.
* `Valuation.isEquiv_normalization`: a valuation is equivalent to its normalization; in
  particular the two have the same valuation subring.
* `Valuation.normalization_surjective`: the normalization of a nontrivial valuation is
  surjective.
* `Valuation.IsTrivialOn.normalization`: normalization preserves triviality on a base ring.
-/

public section

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F]

section OrdIndex

/-- The **index** of a `ℤᵐ⁰`-valued valuation of a field: the least positive order it attains,
and `0` when the valuation is trivial. The orders attained by `v` are exactly the multiples of
the index (`Valuation.ordIndex_dvd_ord` and `Valuation.exists_ord_eq_ordIndex`). -/
noncomputable def ordIndex (v : _root_.Valuation F ℤᵐ⁰) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ f : F, ord v f = n}

variable (v : _root_.Valuation F ℤᵐ⁰)

theorem ordIndex_le {n : ℕ} (hn : 0 < n) {f : F} (hf : ord v f = n) : ordIndex v ≤ n :=
  Nat.sInf_le ⟨hn, f, hf⟩

private theorem ordSet_nonempty {f : F} (hf : ord v f ≠ 0) :
    {n : ℕ | 0 < n ∧ ∃ g : F, ord v g = n}.Nonempty := by
  rcases lt_or_gt_of_ne hf with h | h
  · exact ⟨(-ord v f).toNat, by omega, f⁻¹, by rw [ord_inv]; omega⟩
  · exact ⟨(ord v f).toNat, by omega, f, by omega⟩

/-- A valuation attaining a nonzero order has positive index. -/
theorem ordIndex_pos {f : F} (hf : ord v f ≠ 0) : 0 < ordIndex v :=
  (Nat.sInf_mem (ordSet_nonempty v hf)).1

/-- A nontrivial valuation attains its index as an order. -/
theorem exists_ord_eq_ordIndex (hv : ordIndex v ≠ 0) : ∃ f : F, ord v f = ordIndex v := by
  have hS : {n : ℕ | 0 < n ∧ ∃ g : F, ord v g = n}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hv (by rw [ordIndex, h, Nat.sInf_empty])
  exact (Nat.sInf_mem hS).2

/-- The index vanishes exactly for the trivial valuations. -/
theorem ordIndex_eq_zero_iff : ordIndex v = 0 ↔ ∀ f : F, ord v f = 0 := by
  refine ⟨fun h f ↦ ?_, fun h ↦ ?_⟩
  · by_contra hf
    have := ordIndex_pos v hf
    omega
  · by_contra hne
    obtain ⟨f, hf⟩ := exists_ord_eq_ordIndex v hne
    rw [h f] at hf
    omega

/-- **Every order attained by a valuation is a multiple of its index.** -/
theorem ordIndex_dvd_ord (f : F) : (ordIndex v : ℤ) ∣ ord v f := by
  rcases eq_or_ne (ordIndex v) 0 with h | h
  · simp [h, (ordIndex_eq_zero_iff v).mp h f]
  obtain ⟨t, ht⟩ := exists_ord_eq_ordIndex v h
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [ord_zero] at ht
    omega
  have he : (0 : ℤ) < (ordIndex v : ℤ) := by omega
  refine Int.dvd_of_emod_eq_zero (by_contra fun hr ↦ ?_)
  have hr0 : 0 < ord v f % (ordIndex v : ℤ) :=
    lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hr)
  have hrlt : ord v f % (ordIndex v : ℤ) < (ordIndex v : ℤ) := Int.emod_lt_of_pos _ he
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [ord_zero] at hr0
    simp at hr0
  have hord : ord v (f / t ^ (ord v f / (ordIndex v : ℤ))) = ord v f % (ordIndex v : ℤ) := by
    rw [ord_div_zpow v hf0 ht0, ht, Int.emod_def]
    ring
  have := ordIndex_le v (n := (ord v f % (ordIndex v : ℤ)).toNat) (by omega)
    (f := f / t ^ (ord v f / (ordIndex v : ℤ))) (by rw [hord]; omega)
  omega

end OrdIndex

section Normalization

variable (v : _root_.Valuation F ℤᵐ⁰)

private theorem ediv_ordIndex_add (f g : F) :
    (ord v f + ord v g) / (ordIndex v : ℤ) =
      ord v f / (ordIndex v : ℤ) + ord v g / (ordIndex v : ℤ) := by
  rcases eq_or_ne (ordIndex v) 0 with h | h
  · simp [h]
  · have he : (ordIndex v : ℤ) ≠ 0 := by exact_mod_cast h
    obtain ⟨a, ha⟩ := ordIndex_dvd_ord v f
    obtain ⟨b, hb⟩ := ordIndex_dvd_ord v g
    rw [ha, hb, ← mul_add, Int.mul_ediv_cancel_left _ he, Int.mul_ediv_cancel_left _ he,
      Int.mul_ediv_cancel_left _ he]

private theorem ediv_ordIndex_mono {a b : ℤ} (h : a ≤ b) :
    a / (ordIndex v : ℤ) ≤ b / (ordIndex v : ℤ) := by
  rcases eq_or_ne (ordIndex v) 0 with h0 | h0
  · simp [h0]
  · exact Int.ediv_le_ediv (by omega) h

open scoped Classical in
/-- The **normalization** of a `ℤᵐ⁰`-valued valuation of a field: the valuation whose order
function is the order function of `v` divided by the index `Valuation.ordIndex v`. It is
equivalent to `v` and, as soon as `v` is nontrivial, surjective. -/
noncomputable def normalization : _root_.Valuation F ℤᵐ⁰ where
  toFun f := if f = 0 then 0 else WithZero.exp (-(ord v f / (ordIndex v : ℤ)))
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    have hfg : f * g ≠ 0 := mul_ne_zero hf hg
    rw [ord_mul v hf hg, ediv_ordIndex_add, neg_add, WithZero.exp_add]
    simp [hf, hg, hfg]
  map_add_le_max' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    rcases eq_or_ne (f + g) 0 with h0 | h0
    · simp [h0]
    have hmin := min_ord_le_ord_add v h0
    simp only [hf, hg, h0, ite_false]
    rcases le_total (ord v f) (ord v g) with h | h
    · refine le_trans ?_ (le_max_left _ _)
      rw [WithZero.exp_le_exp, neg_le_neg_iff]
      refine ediv_ordIndex_mono v ?_
      rw [← min_eq_left h]
      exact hmin
    · refine le_trans ?_ (le_max_right _ _)
      rw [WithZero.exp_le_exp, neg_le_neg_iff]
      refine ediv_ordIndex_mono v ?_
      rw [← min_eq_right h]
      exact hmin

theorem normalization_apply {f : F} (hf : f ≠ 0) :
    normalization v f = WithZero.exp (-(ord v f / (ordIndex v : ℤ))) := by
  classical
  simp only [normalization, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hf,
    ite_false]

@[simp]
theorem ord_normalization (f : F) : ord (normalization v) f = ord v f / (ordIndex v : ℤ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [ord_def, normalization_apply v hf, WithZero.log_exp, neg_neg]

/-- **The defining relation between a valuation and its normalization**: the order function of
`v` is the index times the order function of `normalization v`. -/
theorem ord_normalization_mul_ordIndex (f : F) :
    ord (normalization v) f * (ordIndex v : ℤ) = ord v f := by
  rw [ord_normalization]
  rcases eq_or_ne (ordIndex v) 0 with h | h
  · simp [h, (ordIndex_eq_zero_iff v).mp h f]
  · exact Int.ediv_mul_cancel (ordIndex_dvd_ord v f)

theorem ord_normalization_nonneg_iff {f : F} : 0 ≤ ord (normalization v) f ↔ 0 ≤ ord v f := by
  rcases eq_or_ne (ordIndex v) 0 with h | h
  · simp [h, (ordIndex_eq_zero_iff v).mp h f]
  · rw [← ord_normalization_mul_ordIndex v f]
    exact (mul_nonneg_iff_of_pos_right (by omega)).symm

/-- A valuation is equivalent to its normalization. -/
theorem isEquiv_normalization : (normalization v).IsEquiv v := by
  rw [isEquiv_iff_val_le_one]
  intro f
  rw [← _root_.Valuation.mem_valuationSubring_iff, ← _root_.Valuation.mem_valuationSubring_iff,
    mem_valuationSubring_iff_ord_nonneg, mem_valuationSubring_iff_ord_nonneg]
  exact ord_normalization_nonneg_iff v

@[simp]
theorem valuationSubring_normalization :
    (normalization v).valuationSubring = v.valuationSubring :=
  (isEquiv_iff_valuationSubring _ _).mp (isEquiv_normalization v)

/-- The normalization of a nontrivial valuation is surjective: its value group is all of
`ℤᵐ⁰`. -/
theorem normalization_surjective (hv : ordIndex v ≠ 0) :
    Function.Surjective (normalization v) := by
  obtain ⟨t, ht⟩ := exists_ord_eq_ordIndex v hv
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [ord_zero] at ht
    omega
  have he : (ordIndex v : ℤ) ≠ 0 := by exact_mod_cast hv
  intro x
  induction x using WithZero.expRecOn with
  | zero => exact ⟨0, map_zero _⟩
  | exp n =>
    refine ⟨t ^ (-n), ?_⟩
    rw [normalization_apply v (zpow_ne_zero _ ht0), ord_zpow, ht,
      Int.mul_ediv_cancel _ he, neg_neg]

/-- If the order function of a nontrivial valuation is a positive integral multiple of the
order function of another, then their indices differ by the same factor. -/
theorem ordIndex_eq_mul_of_forall_ord_eq (w : _root_.Valuation F ℤᵐ⁰) {e : ℕ} (he : 0 < e)
    (hw : ordIndex w ≠ 0) (hord : ∀ f : F, ord v f = e * ord w f) :
    ordIndex v = e * ordIndex w := by
  obtain ⟨f, hf⟩ := ord_surjective (normalization w) (normalization_surjective w hw) 1
  have hwf : ord w f = (ordIndex w : ℤ) := by
    rw [← ord_normalization_mul_ordIndex w f, hf, one_mul]
  have hvf : ord v f = (e * ordIndex w : ℕ) := by
    rw [hord, hwf]
    norm_cast
  have hprodPos : 0 < e * ordIndex w := Nat.mul_pos he (Nat.pos_of_ne_zero hw)
  have hle := ordIndex_le v hprodPos hvf
  have hv : ordIndex v ≠ 0 := by
    exact Nat.ne_of_gt (ordIndex_pos v (by rw [hvf]; exact_mod_cast hprodPos.ne'))
  obtain ⟨g, hg⟩ := exists_ord_eq_ordIndex v hv
  have hwordPos : 0 < ord w g := by
    have := hord g
    rw [hg] at this
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    have hv' : (0 : ℤ) < ordIndex v := by exact_mod_cast Nat.pos_of_ne_zero hv
    nlinarith
  have hwordEq : ord w g = (ord w g).toNat := by omega
  have hwle := ordIndex_le w (n := (ord w g).toNat) (by omega) hwordEq
  have hge : e * ordIndex w ≤ ordIndex v := by
    have hordg := hord g
    rw [hg] at hordg
    have hwle' : (ordIndex w : ℤ) ≤ ord w g := by
      calc
        (ordIndex w : ℤ) ≤ ((ord w g).toNat : ℕ) := by exact_mod_cast hwle
        _ = ord w g := by omega
    have he' : (0 : ℤ) ≤ e := by positivity
    have : (e * ordIndex w : ℕ) ≤ ordIndex v := by
      exact_mod_cast (calc
        (e : ℤ) * ordIndex w ≤ (e : ℤ) * ord w g := mul_le_mul_of_nonneg_left hwle' he'
        _ = (ordIndex v : ℤ) := hordg.symm)
    exact this
  omega

/-- Normalization preserves triviality on a base ring. -/
theorem IsTrivialOn.normalization {A : Type*} [CommRing A] [Algebra A F]
    [v.IsTrivialOn A] : (_root_.Valuation.normalization v).IsTrivialOn A where
  eq_one a ha := by
    have h1 : v (algebraMap A F a) = 1 := IsTrivialOn.eq_one a ha
    have h0 : algebraMap A F a ≠ 0 := by
      rintro h
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    rw [normalization_apply v h0, ord_def, h1]
    simp

end Normalization

end Valuation
