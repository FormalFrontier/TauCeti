/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Additive orders of discrete valuations

This file packages the additive order attached to a `ℤᵐ⁰`-valued valuation and develops the
facts that do not depend on a choice of constant field.  The convention is
`ord_v f = -log (v f)`, so a uniformizer has order one.  As `WithZero.log 0 = 0`, the order
has the junk value `ord_v 0 = 0`; hypotheses excluding zero are included where necessary.
-/

public section

open scoped WithZero

open MonoidWithZeroHom

namespace Valuation

variable {F : Type*} [Field F]

/-- The additive order attached to a `ℤᵐ⁰`-valued valuation, with the convention that a
uniformizer has order one.  It has the junk value `ord_v 0 = 0`. -/
noncomputable def ord (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ℤ :=
  -WithZero.log (v f)

theorem ord_def (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f = -WithZero.log (v f) :=
  (rfl)

/-- Translation between the multiplicative valuation and its additive order. -/
theorem valuation_eq_exp_neg_ord (v : _root_.Valuation F ℤᵐ⁰) {f : F} (hf : f ≠ 0) :
    v f = WithZero.exp (-ord v f) := by
  rw [ord_def, neg_neg, WithZero.exp_log (v.ne_zero_iff.mpr hf)]

theorem ord_eq_iff_valuation_eq_exp_neg (v : _root_.Valuation F ℤᵐ⁰) {f : F}
    (hf : f ≠ 0) {n : ℤ} : ord v f = n ↔ v f = WithZero.exp (-n) := by
  rw [valuation_eq_exp_neg_ord v hf, WithZero.exp_inj, neg_inj]

@[simp]
theorem ord_zero (v : _root_.Valuation F ℤᵐ⁰) : ord v 0 = 0 := by
  simp [ord_def]

@[simp]
theorem ord_one (v : _root_.Valuation F ℤᵐ⁰) : ord v 1 = 0 := by
  simp [ord_def]

theorem ord_mul (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f * g) = ord v f + ord v g := by
  rw [ord_def, ord_def, ord_def, map_mul,
    WithZero.log_mul (v.ne_zero_iff.mpr hf) (v.ne_zero_iff.mpr hg)]
  ring

@[simp]
theorem ord_inv (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v f⁻¹ = -ord v f := by
  simp [ord_def, map_inv₀, WithZero.log_inv]

@[simp]
theorem ord_zpow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℤ) :
    ord v (f ^ n) = n * ord v f := by
  simp [ord_def, map_zpow₀, WithZero.log_zpow, mul_neg]

@[simp]
theorem ord_pow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℕ) :
    ord v (f ^ n) = n * ord v f := by
  simpa using ord_zpow v f n

theorem ord_div (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord v (f / g) = ord v f - ord v g := by
  rw [div_eq_mul_inv, ord_mul v hf (inv_ne_zero hg), ord_inv, sub_eq_add_neg]

@[simp]
theorem ord_neg (v : _root_.Valuation F ℤᵐ⁰) (f : F) : ord v (-f) = ord v f := by
  simp [ord_def, _root_.Valuation.map_neg]

/-- The order of a quotient by an integral power. -/
theorem ord_div_zpow (v : _root_.Valuation F ℤᵐ⁰) {f t : F} (hf : f ≠ 0) (ht : t ≠ 0)
    (n : ℤ) : ord v (f / t ^ n) = ord v f - n * ord v t := by
  rw [ord_div v hf (zpow_ne_zero _ ht), ord_zpow]

theorem ord_surjective (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    Function.Surjective (ord v) := fun n => by
  obtain ⟨f, hf⟩ := hv (WithZero.exp (-n))
  have hf0 : f ≠ 0 := v.ne_zero_iff.mp (by simp [hf])
  exact ⟨f, (ord_eq_iff_valuation_eq_exp_neg v hf0).mpr hf⟩

theorem mem_valuationSubring_iff_ord_nonneg (v : _root_.Valuation F ℤᵐ⁰) {f : F} :
    f ∈ v.valuationSubring ↔ 0 ≤ ord v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [show f ∈ v.valuationSubring ↔ v f ≤ 1 from Iff.rfl,
      valuation_eq_exp_neg_ord v hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

private theorem exp_max (a b : ℤ) :
    max (WithZero.exp a) (WithZero.exp b) = WithZero.exp (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

/-- The ultrametric inequality in additive form.  The hypothesis excludes the junk value at
zero. -/
theorem min_ord_le_ord_add (v : _root_.Valuation F ℤᵐ⁰) {f g : F} (h : f + g ≠ 0) :
    min (ord v f) (ord v g) ≤ ord v (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hadd := v.map_add f g
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg,
    valuation_eq_exp_neg_ord v h, exp_max, WithZero.exp_le_exp] at hadd
  omega

/-- The strict triangle inequality for an additive order. -/
theorem ord_add_eq_min_of_ord_ne (v : _root_.Valuation F ℤᵐ⁰) {f g : F}
    (hf : f ≠ 0) (hg : g ≠ 0) (h : ord v f ≠ ord v g) :
    ord v (f + g) = min (ord v f) (ord v g) := by
  have hne : v f ≠ v g := by
    rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg]
    simpa using h
  have hsum := v.map_add_of_distinct_val hne
  have hfg : f + g ≠ 0 := by
    refine v.ne_zero_iff.mp ?_
    rw [hsum]
    exact ne_of_gt (lt_max_of_lt_left (zero_lt_iff.mpr (v.ne_zero_iff.mpr hf)))
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord v hg,
    valuation_eq_exp_neg_ord v hfg, exp_max, WithZero.exp_inj] at hsum
  omega

/-- The additive order on nonzero field elements, as an additive homomorphism. -/
noncomputable def ordAddMonoidHom (v : _root_.Valuation F ℤᵐ⁰) : Additive Fˣ →+ ℤ where
  toFun f := ord v ((Additive.toMul f : Fˣ) : F)
  map_zero' := by simp
  map_add' f g := ord_mul v (Units.ne_zero _) (Units.ne_zero _)

@[simp]
theorem ordAddMonoidHom_apply (v : _root_.Valuation F ℤᵐ⁰) (f : Additive Fˣ) :
    ordAddMonoidHom v f = ord v ((Additive.toMul f : Fˣ) : F) :=
  (rfl)

/-- Surjectivity of `v` makes its value group the whole of `ℤᵐ⁰`. -/
theorem valueGroup_eq_top_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : valueGroup (.ofClass v) = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun γ => mem_valueGroup _ (hv γ)

/-- A surjective `ℤᵐ⁰`-valued valuation has nontrivial value group. -/
theorem nontrivial_valueGroup_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : Nontrivial (valueGroup (.ofClass v)) := by
  rw [valueGroup_eq_top_of_surjective v hv]
  exact (Subgroup.topEquiv (G := ℤᵐ⁰ˣ)).toEquiv.nontrivial

/-- The valuation ring of a surjective `ℤᵐ⁰`-valued valuation is a DVR. -/
theorem valuationSubring_isDiscreteValuationRing_of_surjective
    (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) :
    IsDiscreteValuationRing v.valuationSubring := by
  let _ := nontrivial_valueGroup_of_surjective v hv
  exact _root_.Valuation.valuationSubring_isDiscreteValuationRing v

/-- For a surjective valuation, Mathlib's generator is `exp (-1)`. -/
theorem generator_eq_exp_neg_one_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial (valueGroup (.ofClass v))] (hv : Function.Surjective v) :
    _root_.Valuation.IsRankOneDiscrete.generator v =
      Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
  _root_.Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hv

/-- Uniformizers of a surjective `ℤᵐ⁰`-valuation are exactly the elements of order one. -/
theorem isUniformizer_iff_ord_eq_one_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial (valueGroup (.ofClass v))] (hv : Function.Surjective v) {t : F} :
    v.IsUniformizer t ↔ ord v t = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · refine iff_of_false ?_ (by simp)
    simp only [_root_.Valuation.IsUniformizer, generator_eq_exp_neg_one_of_surjective v hv,
      map_zero, Units.val_mk0]
    exact fun h => WithZero.exp_ne_zero h.symm
  · rw [_root_.Valuation.IsUniformizer, generator_eq_exp_neg_one_of_surjective v hv,
      Units.val_mk0, ord_eq_iff_valuation_eq_exp_neg v ht]

theorem exists_isUniformizer_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial (valueGroup (.ofClass v))] (hv : Function.Surjective v) :
    ∃ t : F, v.IsUniformizer t := by
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  exact ⟨t, (isUniformizer_iff_ord_eq_one_of_surjective v hv).mpr ht⟩

theorem isUnit_iff_ord_eq_zero (v : _root_.Valuation F ℤᵐ⁰) {x : v.valuationSubring}
    (hx : (x : F) ≠ 0) : IsUnit x ↔ ord v (x : F) = 0 := by
  rw [_root_.Valuation.Integers.isUnit_iff_valuation_eq_one
      (_root_.Valuation.valuationSubring.integers v),
    Algebra.algebraMap_ofSubsemiring_apply, ord_eq_iff_valuation_eq_exp_neg v hx,
    neg_zero, WithZero.exp_zero]

/-- Existence half of the uniformizer expansion for a surjective valuation. -/
theorem exists_eq_zpow_mul_unit_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    [Nontrivial (valueGroup (.ofClass v))] (hv : Function.Surjective v)
    {t : F} (ht : v.IsUniformizer t) {f : F} (hf : f ≠ 0) :
    ∃ u : v.valuationSubringˣ, f = t ^ ord v f * (u : F) := by
  have ht1 : ord v t = 1 := (isUniformizer_iff_ord_eq_one_of_surjective v hv).mp ht
  have ht0 : t ≠ 0 := fun h => by simp [h] at ht1
  have hne : f / t ^ ord v f ≠ 0 := div_ne_zero hf (zpow_ne_zero _ ht0)
  have hord : ord v (f / t ^ ord v f) = 0 := by
    rw [ord_div_zpow v hf ht0, ht1]
    ring
  have hmem : f / t ^ ord v f ∈ v.valuationSubring :=
    (mem_valuationSubring_iff_ord_nonneg v).mpr hord.ge
  have hunit : IsUnit (⟨_, hmem⟩ : v.valuationSubring) :=
    (isUnit_iff_ord_eq_zero v hne).mpr hord
  refine ⟨hunit.unit, ?_⟩
  have hu : ((hunit.unit : v.valuationSubring) : F) = f / t ^ ord v f := by
    rw [IsUnit.unit_spec]
  rw [hu]
  field_simp

theorem mem_maximalIdeal_iff_ord_pos (v : _root_.Valuation F ℤᵐ⁰)
    {f : v.valuationSubring} (hf : (f : F) ≠ 0) :
    f ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ 0 < ord v (f : F) := by
  rw [_root_.Valuation.mem_maximalIdeal_iff, valuation_eq_exp_neg_ord v hf,
    ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem valuationSubring_ne_top_of_surjective (v : _root_.Valuation F ℤᵐ⁰)
    (hv : Function.Surjective v) : v.valuationSubring ≠ ⊤ := by
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  intro h
  have ht' : t⁻¹ ∈ v.valuationSubring := h ▸ ValuationSubring.mem_top _
  rw [mem_valuationSubring_iff_ord_nonneg v, ord_inv, ht] at ht'
  omega

/-- Two equivalent normalized `ℤᵐ⁰`-valuations are equal. -/
theorem eq_of_isEquiv_of_surjective {v w : _root_.Valuation F ℤᵐ⁰}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  have hmem : ∀ f : F, 0 ≤ ord v f ↔ 0 ≤ ord w f := fun f => by
    rw [← mem_valuationSubring_iff_ord_nonneg v, ← mem_valuationSubring_iff_ord_nonneg w]
    exact h.le_one_iff_le_one
  have hle : ∀ f : F, ord v f ≤ 0 ↔ ord w f ≤ 0 := fun f => by
    have h' := hmem f⁻¹
    rw [ord_inv, ord_inv] at h'
    omega
  have hzero : ∀ f : F, ord v f = 0 ↔ ord w f = 0 := fun f => by
    have h₁ := hmem f
    have h₂ := hle f
    omega
  obtain ⟨t, ht⟩ := ord_surjective v hv 1
  obtain ⟨s, hs⟩ := ord_surjective w hw 1
  have ht0 : t ≠ 0 := fun h' => by simp [h'] at ht
  have hs0 : s ≠ 0 := fun h' => by simp [h'] at hs
  have htW : 1 ≤ ord w t := by
    have h₁ := (hmem t).mp (by omega)
    have h₂ := (hzero t).not.mp (by omega)
    omega
  have hsV : 1 ≤ ord v s := by
    have h₁ := (hmem s).mpr (by omega)
    have h₂ := (hzero s).not.mpr (by omega)
    omega
  have hone : ord w t = 1 := by
    have hst : ord v (s / t ^ ord v s) = 0 := by
      rw [ord_div_zpow v hs0 ht0, ht]
      ring
    have hW := (hzero _).mp hst
    rw [ord_div_zpow w hs0 ht0, hs] at hW
    nlinarith [htW, hsV]
  refine _root_.Valuation.ext fun f => ?_
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have key : ord w f = ord v f := by
    have h₀ : ord v (f / t ^ ord v f) = 0 := by
      rw [ord_div_zpow v hf ht0, ht]
      ring
    have hW := (hzero _).mp h₀
    rw [ord_div_zpow w hf ht0, hone] at hW
    omega
  rw [valuation_eq_exp_neg_ord v hf, valuation_eq_exp_neg_ord w hf, key]

end Valuation
