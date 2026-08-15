/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# The integer cusp width of a finite-index subgroup

The image of `T = [1, 1; 0, 1]` in `GL(2, ℝ)` and its powers are the upper-triangular
shift matrices; a subgroup `𝒢` of finite relative index in `𝒮ℒ` contains some positive
power of `T`, and `Subgroup.integerCuspWidth 𝒢` is the least such exponent. The cosets of the
first `Subgroup.integerCuspWidth 𝒢` powers of `T` are pairwise distinct in `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`, and
the integer cusp width is a positive integer multiple of the strict width at `∞`.

## Main declarations

* `TauCeti.Subgroup.integerCuspWidth`.
* `TauCeti.Subgroup.natCast_mem_strictPeriods_iff`: the integer strict periods are the
  multiples of the width.
* `TauCeti.Subgroup.quotient_T_pow_integerCuspWidth_injective`.
* `TauCeti.Subgroup.exists_pos_nat_integerCuspWidth_eq_mul_strictWidthInfty`.
* `TauCeti.ModularForm.slash_T_zpow_apply`: slashing by a power of `T` is an integer shift.

## References

* [Mathlib PR #39087](https://github.com/leanprover-community/mathlib4/pull/39087)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup Subgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)` for any commutative ring `S` is the
upper-triangular matrix `[1, n; 0, 1]`. -/
@[simp]
lemma ModularGroup.mapGL_T_zpow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℤ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapGL_coe_matrix, ModularGroup.coe_T_zpow, -map_zpow]

/-- The image of `T ^ n : SL(2, ℤ)` in `GL(2, S)`, for a natural exponent. -/
@[simp]
lemma ModularGroup.mapGL_T_pow_eq_upperRightHom {S : Type*} [CommRing S] (n : ℕ) :
    Matrix.SpecialLinearGroup.mapGL S ((ModularGroup.T : SL(2, ℤ))^n) =
      Matrix.GeneralLinearGroup.upperRightHom (n : S) := by
  rw [← zpow_natCast, ModularGroup.mapGL_T_zpow_eq_upperRightHom, Int.cast_natCast]

/-- The matrix of `mapGL S ModularGroup.T` is `!![1, 1; 0, 1]`. -/
@[simp]
lemma ModularGroup.mapGL_T_coe_matrix {S : Type*} [CommRing S] :
    (↑(Matrix.SpecialLinearGroup.mapGL S (ModularGroup.T : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) S) =
      !![1, 1; 0, 1] := by
  have hT := ModularGroup.mapGL_T_pow_eq_upperRightHom (S := S) 1
  rw [pow_one] at hT
  rw [hT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.upperRightHom_apply]

/-- The coercion of `SL(2, ℤ)` into `GL(2, ℝ)` agrees with `mapGL ℝ`. -/
lemma Matrix.SpecialLinearGroup.coe_GL_eq_mapGL (g : SL(2, ℤ)) :
    (g : GL (Fin 2) ℝ) = mapGL ℝ g := rfl

/-- The Möbius action of `upperRightHom x = [1, x; 0, 1]` on `ℍ` is the shift `x +ᵥ ·`. -/
lemma Matrix.GeneralLinearGroup.upperRightHom_smul (x : ℝ) (τ : ℍ) :
    _root_.Matrix.GeneralLinearGroup.upperRightHom x • τ = x +ᵥ τ := by
  ext1
  rw [coe_smul_of_det_pos (by simp)]
  simp [num, denom, _root_.Matrix.GeneralLinearGroup.upperRightHom_apply, add_comm]

/-- Slashing a function `g : ℍ → ℂ` by the shift matrix `[1, x; 0, 1]` is the shift
`τ ↦ g (x +ᵥ τ)`. -/
lemma ModularForm.slash_upperRightHom_apply (k : ℤ) (x : ℝ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] (_root_.Matrix.GeneralLinearGroup.upperRightHom x : GL (Fin 2) ℝ)) τ =
      g (x +ᵥ τ) := by
  rw [_root_.ModularForm.slash_apply, Matrix.GeneralLinearGroup.upperRightHom_smul]
  simp [σ, denom, _root_.Matrix.GeneralLinearGroup.val_det_apply,
    _root_.Matrix.GeneralLinearGroup.upperRightHom_apply]

/-- Acting on a function `g : ℍ → ℂ` by `T ^ j` via the weight `k` slash action is the shift
`τ ↦ g ((j : ℝ) +ᵥ τ)`. -/
lemma ModularForm.slash_T_zpow_apply (k j : ℤ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] (ModularGroup.T ^ j : SL(2, ℤ))) τ = g ((j : ℝ) +ᵥ τ) := by
  rw [_root_.ModularForm.SL_slash, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
    ModularGroup.mapGL_T_zpow_eq_upperRightHom, ModularForm.slash_upperRightHom_apply]


section IntegerCuspWidth

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]

/-- The left-multiplication action of `𝒮ℒ` on the coset space `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`,
constructed explicitly: instance synthesis for this action is unstable at use sites, so
the declarations below install it with `letI`. -/
@[instance_reducible]
private noncomputable def quotientTAction :
    MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
  letI : MulAction 𝒮ℒ 𝒮ℒ := Monoid.toMulAction _
  .quotient ..

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The coset of a power of `T` is the base coset exactly when the exponent is a strict
period of `𝒢`: the bridge between the coset space and the strict periods, stated without
reference to the group action. -/
@[simp]
lemma Subgroup.mk_T_pow_eq_iff {n : ℕ} :
    (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)))^n⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) = ⟦1⟧ ↔ (n : ℝ) ∈ 𝒢.strictPeriods := by
  rw [QuotientGroup.eq]
  simp only [mul_one, inv_mem_iff, Subgroup.mem_subgroupOf,
    MonoidHom.coe_rangeRestrict, ← map_pow, ModularGroup.mapGL_T_pow_eq_upperRightHom,
    Subgroup.mem_strictPeriods_iff]

/-- A subgroup of `GL(2, ℝ)` of finite relative index in `𝒮ℒ` always has a positive
natural number in its strict periods: some positive power of `T` lands in the
subgroup. -/
lemma Subgroup.exists_pos_nat_mem_strictPeriods (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ∈ 𝒢.strictPeriods := by
  obtain ⟨n, hn_pos, _, hn_mem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := (𝒢 : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    ((mapGL ℝ).rangeRestrict ModularGroup.T)
  refine ⟨n, hn_pos, Subgroup.mk_T_pow_eq_iff.mp ?_⟩
  rw [QuotientGroup.eq]
  simpa using inv_mem hn_mem

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The powers of the coset of `T` acting on the base coset, as statements about
cosets: `t ^ n • ⟦1⟧ = ⟦t ^ n⟧` under the explicit action. -/
private lemma quotientTAction_pow_smul_mk_one (n : ℕ) :
    let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
    ((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))))^n •
        (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) =
      ⟦((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))))^n⟧ := by
  intro _
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The `MulAction.period` of the coset of `T` acting on the base coset of
`𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`. When some positive power of `T` lies in `𝒢` — in particular whenever
`𝒢` has finite relative index in `𝒮ℒ`, see `Subgroup.integerCuspWidth_pos` — this is
the smallest positive integer `n` such that the upper-triangular matrix `[1, n; 0, 1]`
lies in `𝒢`; otherwise it is `0`. -/
noncomputable def Subgroup.integerCuspWidth (𝒢 : Subgroup (GL (Fin 2) ℝ)) : ℕ :=
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  MulAction.period ((mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)))
    (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))

/-- The integer cusp width is positive. -/
lemma Subgroup.integerCuspWidth_pos : 0 < Subgroup.integerCuspWidth 𝒢 := by
  obtain ⟨n, hn_pos, hn_mem⟩ := Subgroup.exists_pos_nat_mem_strictPeriods 𝒢
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact MulAction.period_pos_of_fixed hn_pos
    ((quotientTAction_pow_smul_mk_one n).trans (Subgroup.mk_T_pow_eq_iff.mpr hn_mem))

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The integer cusp width is a strict period. -/
lemma Subgroup.integerCuspWidth_mem_strictPeriods :
    (Subgroup.integerCuspWidth 𝒢 : ℝ) ∈ 𝒢.strictPeriods := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact Subgroup.mk_T_pow_eq_iff.mp
    ((quotientTAction_pow_smul_mk_one _).symm.trans (MulAction.pow_period_smul _ _))

/-- `∞` is a cusp of a subgroup of finite relative index in `𝒮ℒ`: its integer cusp width is
a positive strict period, which is exactly the criterion.

This is the group-theoretic half of every "a form for `𝒢` is bounded at `∞`" argument; the
form-theoretic half is one application of `ModularFormClass.bdd_at_cusps` on top of it. -/
lemma Subgroup.isCusp_infty_of_finiteRelIndex : IsCusp OnePoint.infty 𝒢 :=
  Subgroup.isCusp_of_mem_strictPeriods
    (by exact_mod_cast Subgroup.integerCuspWidth_pos (𝒢 := 𝒢) :
      (0 : ℝ) < Subgroup.integerCuspWidth 𝒢)
    Subgroup.integerCuspWidth_mem_strictPeriods

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The integer cusp width is minimal among positive integer strict periods. -/
lemma Subgroup.integerCuspWidth_le {n : ℕ} (hpos : 0 < n)
    (hmem : (n : ℝ) ∈ 𝒢.strictPeriods) : Subgroup.integerCuspWidth 𝒢 ≤ n := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  exact MulAction.period_le_of_fixed hpos
    ((quotientTAction_pow_smul_mk_one n).trans (Subgroup.mk_T_pow_eq_iff.mpr hmem))

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The `integerCuspWidth 𝒢`-th power of `T` lies in `𝒢`. -/
lemma Subgroup.T_pow_integerCuspWidth_mem :
    ((ModularGroup.T : SL(2, ℤ))^(Subgroup.integerCuspWidth 𝒢 : ℕ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  rw [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← map_pow,
    ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff]
  exact Subgroup.integerCuspWidth_mem_strictPeriods

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The natural numbers among the strict periods are exactly the multiples of the
integer cusp width. -/
-- Not a `simp` lemma: `simpNF` rejects it because the left-hand side already simplifies
-- through `Subgroup.mem_strictPeriods_iff`.
lemma Subgroup.natCast_mem_strictPeriods_iff {n : ℕ} :
    (n : ℝ) ∈ 𝒢.strictPeriods ↔ Subgroup.integerCuspWidth 𝒢 ∣ n := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  rw [← Subgroup.mk_T_pow_eq_iff, ← quotientTAction_pow_smul_mk_one n,
    Subgroup.integerCuspWidth, MulAction.pow_smul_eq_iff_period_dvd]

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The powers of `T` lying in `𝒢` are exactly those with exponent divisible by the
integer cusp width. -/
@[simp]
lemma Subgroup.T_pow_mem_iff {n : ℕ} :
    ((ModularGroup.T : SL(2, ℤ))^n : GL (Fin 2) ℝ) ∈ 𝒢 ↔
      Subgroup.integerCuspWidth 𝒢 ∣ n := by
  rw [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← map_pow,
    ModularGroup.mapGL_T_pow_eq_upperRightHom, ← mem_strictPeriods_iff,
    Subgroup.natCast_mem_strictPeriods_iff]

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The cosets `T ^ j • (𝒢 ⊓ 𝒮ℒ)` for `j < integerCuspWidth 𝒢` are pairwise distinct in
`𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ`. -/
lemma Subgroup.quotient_T_pow_integerCuspWidth_injective :
    Function.Injective (fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦
      (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))) := by
  let _ : MulAction 𝒮ℒ (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := quotientTAction (𝒢 := 𝒢)
  set t := (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ))
  intro j₁ j₂ hj
  simp only [map_pow] at hj
  rw [← quotientTAction_pow_smul_mk_one (j₁ : ℕ),
    ← quotientTAction_pow_smul_mk_one (j₂ : ℕ)] at hj
  -- Injectivity of iterates below the minimal period, transported along
  -- `period = minimalPeriod` and `iterate = pow-smul`.
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := (t • ·))
    (x := (⟦1⟧ : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)))
  rw [← MulAction.period_eq_minimalPeriod] at hinj
  exact Fin.ext (hinj (Set.mem_Iio.mpr j₁.isLt) (Set.mem_Iio.mpr j₂.isLt)
    (by simpa only [smul_iterate] using hj))


/-- The integer cusp width is a positive integer multiple of the strict width at `∞`. -/
lemma Subgroup.exists_pos_nat_integerCuspWidth_eq_mul_strictWidthInfty
    [DiscreteTopology 𝒢.strictPeriods] :
    ∃ m : ℕ, 0 < m ∧ (Subgroup.integerCuspWidth 𝒢 : ℝ) = m * 𝒢.strictWidthInfty := by
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp <|
    Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty (𝒢 := 𝒢) ▸
      Subgroup.integerCuspWidth_mem_strictPeriods
  rw [zsmul_eq_mul] at hm
  have hm_pos : (0 : ℤ) < m := by
    have : (0 : ℝ) < m :=
      pos_of_mul_pos_left (hm ▸ mod_cast Subgroup.integerCuspWidth_pos) 𝒢.strictWidthInfty_nonneg
    exact_mod_cast this
  exact ⟨m.toNat, by lia, by rw [← hm, ← Int.cast_natCast, Int.toNat_of_nonneg hm_pos.le]⟩

end IntegerCuspWidth

end TauCeti

end
