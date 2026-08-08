/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.Cusps
public import TauCeti.NumberTheory.ModularForms.GaloisProd

/-!
# Analytic properties of the translate package, and the norm decomposition at `∞`

For a modular form `f`, each translate in the package `SlashInvariantForm.quotientFunc` is
holomorphic, and — when the cusp `∞` is a cusp of `ℋ` of finite relative index — bounded at
infinity. For `𝒢` of finite relative index in `𝒮ℒ`, the norm of `f` from `𝒢` down to `𝒮ℒ`
factors at `∞` as the Galois product of the first `Subgroup.integerCuspWidth 𝒢` integer
translates of `f` times a `1`-periodic remainder analytic at `∞`.

## Main declarations

* `TauCeti.SlashInvariantForm.mdifferentiable_quotientFunc`.
* `TauCeti.SlashInvariantForm.isBoundedAtImInfty_quotientFunc`.
* `TauCeti.ModularForm.exists_norm_decomposition`.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083) and
  [Mathlib PR #39088](https://github.com/leanprover-community/mathlib4/pull/39088)
  (Chris Birkbeck) — the upstream drafts this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic
open TauCeti.UpperHalfPlane

open scoped ModularForm Topology Filter Manifold MatrixGroups Pointwise

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}
  [ModularFormClass F 𝒢 k]

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

namespace TauCeti

namespace SlashInvariantForm

/-- Each translate in the package `quotientFunc` of a modular form is holomorphic. -/
lemma mdifferentiable_quotientFunc (q : 𝒬) : MDiff (quotientFunc f q) :=
  Quotient.inductionOn q fun r ↦ (ModularForm.translate f r.val⁻¹).holo'

/-- Each translate in the package `quotientFunc` of a modular form is bounded at infinity,
when `∞` is a cusp of `ℋ` and the relative index is finite. -/
lemma isBoundedAtImInfty_quotientFunc [𝒢.IsFiniteRelIndex ℋ] [Fact (IsCusp OnePoint.infty ℋ)]
    (q : 𝒬) : IsBoundedAtImInfty (quotientFunc f q) :=
  Quotient.inductionOn q fun ⟨_, hr⟩ ↦ OnePoint.isBoundedAt_infty_iff.mp <|
    (ModularForm.translate f _).bdd_at_cusps'
      ((Fact.out : IsCusp _ _).of_isFiniteRelIndex_conj hr)

end SlashInvariantForm

namespace ModularForm

section NormDecomposition

open _root_.Matrix.SpecialLinearGroup

variable [𝒢.IsFiniteRelIndex 𝒮ℒ]

variable (𝒢) in
/-- The coset of `T ^ j` in `𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ)`. -/
private def tPowCoset (j : ℕ) : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ) :=
  ⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^j)⟧

variable (𝒢) in
/-- The cosets of `T ^ j` for `j < integerCuspWidth 𝒢`, as a finset. -/
private def tPowCosets [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] :
    Finset (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
  Finset.univ.image fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦ tPowCoset 𝒢 j

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
private lemma quotientFunc_T_pow_apply (j : Fin (Subgroup.integerCuspWidth 𝒢)) (τ : ℍ) :
    quotientFunc f (tPowCoset 𝒢 j) τ = f (ofComplex ((τ : ℂ) - (j : ℕ))) := by
  rw [tPowCoset, quotientFunc_mk]
  have h_val : ((((mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^(j : ℕ)) : 𝒮ℒ) :
      GL (Fin 2) ℝ))⁻¹ = ((ModularGroup.T ^ (-(j : ℕ) : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [MonoidHom.coe_rangeRestrict, ← map_inv, ← zpow_natCast, ← zpow_neg,
      ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  rw [h_val, ← _root_.ModularForm.SL_slash, slash_T_zpow_apply]
  have him : 0 < ((τ : ℂ) - (j : ℕ)).im := by
    simp [Complex.sub_im, Complex.natCast_im, τ.im_pos]
  have h_eq : (((-(j : ℕ) : ℤ) : ℝ) +ᵥ τ : ℍ) = ofComplex ((τ : ℂ) - (j : ℕ)) := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos him]
    push_cast
    ring
  rw [h_eq]

private lemma smul_mem_tPowCosets [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    {q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)} (hq : q ∈ tPowCosets 𝒢) :
    (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)) • q ∈ tPowCosets 𝒢 := by
  induction q using Quotient.inductionOn with
  | h x =>
    set t : 𝒮ℒ := (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)) with ht_def
    simp only [tPowCosets, tPowCoset] at hq ⊢
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hq
    -- The action lemma below produces the `QuotientGroup.mk` spelling of the coset, while the
    -- image members are spelled `⟦·⟧`; the two are definitionally but not syntactically equal,
    -- so this bridge is proved by `Quotient.sound` rather than reached by rewriting.
    have hmk : ((t * x : 𝒮ℒ) : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) =
        ⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^((j : ℕ) + 1))⟧ :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
        rw [pow_succ', map_mul, ← ht_def]
        convert inv_mem (QuotientGroup.leftRel_apply.mp (Quotient.exact hj)) using 1
        group))
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, Finset.mem_image, hmk]
    by_cases hj1 : (j : ℕ) + 1 < Subgroup.integerCuspWidth 𝒢
    · exact ⟨⟨(j : ℕ) + 1, hj1⟩, Finset.mem_univ _, rfl⟩
    · refine ⟨⟨0, Subgroup.integerCuspWidth_pos⟩, Finset.mem_univ _,
        Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)⟩
      have hw : (j : ℕ) + 1 = Subgroup.integerCuspWidth 𝒢 := by lia
      rw [hw]
      simp only [pow_zero, map_one, inv_one, one_mul, Subgroup.mem_subgroupOf, map_pow]
      have key := Subgroup.T_pow_integerCuspWidth_mem (𝒢 := 𝒢)
      rwa [Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] at key

private lemma inv_smul_mem_tPowCosets_iff [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    (q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :
    ((mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)))⁻¹ • q ∈ tPowCosets 𝒢 ↔
      q ∈ tPowCosets 𝒢 := by
  set t : 𝒮ℒ := (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ))
  have h_eq : t • tPowCosets 𝒢 = tPowCosets 𝒢 :=
    Finset.eq_of_subset_of_card_le (fun q hq ↦ by
      obtain ⟨q', hq', rfl⟩ := Finset.mem_smul_finset.mp hq
      exact smul_mem_tPowCosets hq')
      (Finset.card_smul_finset ..).ge
  rw [Finset.inv_smul_mem_iff, h_eq]

private lemma prod_quotientFunc_one_vadd [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    [Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] (τ : ℍ) :
    ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q ((1 : ℝ) +ᵥ τ) =
      ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q τ := by
  set t : 𝒮ℒ := (mapGL ℝ).rangeRestrict (ModularGroup.T : SL(2, ℤ)) with ht_def
  have ht_val : (t : GL (Fin 2) ℝ) = ((ModularGroup.T ^ (1 : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [ht_def, MonoidHom.coe_rangeRestrict, zpow_one,
      ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]
  have h_step (q : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :
      quotientFunc f q ((1 : ℝ) +ᵥ τ) = quotientFunc f (t⁻¹ • q) τ := by
    have hslash : quotientFunc f q ((1 : ℝ) +ᵥ τ) =
        (quotientFunc f q ∣[k] (t : GL (Fin 2) ℝ)) τ := by
      rw [ht_val, ← _root_.ModularForm.SL_slash, slash_T_zpow_apply]
      norm_num
    rw [hslash, quotientFunc_smul f t.2]
  refine (Finset.prod_congr rfl fun q _ ↦ h_step q).trans <|
    Finset.prod_equiv (MulAction.toPerm t⁻¹)
      (fun q ↦ by simpa using (inv_smul_mem_tPowCosets_iff (𝒢 := 𝒢) q).symm.not)
      (fun _ _ ↦ rfl)

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
private lemma prod_tPowCosets_quotientFunc [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] (τ : ℍ) :
    ∏ q ∈ tPowCosets 𝒢, quotientFunc f q τ =
      galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ := by
  rw [tPowCosets, galoisProd_apply,
    Finset.prod_image fun i _ j _ h ↦
      Subgroup.quotient_T_pow_integerCuspWidth_injective (by simpa [tPowCoset] using h),
    Finset.prod_congr rfl fun j _ ↦ quotientFunc_T_pow_apply f j τ,
    Fin.prod_univ_eq_prod_range (fun n ↦ (f : ℍ → ℂ) (ofComplex ((τ : ℂ) - n))) _]

/-- Decomposition of the norm of `f` from `𝒢` to `𝒮ℒ` at the cusp `∞`: it is the Galois
product of the first `Subgroup.integerCuspWidth 𝒢` integer translates of `f` times a remainder which
is `1`-periodic and analytic at `∞`. -/
lemma exists_norm_decomposition :
    ∃ rest : ℍ → ℂ,
      Function.Periodic (rest ∘ ofComplex) 1 ∧ AnalyticAt ℂ (cuspFunction 1 rest) 0 ∧
        ∀ τ : ℍ, _root_.ModularForm.norm 𝒮ℒ f τ =
          galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ * rest τ := by
  classical
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (by simp)⟩
  let _ : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  set rest : ℍ → ℂ :=
    fun τ ↦ ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q τ
  have h_rest_eq : rest =
      ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q :=
    funext fun _ ↦ (Finset.prod_apply ..).symm
  have h_rest_per : Function.Periodic (rest ∘ ofComplex) 1 :=
    periodic_comp_ofComplex_iff.mpr fun τ ↦ prod_quotientFunc_one_vadd f τ
  refine ⟨rest, h_rest_per, analyticAt_cuspFunction_zero one_pos h_rest_per
    (h_rest_eq ▸ MDifferentiable.prod fun q _ ↦
      SlashInvariantForm.mdifferentiable_quotientFunc f q)
    (h_rest_eq ▸ Filter.BoundedAtFilter.prod _ fun q _ ↦
      SlashInvariantForm.isBoundedAtImInfty_quotientFunc f q),
    fun τ ↦ ?_⟩
  rw [_root_.ModularForm.coe_norm, Finset.prod_apply,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ tPowCosets 𝒢),
    Finset.filter_univ_mem, prod_tPowCosets_quotientFunc f τ]

end NormDecomposition

end ModularForm

end TauCeti

end
