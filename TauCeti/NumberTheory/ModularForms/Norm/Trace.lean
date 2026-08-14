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
* `TauCeti.ModularForm.normRest`, `TauCeti.ModularForm.periodic_normRest` and
  `TauCeti.ModularForm.analyticAt_cuspFunction_normRest`.
* `TauCeti.ModularForm.slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest`, with
  `TauCeti.ModularForm.norm_apply_eq_galoisProd_mul_normRest` as its modular-form corollary.
* `TauCeti.ModularForm.normRest_def`: the remainder as a product of coset factors.
* `TauCeti.ModularForm.normRest_apply_eq_div`: how to compute the remainder off the zeros of
  the Galois product.

The remainder and the decomposition itself are algebraic, so they are stated for
`SlashInvariantForm.norm` under `SlashInvariantFormClass`; only analyticity at the cusp
needs `f` to be a modular form.

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

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

namespace TauCeti

namespace SlashInvariantForm

variable [ModularFormClass F 𝒢 k]

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

/-! ### The algebraic layer

Everything up to the decomposition itself is a statement about the coset product, so it
needs only slash invariance. Analyticity at the cusp is separated out below. -/

section Algebraic

variable [SlashInvariantFormClass F 𝒢 k]

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
    -- so this bridge is proved rather than reached by rewriting. `QuotientGroup.eq` is the
    -- membership criterion for that equality — its own proof is `rw [leftRel_apply]`, so
    -- opening `Quotient.exact`/`leftRel_apply` by hand only redoes it.
    have hmk : ((t * x : 𝒮ℒ) : 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) =
        ⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ))^((j : ℕ) + 1))⟧ :=
      QuotientGroup.eq.mpr (by
        rw [pow_succ', map_mul, ← ht_def]
        convert inv_mem (QuotientGroup.eq.mp hj) using 1
        group)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, Finset.mem_image, hmk]
    by_cases hj1 : (j : ℕ) + 1 < Subgroup.integerCuspWidth 𝒢
    · exact ⟨⟨(j : ℕ) + 1, hj1⟩, Finset.mem_univ _, rfl⟩
    · refine ⟨⟨0, Subgroup.integerCuspWidth_pos⟩, Finset.mem_univ _, QuotientGroup.eq.mpr ?_⟩
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

/-- The remainder factor of the norm at the cusp `∞`: the product of the coset factors
outside the `T`-power cosets, so that the norm is the Galois product of the integer
translates of `f` times this factor.

Under `SlashInvariantFormClass` alone it is `1`-periodic (`periodic_normRest`) and is
characterised by `slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest`. Analyticity is the
one property that needs `f` to be a modular form: see `analyticAt_cuspFunction_normRest`. -/
public noncomputable def normRest : ℍ → ℂ := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  exact ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q

-- The working form, stated against the private `tPowCosets`. `normRest_def` below is the
-- same product with the index set written out, and is the public one; `tPowCoset` and
-- `tPowCosets` stay private, bridged by `tPowCosets_eq_image`.
/-- `normRest` as the product over the cosets that are not represented by a power of `T`,
for any choice of the finiteness and decidability instances on the coset space. -/
@[simp]
private lemma normRest_eq_prod_tPowCosets [Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] :
    normRest f = ∏ q ∈ Finset.univ.filter (· ∉ tPowCosets 𝒢), quotientFunc f q := by
  unfold normRest
  congr!

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
private lemma tPowCosets_eq_image [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] :
    tPowCosets 𝒢 = Finset.univ.image fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦
      (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)) ^ (j : ℕ))⟧ :
        𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) :=
  rfl

/-- **The remainder as a product.** `normRest f` is the product of the coset factors
`quotientFunc f q` over those `q` that are not the class of a power of `T` below the integer
cusp width, for any choice of the finiteness and decidability instances on the coset space. -/
public lemma normRest_def [Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))]
    [DecidableEq (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))] :
    normRest f = ∏ q ∈ Finset.univ.filter (· ∉ Finset.univ.image
        fun j : Fin (Subgroup.integerCuspWidth 𝒢) ↦
          (⟦(mapGL ℝ).rangeRestrict ((ModularGroup.T : SL(2, ℤ)) ^ (j : ℕ))⟧ :
            𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ))),
      quotientFunc f q := by
  rw [normRest_eq_prod_tPowCosets, tPowCosets_eq_image]
  congr!

/-- `normRest` is `1`-periodic. -/
public lemma periodic_normRest : Function.Periodic (normRest f ∘ ofComplex) 1 := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  refine periodic_comp_ofComplex_iff.mpr fun τ ↦ ?_
  rw [normRest_eq_prod_tPowCosets, Finset.prod_apply, Finset.prod_apply]
  exact prod_quotientFunc_one_vadd f τ

/-- **Decomposition of the norm at the cusp**, with the remainder factor named: the norm is
the Galois product of the first `Subgroup.integerCuspWidth 𝒢` integer translates of `f`
times `normRest f`.

Stated for `SlashInvariantForm.norm`: the decomposition is algebraic, so it needs only slash
invariance. `norm_apply_eq_galoisProd_mul_normRest` is the modular-form corollary. -/
public lemma slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest (τ : ℍ) :
    _root_.SlashInvariantForm.norm 𝒮ℒ f τ =
      galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ * normRest f τ := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  rw [_root_.SlashInvariantForm.coe_norm, Finset.prod_apply,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ tPowCosets 𝒢),
    Finset.filter_univ_mem, prod_tPowCosets_quotientFunc f τ, normRest_eq_prod_tPowCosets,
    Finset.prod_apply]

/-- Off the zeros of the Galois product, `normRest` **is** the quotient of the norm by that
product: together with the decomposition, this says how to compute `normRest` at a point with
no reference to the coset indexing used to define it.

Nothing is claimed here about the size of the excluded set — slash invariance alone gives no
zero-isolation property. -/
public lemma normRest_apply_eq_div {τ : ℍ}
    (h : galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ ≠ 0) :
    normRest f τ = _root_.SlashInvariantForm.norm 𝒮ℒ f τ /
      galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ := by
  rw [eq_div_iff h, slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest, mul_comm]

end Algebraic

/-! ### The analytic layer

Holomorphy and boundedness of the translates need `f` to be a modular form. -/

section Analytic

variable [ModularFormClass F 𝒢 k]

/-- The cusp function of `normRest` is analytic at `0`. -/
public lemma analyticAt_cuspFunction_normRest :
    AnalyticAt ℂ (cuspFunction 1 (normRest f)) 0 := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)) := Fintype.ofFinite _
  exact analyticAt_cuspFunction_zero one_pos (periodic_normRest f)
    (normRest_eq_prod_tPowCosets f ▸ MDifferentiable.prod fun q _ ↦
      SlashInvariantForm.mdifferentiable_quotientFunc f q)
    (normRest_eq_prod_tPowCosets f ▸ Filter.BoundedAtFilter.prod _ fun q _ ↦
      SlashInvariantForm.isBoundedAtImInfty_quotientFunc f q)

/-- **Decomposition of the norm at the cusp** for a modular form: the norm of `f` from `𝒢`
down to `𝒮ℒ` is the Galois product of the first `Subgroup.integerCuspWidth 𝒢` integer
translates of `f` times `normRest f`. This is the form to rewrite with when `f` is a modular
form; `slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest` is the general statement. -/
public lemma norm_apply_eq_galoisProd_mul_normRest (τ : ℍ) :
    _root_.ModularForm.norm 𝒮ℒ f τ =
      galoisProd (Subgroup.integerCuspWidth 𝒢) (f : ℍ → ℂ) τ * normRest f τ := by
  -- The two norms share an underlying function but not a spelling, and `rw` matches
  -- syntactically, so the bridge is taken through the two `coe_norm` lemmas rather than
  -- left to definitional unfolding.
  have hcoe : _root_.ModularForm.norm 𝒮ℒ f τ = _root_.SlashInvariantForm.norm 𝒮ℒ f τ := by
    rw [_root_.ModularForm.coe_norm, _root_.SlashInvariantForm.coe_norm]
  rw [hcoe, slashInvariantForm_norm_apply_eq_galoisProd_mul_normRest]

end Analytic

end NormDecomposition

end ModularForm

end TauCeti

end
