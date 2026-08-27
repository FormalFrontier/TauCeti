/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
public import TauCeti.NumberTheory.ModularForms.Norm.Order
public import TauCeti.NumberTheory.ModularForms.Norm.Trace
public import TauCeti.NumberTheory.ModularForms.Norm.Valence

/-!
# The cusp term of the general-level valence formula

For `𝒢 ≤ GL(2, ℝ)` of finite relative index in `𝒮ℒ`, the norm
`ModularForm.norm 𝒮ℒ f = ∏_{q ∈ 𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ} f ∣[k] q⁻¹` of a weight-`k` form on `𝒢` is a
level-one form, and `TauCeti/NumberTheory/ModularForms/Norm/Valence.lean` reads the level-one
valence formula back along it as

`Σ_{P ∈ 𝒢 \ ℍ} (2 / |Stab_𝒢 P|) · ord_P f + ord_∞(Nm f) = k · [SL(2, ℤ) : 𝒢] / 12`,

whose cusp term is still one order at `∞`, taken on the norm. This file distributes that term
over the cusps of `𝒢`, each read in its own width parameter, and so closes the general-level
valence formula (`valence_formula_finiteIndex`).

## Indexing the cusp translation orbits

The coset of `x` contributes the factor `f ∣[k] x⁻¹`, which is `f` read at the cusp `x⁻¹ ∞`, and
two cosets contribute at the same cusp exactly when they differ by left multiplication by an
element of the stabiliser `⟨T, -I⟩` of `∞` in `SL(2, ℤ)`. Here the cusp term is indexed by the
orbits of `⟨T⟩` alone (`CuspTranslationOrbit`), so a classical cusp of `𝒢` corresponds to one
cusp translation orbit or two, according as its `⟨T⟩`-orbit is stable under `-I` or not. That is
the **full**-coset convention that
`Norm/Valence.lean` already makes on the interior term — the weight there is read on the matrix
stabiliser, and the norm's weight is `k · [SL(2, ℤ) : 𝒢]` for the full index — so both halves of
the identity are read for the full coset space, which is what makes them match.

The **width** of an orbit is the period of that action: the least `m > 0` with
`x⁻¹ T ^ m x ∈ 𝒢` (`minimalPeriod_TSL_dvd_iff`, `cuspTranslationOrbitWidth_mk`). It is the
classical width of the cusp `x⁻¹ ∞` when `-I ∈ 𝒢`, and otherwise that width or twice it, in step
with the same convention.
The widths sum to the index (`sum_cuspTranslationOrbitWidth`), and the orbit of the base coset —
the cusp `∞` — has width `Subgroup.integerCuspWidth 𝒢`
(`cuspTranslationOrbitWidth_mk_one`).

## The mechanism

Over one orbit the coset factors are the integer translates of a single factor, so they multiply
to the Galois product `galoisProd` of it; and the width-`1` expansion of a Galois product has the
same order as the width-`m` expansion of the function it is built from
(`qExpansion_one_galoisProd_order_eq`). The norm is the product of these Galois products over the
orbits, so its order at `∞` is the sum of the orders of `f` at the cusp translation orbits.
Nothing here divides by an order that could be `⊤`: each factor of a nonzero form is nonzero
(`SlashInvariantForm.quotientFunc_ne_zero`), which is what the additivity of
`qExpansionOrderAtCusp` over products asks for.

## Main definitions

* `TauCeti.ModularForm.CuspTranslationOrbit`: the `T`-orbits on `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ` that index the
  cusp term under the full-coset convention.
* `TauCeti.ModularForm.cuspTranslationOrbitWidth`: the width of a cusp translation orbit.
* `TauCeti.ModularForm.orderAtCuspTranslationOrbit`: the vanishing order of a form at a cusp
  translation orbit, read in that orbit's width.

## Main results

* `TauCeti.ModularForm.orderAtCuspTranslationOrbit_mk`: the order at an orbit may be read at any
  representative coset, so the `Quotient.out` of the definition is only a spelling.
* `TauCeti.ModularForm.qExpansionOrderAtCusp_one_norm_eq_sum_orderAtCuspTranslationOrbit`: the cusp
  distribution — `ord_∞(Nm f) = Σ_c ord_c f`.
* `TauCeti.ModularForm.valence_formula_finiteIndex`: **the valence formula at general level**,
  with both halves distributed.
* `TauCeti.ModularForm.twelve_mul_orderAtCuspTranslationOrbit_le_weight_mul_index`: the mass at
  one cusp translation orbit is bounded by the total mass.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §3.
-/

public section

open UpperHalfPlane Complex Function SlashInvariantForm MulAction

open scoped ModularForm Topology Filter Manifold MatrixGroups

namespace TauCeti

namespace ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- The translation `T = [1, 1; 0, 1]`, viewed as an element of `𝒮ℒ`. Its powers generate the
translations of `ℍ` by integers, and left multiplication by them is the action whose orbits on
`𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ` are the cusp translation orbits. -/
def TSL : 𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict ModularGroup.T

/-- The image of `TSL ^ j` in `GL(2, ℝ)` is the image of `T ^ j`. -/
lemma coe_TSL_zpow (j : ℤ) :
    ((TSL ^ j : 𝒮ℒ) : GL (Fin 2) ℝ) = ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [TSL, ← map_zpow, MonoidHom.coe_rangeRestrict,
    ← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL]

/-- The **cusp translation orbits** of `𝒢`: the orbits of left translation by `T` on the coset
space `𝒮ℒ ⧸ 𝒢 ⊓ 𝒮ℒ`. The orbit of the coset of `x` represents the cusp `x⁻¹ ∞` of `𝒢`, indexed
for the full coset space rather than its projective quotient; see the module docstring. -/
abbrev CuspTranslationOrbit (𝒢 : Subgroup (GL (Fin 2) ℝ)) : Type :=
  orbitRel.Quotient (Subgroup.zpowers TSL) (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)

section Translate

variable [SlashInvariantFormClass F 𝒢 k]

/-- Translating a coset by a power of `T` shifts its factor of the norm. -/
lemma quotientFunc_TSL_zpow_smul (f : F) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (j : ℤ) (τ : ℍ) :
    quotientFunc f (TSL ^ j • q) τ = quotientFunc f q ((-j : ℝ) +ᵥ τ) := by
  have hmem : ((TSL ^ (-j) : 𝒮ℒ) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := (TSL ^ (-j) : 𝒮ℒ).2
  have hsubtype : (⟨((TSL ^ (-j) : 𝒮ℒ) : GL (Fin 2) ℝ), hmem⟩ : 𝒮ℒ) = TSL ^ (-j) :=
    Subtype.ext rfl
  have hinv : (⟨((TSL ^ (-j) : 𝒮ℒ) : GL (Fin 2) ℝ), hmem⟩ : 𝒮ℒ)⁻¹ = TSL ^ j := by
    rw [hsubtype, ← zpow_neg, neg_neg]
  rw [← hinv, ← quotientFunc_smul f hmem q, coe_TSL_zpow, ← _root_.ModularForm.SL_slash,
    slash_T_zpow_apply]
  norm_num

end Translate


section Width

/-- The period of a group element on a point is constant along that element's orbit.
Mathlib has `MulAction.period` and its divisibility API but not this invariance; it stays
private rather than planting a general group-theoretic declaration in a modular-forms file. -/
private lemma minimalPeriod_zpow_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (j : ℤ)
    (a : α) : minimalPeriod (g • ·) (g ^ j • a) = minimalPeriod (g • ·) a := by
  have key : ∀ (b : α) (i : ℤ), minimalPeriod (g • ·) (g ^ i • b) ∣ minimalPeriod (g • ·) b :=
    fun b i ↦ MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp (by
      rw [← mul_smul, ← zpow_natCast, ← zpow_add, add_comm, zpow_add, zpow_natCast, mul_smul,
        MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl])
  refine Nat.dvd_antisymm (key a j) ?_
  have h := key (g ^ j • a) (-j)
  rwa [← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul] at h

/-- The **width** of a cusp translation orbit of `𝒢`: the period of the `T`-action. Under
`[𝒢.IsFiniteRelIndex 𝒮ℒ]`, `minimalPeriod_TSL_dvd_iff` and
`cuspTranslationOrbitWidth_mk` identify it with the least `m > 0` such that
`x⁻¹ T ^ m x ∈ 𝒢` for any representative `x` of the orbit. -/
noncomputable def cuspTranslationOrbitWidth (c : CuspTranslationOrbit 𝒢) : ℕ :=
  minimalPeriod (TSL • ·) c.out

private lemma exists_zpow_smul_eq_out (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    ∃ j : ℤ, TSL ^ j • q = (⟦q⟧ : CuspTranslationOrbit 𝒢).out := by
  obtain ⟨h, hh⟩ := (orbitRel_apply (G := Subgroup.zpowers TSL)).mp
    (Quotient.eq.mp (Quotient.out_eq (⟦q⟧ : CuspTranslationOrbit 𝒢)))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.2
  refine ⟨j, ?_⟩
  rw [hj]
  exact hh

/-- The width of a cusp translation orbit is the period of the `T`-action at any representative
coset. -/
@[simp] lemma cuspTranslationOrbitWidth_mk (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    cuspTranslationOrbitWidth (⟦q⟧ : CuspTranslationOrbit 𝒢) =
      minimalPeriod (TSL • ·) q := by
  obtain ⟨j, hj⟩ := exists_zpow_smul_eq_out (𝒢 := 𝒢) q
  rw [cuspTranslationOrbitWidth, ← hj, minimalPeriod_zpow_smul]

/-- **What the period of a coset says about the group**: `T ^ n` fixes the coset of `x` exactly
when `x⁻¹ T ^ n x ∈ 𝒢`. Thus the action period is characterized by divisibility of exactly these
exponents. When the period is positive — in particular under `[𝒢.IsFiniteRelIndex 𝒮ℒ]` — it is
the least positive such `n`, the classical width of the cusp `x⁻¹ ∞`, read for the full coset
space rather than its projective quotient. -/
lemma minimalPeriod_TSL_dvd_iff (x : 𝒮ℒ) (n : ℕ) :
    minimalPeriod (TSL • ·) (QuotientGroup.mk x : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∣ n ↔
      ((x⁻¹ * TSL ^ n * x : 𝒮ℒ) : GL (Fin 2) ℝ) ∈ 𝒢 := by
  have hconj : ((TSL ^ n * x : 𝒮ℒ)⁻¹ * x : 𝒮ℒ) =
      (x⁻¹ * TSL ^ n * x : 𝒮ℒ)⁻¹ := by
    group
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, MulAction.Quotient.smul_mk, smul_eq_mul,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, hconj, InvMemClass.coe_inv, Subgroup.inv_mem_iff]

instance [𝒢.IsFiniteRelIndex 𝒮ℒ] (c : CuspTranslationOrbit 𝒢) :
    NeZero (cuspTranslationOrbitWidth c) :=
  inferInstanceAs (NeZero (minimalPeriod (TSL • ·) c.out))

lemma cuspTranslationOrbitWidth_pos [𝒢.IsFiniteRelIndex 𝒮ℒ] (c : CuspTranslationOrbit 𝒢) :
    0 < cuspTranslationOrbitWidth c :=
  Nat.pos_of_neZero _

end Width

section Product

variable [SlashInvariantFormClass F 𝒢 k]

/-- Each factor of the norm is periodic with the period of its coset as a period. -/
lemma periodic_quotientFunc (f : F) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    Periodic (quotientFunc f q ∘ ofComplex) ((minimalPeriod (TSL • ·) q : ℕ) : ℝ) := by
  refine TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mpr fun τ ↦ ?_
  have h := quotientFunc_TSL_zpow_smul f q (-(minimalPeriod (TSL • ·) q : ℤ)) τ
  rw [MulAction.zpow_smul_eq_iff_minimalPeriod_dvd.mpr (dvd_neg.mpr dvd_rfl)] at h
  rw [h]
  norm_num

/-- Each factor of the norm is periodic with the width of its cusp translation orbit as a
period. -/
lemma periodic_quotientFunc_out (f : F) (c : CuspTranslationOrbit 𝒢) :
    Periodic (quotientFunc f c.out ∘ ofComplex) (cuspTranslationOrbitWidth c : ℝ) :=
  periodic_quotientFunc f c.out

/-- The product of the norm factors over one cusp translation orbit is the Galois product of that
orbit's factor at its own width. -/
lemma prod_cuspTranslationOrbit_quotientFunc [𝒢.IsFiniteRelIndex 𝒮ℒ] (f : F)
    (c : CuspTranslationOrbit 𝒢) (τ : ℍ) :
    ∏ x : ZMod (cuspTranslationOrbitWidth c),
        quotientFunc f (TSL ^ (ZMod.cast x : ℤ) • c.out) τ =
      galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out) τ := by
  rw [galoisProd_apply]
  refine Finset.prod_nbij' ZMod.val (fun j ↦ (j : ZMod (cuspTranslationOrbitWidth c)))
    (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x)) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ (ZMod.natCast_zmod_val x)) (fun j hj ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hj))
    fun x _ ↦ ?_
  rw [quotientFunc_TSL_zpow_smul]
  congr 1
  have him : 0 < ((τ : ℂ) - ((x.val : ℕ) : ℂ)).im := by
    rw [Complex.sub_im, Complex.natCast_im, sub_zero]; exact τ.im_pos
  refine UpperHalfPlane.ext ?_
  rw [coe_vadd, ofComplex_apply_of_im_pos him, ← ZMod.natCast_val (R := ℤ)]
  push_cast
  ring

end Product



section Representative

section SlashInvariant

variable [SlashInvariantFormClass F 𝒢 k]

/-- **The Galois product over a full period does not see the choice of representative.**
Translating the coset by a power of `T` translates the product's argument by an integer,
and the Galois product is `1`-periodic. -/
lemma galoisProd_quotientFunc_TSL_zpow_smul (f : F) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (j : ℤ) :
    galoisProd (minimalPeriod (TSL • ·) q) (quotientFunc f (TSL ^ j • q)) =
      galoisProd (minimalPeriod (TSL • ·) q) (quotientFunc f q) := by
  funext τ
  have him : 0 < ((τ : ℂ) - (j : ℤ) * 1).im := by
    rw [mul_one, Complex.sub_im, Complex.intCast_im, sub_zero]; exact τ.im_pos
  have hτ : ((-j : ℝ) +ᵥ τ : ℍ) = ofComplex ((τ : ℂ) - (j : ℤ) * 1) := by
    refine UpperHalfPlane.ext ?_
    rw [coe_vadd, ofComplex_apply_of_im_pos him]
    push_cast
    ring
  have hshift : galoisProd (minimalPeriod (TSL • ·) q) (quotientFunc f (TSL ^ j • q)) τ =
      galoisProd (minimalPeriod (TSL • ·) q) (quotientFunc f q) ((-j : ℝ) +ᵥ τ) := by
    simp only [galoisProd_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [quotientFunc_TSL_zpow_smul]
    congr 1
    have harg : ((((-j : ℝ) +ᵥ τ : ℍ) : ℂ) - (i : ℕ)) = ((τ : ℂ) - (i : ℕ)) + ((-j : ℝ) : ℂ) := by
      rw [coe_vadd]; ring
    have hi : 0 < ((τ : ℂ) - (i : ℕ)).im := by
      rw [Complex.sub_im, Complex.natCast_im, sub_zero]; exact τ.im_pos
    have hi' : 0 < (((τ : ℂ) - (i : ℕ)) + ((-j : ℝ) : ℂ)).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hi
    refine UpperHalfPlane.ext ?_
    rw [harg, coe_vadd, ofComplex_apply_of_im_pos hi, ofComplex_apply_of_im_pos hi']
    ring
  have hP := (galoisProd_periodic_one (periodic_quotientFunc f q)).sub_int_mul_eq (x := (τ : ℂ)) j
  simp only [Function.comp_apply] at hP
  rw [hshift, hτ, hP, ofComplex_apply]

end SlashInvariant

variable [𝒢.IsFiniteRelIndex 𝒮ℒ] [ModularFormClass F 𝒢 k]

/-- **The order at a coset does not see the choice of representative** inside its `T`-orbit. -/
lemma qExpansionOrderAtCusp_quotientFunc_TSL_zpow_smul (f : F)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) (j : ℤ) :
    qExpansionOrderAtCusp ((minimalPeriod (TSL • ·) q : ℕ) : ℝ)
        (quotientFunc f (TSL ^ j • q)) =
      qExpansionOrderAtCusp ((minimalPeriod (TSL • ·) q : ℕ) : ℝ) (quotientFunc f q) := by
  have hw : 0 < minimalPeriod (TSL • ·) q := Nat.pos_of_neZero _
  have hper : Periodic (quotientFunc f (TSL ^ j • q) ∘ ofComplex)
      ((minimalPeriod (TSL • ·) q : ℕ) : ℝ) :=
    minimalPeriod_zpow_smul TSL j q ▸ periodic_quotientFunc f (TSL ^ j • q)
  rw [qExpansionOrderAtCusp_def, qExpansionOrderAtCusp_def,
    ← qExpansion_one_galoisProd_order_eq hw hper
      (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)
      (SlashInvariantForm.mdifferentiable_quotientFunc f _),
    ← qExpansion_one_galoisProd_order_eq hw (periodic_quotientFunc f q)
      (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)
      (SlashInvariantForm.mdifferentiable_quotientFunc f _),
    galoisProd_quotientFunc_TSL_zpow_smul]

end Representative

section Decomposition

variable [𝒢.IsFiniteRelIndex 𝒮ℒ]

/-- A subgroup of finite relative index has finitely many cusp translation orbits: they are the
orbits of an action on the finite coset space. -/
noncomputable instance fintypeCuspTranslationOrbit : Fintype (CuspTranslationOrbit 𝒢) :=
  Fintype.ofFinite _

variable [SlashInvariantFormClass F 𝒢 k]

/-- **The norm, decomposed over the cusp translation orbits**: the coset factors of one orbit
multiply to the Galois product of that orbit's factor, taken over a full period. -/
lemma slashInvariantForm_norm_apply_eq_prod_galoisProd (f : F) (τ : ℍ) :
    _root_.SlashInvariantForm.norm 𝒮ℒ f τ =
      ∏ c : CuspTranslationOrbit 𝒢,
        galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out) τ := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  rw [_root_.SlashInvariantForm.coe_norm, Finset.prod_apply,
    ← Equiv.prod_comp (Subgroup.quotientEquivSigmaZMod (𝒢.subgroupOf 𝒮ℒ) TSL).symm
      (fun q ↦ quotientFunc f q τ), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [← prod_cuspTranslationOrbit_quotientFunc f c τ]
  exact Finset.prod_congr rfl fun x _ ↦ by
    rw [Subgroup.quotientEquivSigmaZMod_symm_apply]
    rfl

end Decomposition


section Order

variable [𝒢.IsFiniteRelIndex 𝒮ℒ]

/-- The **vanishing order of `f` at a cusp translation orbit**: the order of the width-`m`
`q`-expansion of the coset factor `f ∣[k] x⁻¹`, where `m` is the width of the orbit and `x` a
representative. It does not depend on the representative — `orderAtCuspTranslationOrbit_mk`. -/
noncomputable def orderAtCuspTranslationOrbit [SlashInvariantFormClass F 𝒢 k] (f : F)
    (c : CuspTranslationOrbit 𝒢) : ℤ :=
  qExpansionOrderAtCusp (cuspTranslationOrbitWidth c : ℝ) (quotientFunc f c.out)

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The order at a cusp translation orbit is nonnegative: a modular form is holomorphic at every
cusp. -/
lemma orderAtCuspTranslationOrbit_nonneg [SlashInvariantFormClass F 𝒢 k] (f : F)
    (c : CuspTranslationOrbit 𝒢) : 0 ≤ orderAtCuspTranslationOrbit f c :=
  qExpansionOrderAtCusp_nonneg _ _

variable [ModularFormClass F 𝒢 k]

/-- **The order at a cusp translation orbit may be read at any representative coset**, in that
coset's own period; the `Quotient.out` in the definition is therefore only a choice of spelling. -/
@[simp] lemma orderAtCuspTranslationOrbit_mk (f : F) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    orderAtCuspTranslationOrbit f (⟦q⟧ : CuspTranslationOrbit 𝒢) =
      qExpansionOrderAtCusp ((minimalPeriod (TSL • ·) q : ℕ) : ℝ) (quotientFunc f q) := by
  obtain ⟨j, hj⟩ := exists_zpow_smul_eq_out (𝒢 := 𝒢) q
  rw [orderAtCuspTranslationOrbit, cuspTranslationOrbitWidth_mk, ← hj,
    qExpansionOrderAtCusp_quotientFunc_TSL_zpow_smul]

private lemma analyticAt_cuspFunction_one_galoisProd (f : F) (c : CuspTranslationOrbit 𝒢) :
    AnalyticAt ℂ
      (cuspFunction 1 (galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out))) 0 :=
  analyticAt_cuspFunction_zero one_pos (galoisProd_periodic_one (periodic_quotientFunc_out f c))
    (mdifferentiable_galoisProd (SlashInvariantForm.mdifferentiable_quotientFunc f _))
    (isBoundedAtImInfty_galoisProd (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _))

/-- The width-`1` order of the Galois product over a cusp translation orbit is the order of that
orbit's factor at its own width. -/
private lemma qExpansion_one_galoisProd_cuspTranslationOrbit_order_eq (f : F)
    (c : CuspTranslationOrbit 𝒢) :
    (qExpansion 1 (galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out))).order =
      (qExpansion (cuspTranslationOrbitWidth c : ℝ) (quotientFunc f c.out)).order :=
  qExpansion_one_galoisProd_order_eq (cuspTranslationOrbitWidth_pos c)
    (periodic_quotientFunc_out f c)
    (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)
    (SlashInvariantForm.mdifferentiable_quotientFunc f _)

private lemma qExpansion_cuspTranslationOrbit_ne_zero {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (c : CuspTranslationOrbit 𝒢) :
    qExpansion (cuspTranslationOrbitWidth c : ℝ) (quotientFunc f c.out) ≠ 0 :=
  mt (qExpansion_eq_zero_iff (mod_cast cuspTranslationOrbitWidth_pos c)
    (periodic_quotientFunc_out f c)
    (SlashInvariantForm.mdifferentiable_quotientFunc f _)
    (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)).mp
    (SlashInvariantForm.quotientFunc_ne_zero hf _)

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The period of the base coset is the integer cusp width of `𝒢`: both are characterised by
divisibility of the exponents `n` with `T ^ n ∈ 𝒢`. -/
private lemma minimalPeriod_TSL_mk_one :
    minimalPeriod (TSL • ·) (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) =
      Subgroup.integerCuspWidth 𝒢 := by
  have hsmul : ∀ n : ℕ, (TSL ^ n • (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)) =
      QuotientGroup.mk (TSL ^ n) := fun n ↦ by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have key : ∀ n : ℕ,
      minimalPeriod (TSL • ·) (QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) ∣ n ↔
      Subgroup.integerCuspWidth 𝒢 ∣ n := fun n ↦ by
    rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, hsmul n,
      ← Subgroup.natCast_mem_strictPeriods_iff]
    exact ⟨fun h ↦ Subgroup.mk_T_pow_eq_iff.mp h, fun h ↦ Subgroup.mk_T_pow_eq_iff.mpr h⟩
  exact Nat.dvd_antisymm ((key _).mpr dvd_rfl) ((key _).mp dvd_rfl)

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The orbit of the base coset represents the cusp `∞`, whose width is the integer cusp width. -/
@[simp 1100] lemma cuspTranslationOrbitWidth_mk_one :
    cuspTranslationOrbitWidth
        (⟦(QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢) =
      Subgroup.integerCuspWidth 𝒢 := by
  rw [cuspTranslationOrbitWidth_mk, minimalPeriod_TSL_mk_one]

/-- **At the cusp `∞` the order is the one the `∞`-decomposition reads**: the order of `f`
itself at the integer cusp width. -/
@[simp 1100] lemma orderAtCuspTranslationOrbit_mk_one (f : F) :
    orderAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢) =
      qExpansionOrderAtCusp ((Subgroup.integerCuspWidth 𝒢 : ℕ) : ℝ) (⇑f) := by
  rw [orderAtCuspTranslationOrbit_mk, minimalPeriod_TSL_mk_one,
    _root_.SlashInvariantForm.quotientFunc_mk, Subgroup.coe_one, inv_one, SlashAction.slash_one]

/-- **The order of the norm at `∞` is the sum of the orders of `f` at the cusp translation
orbits.** -/
theorem qExpansionOrderAtCusp_one_norm_eq_sum_orderAtCuspTranslationOrbit (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    qExpansionOrderAtCusp 1 ⇑(_root_.ModularForm.norm 𝒮ℒ f) =
      ∑ c : CuspTranslationOrbit 𝒢, orderAtCuspTranslationOrbit f c := by
  have hne : ∀ c : CuspTranslationOrbit 𝒢,
      analyticOrderAt (cuspFunction 1
        (galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out))) 0 ≠ ⊤ := fun c ↦ by
    rw [← qExpansion_order_eq_analyticOrderAt_cuspFunction
      (analyticAt_cuspFunction_one_galoisProd f c),
      qExpansion_one_galoisProd_cuspTranslationOrbit_order_eq, Ne, PowerSeries.order_eq_top]
    exact qExpansion_cuspTranslationOrbit_ne_zero hf c
  have hfun : (⇑(_root_.ModularForm.norm 𝒮ℒ f) : ℍ → ℂ) =
      ∏ c : CuspTranslationOrbit 𝒢,
        galoisProd (cuspTranslationOrbitWidth c) (quotientFunc f c.out) := by
    ext τ
    rw [_root_.ModularForm.coe_norm, ← _root_.SlashInvariantForm.coe_norm, Finset.prod_apply]
    exact slashInvariantForm_norm_apply_eq_prod_galoisProd f τ
  rw [hfun, qExpansionOrderAtCusp_prod _ (fun c _ ↦ analyticAt_cuspFunction_one_galoisProd f c)
    fun c _ ↦ hne c]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [orderAtCuspTranslationOrbit, qExpansionOrderAtCusp_def, qExpansionOrderAtCusp_def,
    qExpansion_one_galoisProd_cuspTranslationOrbit_order_eq]

end Order


section ValenceFormula

/-- **The widths of the cusp translation orbits sum to the index**
`[SL(2, ℤ) : 𝒢 ⊓ SL(2, ℤ)]`. -/
lemma sum_cuspTranslationOrbitWidth [𝒢.IsFiniteRelIndex 𝒮ℒ] :
    ∑ c : CuspTranslationOrbit 𝒢, cuspTranslationOrbitWidth c =
      Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :=
  ((𝒢.subgroupOf 𝒮ℒ).index_eq_card ▸
    Subgroup.index_eq_sum_minimalPeriod (𝒢.subgroupOf 𝒮ℒ) TSL).symm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
  [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- **The valence formula at general level**: for a nonzero weight-`k` form on a finite-index
`Γ ≤ SL(2, ℤ)`, the interior orders — weighted by `2 / |Stab_Γ P|` — together with the orders
indexed by the cusp translation orbits add up to `k · [SL(2, ℤ) : Γ] / 12`.

This is `valence_formula_finiteIndex_norm` with its cusp term, an order at `∞` on the norm,
distributed over the cusps of `Γ`. -/
theorem valence_formula_finiteIndex (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          weightedOrderOfVanishingOnSubgroupOrbit f o) +
        ∑ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
          (orderAtCuspTranslationOrbit f c : ℚ) =
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) / 12 := by
  rw [← valence_formula_finiteIndex_norm f hf,
    qExpansionOrderAtCusp_one_norm_eq_sum_orderAtCuspTranslationOrbit f hf]
  push_cast
  ring

/-- **The mass at one cusp is bounded by the total mass.** Every other term of the general-level
valence formula is nonnegative, so `12 · ord_c f ≤ k · [SL(2, ℤ) : Γ]` for a nonzero form — the
cusp counterpart of the interior bound
`twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le_weight_mul_index_mul_cardStabilizer`,
with `12` in place of `24` because a cusp carries no stabiliser weight. -/
theorem twelve_mul_orderAtCuspTranslationOrbit_le_weight_mul_index (f : F)
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
    12 * orderAtCuspTranslationOrbit f c ≤
      k * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  have hinterior : (0 : ℚ) ≤ ∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
      weightedOrderOfVanishingOnSubgroupOrbit f o :=
    finsum_nonneg (weightedOrderOfVanishingOnSubgroupOrbit_nonneg f)
  have hsingle : (orderAtCuspTranslationOrbit f c : ℚ) ≤
      ∑ c' : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c' : ℚ) :=
    Finset.single_le_sum (f := fun c' ↦ (orderAtCuspTranslationOrbit f c' : ℚ))
      (fun c' _ ↦ by exact_mod_cast orderAtCuspTranslationOrbit_nonneg f c')
      (Finset.mem_univ c)
  have htotal := valence_formula_finiteIndex f hf
  have hq : (12 : ℚ) * (orderAtCuspTranslationOrbit f c : ℚ) ≤
      (k : ℚ) * Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by linarith
  exact_mod_cast hq

end ValenceFormula

end ModularForm

end TauCeti

end
