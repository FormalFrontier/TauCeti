/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Modular-forms basics: extensions of Mathlib's API

Small generic lemmas extending `Mathlib/NumberTheory/ModularForms/Basic.lean` and its slash
actions: the conjugation `σ` is trivial on `SL(2, ℤ)`-matrices — a special case of
`UpperHalfPlane.σ_eq_refl_of_det_pos`, which lives with `σ` itself in
`TauCeti/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean` — the `CuspForm`
translation equations Mathlib does not yet provide (`CuspForm.mcast_apply` and the
`GL(2, ℝ)`-level `CuspForm.coe_translate_gl`), and the weight-`k` slash action of `-I`
(`ModularForm.slash_neg_one`), the source of every parity constraint on weights and
nebentypus characters.

It also records how modular and cusp forms move between two nested groups `Γ' ≤ Γ`. Shrinking
the group is unconditional (`ModularForm.ofLe`): slash invariance restricts, and every cusp of
`Γ'` is a cusp of `Γ` (`IsCusp.mono`), so the boundedness conditions restrict as well.
Enlarging it is not: a `Γ'`-form which happens to be `Γ`-slash invariant is bounded only at the
cusps of `Γ'`, so one needs to know that `Γ` has no further cusps, which
`ModularForm.ofSlashInvariant` takes as its hypothesis. Two arithmetic groups always satisfy it
(`Subgroup.IsArithmetic.isCusp_of_isCusp`: both have the cusps of `SL(2, ℤ)`). Under it the two
constructions are mutually inverse: the image of `M_k(Γ) → M_k(Γ')` is exactly the
`Γ`-invariant part of `M_k(Γ')` (`ModularForm.mem_range_ofLeₗ_iff`).

The first group of lemmas was split out of the diamond-operator development ported from the
AINTLIB `LeanModularForms` project
(<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).

## Main definitions

* `ModularForm.ofLe`, `CuspForm.ofLe` (and their `ℂ`-linear packagings `ofLeₗ`): a form for `Γ`
  read as a form for a subgroup `Γ' ≤ Γ`.
* `ModularForm.ofSlashInvariant`, `CuspForm.ofSlashInvariant`: a `Γ'`-form which is slash
  invariant under a group `Γ` all of whose cusps are cusps of `Γ'`, read as a form for `Γ`.

## Main results

* `SlashInvariantFormClass.SL_slash_eq`: a form invariant under the image of `Γ ≤ SL(2, ℤ)`
  is fixed by the slash action of every element of `Γ`.
* `SlashInvariantForm.slash_action_eqn_of_det_pos`: the transformation law
  `f (γ • τ) = |det γ| ^ (1 - k) * denom γ τ ^ k * f τ` for `γ` of positive determinant,
  generalising Mathlib's `slash_action_eqn''`, which assumes `det γ = 1`.
* `Subgroup.IsArithmetic.isCusp_of_isCusp`: any two arithmetic groups have the same cusps.
* `ModularForm.mem_range_ofLeₗ_iff`, `CuspForm.mem_range_ofLeₗ_iff`: for `Γ' ≤ Γ` with every
  cusp of `Γ` a cusp of `Γ'`, a form for `Γ'` extends to `Γ` exactly when it is `Γ`-slash
  invariant.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm

/-- **Every element of `𝒮ℒ` has positive determinant**: it is the image of a matrix of
determinant `1`.

This is the hypothesis the positive-determinant slash lemmas take — `σ_eq_refl_of_det_pos` just
below, and `orderOfVanishingAt_slash` / `orderOfVanishingAt_smul` in
`TauCeti.NumberTheory.ModularForms.Order.OfVanishing` — and every modular call site discharges
it the same way. Keying it on membership in `𝒮ℒ` rather than on
`Matrix.SpecialLinearGroup.mapGL` covers both shapes the call sites come in: a direct image
`mapGL ℝ γ` (via `MonoidHom.mem_range.mpr ⟨γ, rfl⟩`) and an element of the image of a subgroup
`Γ ≤ SL(2, ℤ)` (via `Subgroup.map_le_range`). -/
theorem det_pos_of_mem_slGL {g : GL (Fin 2) ℝ} (hg : g ∈ 𝒮ℒ) :
    0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
  obtain ⟨γ, rfl⟩ := hg
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL]
  exact one_pos

/-- The slash-action conjugation `σ` is the identity for matrices coming from
`SL₂(ℤ)`: their determinant is `1 > 0`, so the `σ` branch picks `ContinuousAlgEquiv.refl ℝ ℂ`.

This keeps `@[simp]` even though `UpperHalfPlane.σ_eq_refl_of_det_pos` is also `@[simp]`: that
one is conditional, and `simp` cannot discharge `0 < (↑(mapGL ℝ s)).det` on its own — the
determinant of a mapped `SL(2, ℤ)` matrix reduces through `GeneralLinearGroup.det`, not through
`Matrix.det` of the entrywise map. So the two do not overlap in practice. -/
@[simp]
lemma σ_mapGL_real_eq_refl (s : SL(2, ℤ)) :
    UpperHalfPlane.σ (mapGL ℝ s) = ContinuousAlgEquiv.refl ℝ ℂ :=
  σ_eq_refl_of_det_pos (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨s, rfl⟩))

/-- `CuspForm.mcast` does not change the pointwise values of a cusp form: the `CuspForm`
analogue of Mathlib's `ModularForm.mcast_apply`, which Mathlib does not yet provide. -/
lemma _root_.CuspForm.mcast_apply {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b)
    (f : CuspForm Γ a) (hΓ : Γ' = Γ := by rfl) (z : ℍ) : CuspForm.mcast h f hΓ z = f z := (rfl)

/-- `GL(2, ℝ)`-level coercion lemma for `CuspForm.translate`; Mathlib's
`CuspForm.coe_translate` is specialized to `SL(2, ℤ)` arguments. -/
@[simp]
lemma _root_.CuspForm.coe_translate_gl {F : Type*} [FunLike F UpperHalfPlane ℂ] {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    ⇑(CuspForm.translate f g) = ⇑f ∣[k] g := (rfl)

/-- The weight-`k` slash action of `-I` is multiplication by `(-1) ^ k`: `-I` acts trivially
on `ℍ` and has determinant `1`, so the only surviving factor is its automorphy factor
`denom (-I) z ^ (-k) = (-1) ^ (-k) = (-1) ^ k`.

This is the source of every parity constraint on weights and nebentypus characters. -/
@[simp]
theorem _root_.ModularForm.slash_neg_one (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] (-1 : GL (Fin 2) ℝ) = (-1 : ℂ) ^ k • f := by
  have hzpow : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
    rw [zpow_neg, ← inv_zpow]
    norm_num
  have hdet : (-1 : GL (Fin 2) ℝ).det = 1 := by
    ext
    simp [Matrix.det_neg]
  funext z
  rw [ModularForm.slash_apply, σ_eq_refl_of_det_pos (by simp [Matrix.det_neg])]
  simp [hzpow, hdet, mul_comm]

/-- **The weight-`k` slash formula at a positive-determinant matrix**, free of the `σ` twist:

`f ∣[k] g = fun τ ↦ f (g • τ) * |det g| ^ (k - 1) * denom g τ ^ (-k)`.

Mathlib's `ModularForm.slash_def` carries `σ g` around the value of `f`, which is complex
conjugation on the negative-determinant branch. `ModularForm.SL_slash_def` drops it because
`det = 1`; here positivity alone is what does it. -/
theorem _root_.ModularForm.slash_def_of_det_pos (k : ℤ) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ) :
    f ∣[k] g = fun τ ↦ f (g • τ) * |(g.det : ℝ)| ^ (k - 1) * denom g τ ^ (-k) := by
  rw [ModularForm.slash_def, σ_eq_refl_of_det_pos hg]
  rfl

/-- The pointwise form of `ModularForm.slash_def_of_det_pos`, matching
`ModularForm.SL_slash_apply`. -/
theorem _root_.ModularForm.slash_apply_of_det_pos (k : ℤ) {g : GL (Fin 2) ℝ}
    (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] g) τ = f (g • τ) * |(g.det : ℝ)| ^ (k - 1) * denom g τ ^ (-k) :=
  congrFun (ModularForm.slash_def_of_det_pos k hg f) τ

/-- **Scalars pass through the slash of a positive-determinant matrix.** Mathlib's
`ModularForm.smul_slash` carries the twist `σ A c`, which is complex conjugation when the
determinant is negative, so scalars do not commute past a general slash. On the positive branch
they do.

This is what makes a Hecke operator `ℂ`-linear: it is a sum of slashes by representatives of
positive determinant. The scalar generality matches `ModularForm.SL_smul_slash`. -/
@[simp]
theorem _root_.ModularForm.smul_slash_of_det_pos {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (f : ℍ → ℂ)
    (c : α) : (c • f) ∣[k] g = c • f ∣[k] g := by
  ext τ : 1
  simp [ModularForm.slash_apply_of_det_pos k hg, smul_mul_assoc]

/-- A form invariant under the image in `GL(2, ℝ)` of a subgroup `Γ ≤ SL(2, ℤ)` is fixed by
the weight-`k` slash action of every element of `Γ` — the invariance condition read back at
the `SL₂(ℤ)` level, where congruence subgroups are given. -/
theorem _root_.SlashInvariantFormClass.SL_slash_eq {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F (Γ.map (mapGL ℝ)) k] (f : F)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) : ⇑f ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩

/-- **The transformation law of a slash-invariant form under a positive-determinant element.**
For `γ ∈ Γ` with `0 < det γ`, `f (γ • τ) = |det γ| ^ (1 - k) * denom γ τ ^ k * f τ`.

Mathlib's `SlashInvariantForm.slash_action_eqn''` is the `det = 1` case, in which the first
factor is `1` and disappears. -/
theorem _root_.SlashInvariantForm.slash_action_eqn_of_det_pos {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [SlashInvariantFormClass F Γ k] (f : F) {γ}
    (hγ : γ ∈ Γ) (hdet : 0 < γ.val.det) (τ : ℍ) :
    f (γ • τ) = ((|(γ.det : ℝ)| : ℝ) : ℂ) ^ (1 - k) * denom γ (τ : ℂ) ^ k * f τ := by
  have hdet_ne : ((|(γ.det : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (γ.det : ℝˣ).ne_zero).ne'
  have h := congr_fun (SlashInvariantForm.slash_action_eqn f γ hγ) τ
  rw [ModularForm.slash_def, σ_eq_refl_of_det_pos hdet] at h
  simp only [ContinuousAlgEquiv.refl_apply] at h
  -- clear the two inverse factors of the slash action in turn, then read off the exponents
  have hden : denom γ (τ : ℂ) ^ (-k) ≠ 0 := zpow_ne_zero _ (denom_ne_zero γ τ)
  have hpow : ((|(γ.det : ℝ)| : ℝ) : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hdet_ne
  rw [(eq_mul_inv_iff_mul_eq₀ hpow).mpr ((eq_mul_inv_iff_mul_eq₀ hden).mpr h),
    ← zpow_neg, ← zpow_neg, neg_neg, neg_sub]
  ring

/-! ### Changing the invariance group

Throughout, `Γ' ≤ Γ` are subgroups of `GL(2, ℝ)`.
-/

section OfLe

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

-- The four constructions below are deliberately not `@[expose]`, so their characteristic lemmas
-- are written `(rfl)` rather than `rfl`: the parentheses opt out of exporting the definitional
-- equality, which downstream modules do not need and which those lemmas themselves replace.

/-- Two arithmetic subgroups of `GL(2, ℝ)` have the same cusps, namely those of `SL(2, ℤ)`.
This is the standard way to supply the cusp hypothesis of `ModularForm.ofSlashInvariant`. -/
lemma _root_.Subgroup.IsArithmetic.isCusp_of_isCusp [Γ.IsArithmetic] [Γ'.IsArithmetic]
    (c : OnePoint ℝ) (hc : IsCusp c Γ) : IsCusp c Γ' :=
  (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ').mpr
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mp hc)

namespace ModularForm

/-- A modular form for `Γ` is a modular form for any subgroup `Γ' ≤ Γ`: slash invariance
restricts, and a cusp of `Γ'` is a cusp of `Γ`, so the boundedness conditions restrict too. -/
def ofLe (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' _ hγ := f.slash_action_eq' _ (h hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[simp]
lemma coe_ofLe (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ⇑(ofLe h f) = ⇑f := (rfl)

lemma ofLe_injective (h : Γ' ≤ Γ) : Function.Injective (ofLe h : ModularForm Γ k → _) :=
  fun _ _ hfg ↦ ext fun z ↦ DFunLike.congr_fun hfg z

/-- Restriction of the invariance group, as a `ℂ`-linear map. -/
def ofLeₗ [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) :
    ModularForm Γ k →ₗ[ℂ] ModularForm Γ' k where
  toFun := ofLe h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma ofLeₗ_apply [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ofLeₗ h f = ofLe h f := (rfl)

lemma ofLeₗ_injective [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) :
    Function.Injective (ofLeₗ h : ModularForm Γ k → _) :=
  ofLe_injective h

/-- A modular form for `Γ'` which is slash invariant under a group `Γ` every cusp of which is a
cusp of `Γ'` is a modular form for `Γ`. The hypothesis `hc` on cusps is what makes this
legitimate: without it, enlarging the invariance group can create cusps at which nothing is
known. Two arithmetic groups always satisfy it
(`Subgroup.IsArithmetic.isCusp_of_isCusp`). -/
def ofSlashInvariant (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : ModularForm Γ' k)
    (hf : ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f) : ModularForm Γ k where
  toFun := f
  slash_action_eq' := hf
  holo' := f.holo'
  bdd_at_cusps' hc' := f.bdd_at_cusps' (hc _ hc')

@[simp]
lemma coe_ofSlashInvariant (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : ModularForm Γ' k)
    (hf : ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f) : ⇑(ofSlashInvariant hc f hf) = ⇑f := (rfl)

/-- For `Γ' ≤ Γ` with every cusp of `Γ` a cusp of `Γ'`, a modular form for `Γ'` comes from a
modular form for `Γ` exactly when it is `Γ`-slash invariant. -/
lemma mem_range_ofLeₗ_iff [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ)
    (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : ModularForm Γ' k) :
    f ∈ LinearMap.range (ofLeₗ h) ↔ ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f :=
  ⟨by rintro ⟨g, rfl⟩ γ hγ; exact g.slash_action_eq' γ hγ,
    fun hf ↦ ⟨ofSlashInvariant hc f hf, rfl⟩⟩

end ModularForm

namespace CuspForm

/-- A cusp form for `Γ` is a cusp form for any subgroup `Γ' ≤ Γ`. -/
def ofLe (h : Γ' ≤ Γ) (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f
  slash_action_eq' _ hγ := f.slash_action_eq' _ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[simp]
lemma coe_ofLe (h : Γ' ≤ Γ) (f : CuspForm Γ k) : ⇑(ofLe h f) = ⇑f := (rfl)

lemma ofLe_injective (h : Γ' ≤ Γ) : Function.Injective (ofLe h : CuspForm Γ k → _) :=
  fun _ _ hfg ↦ ext fun z ↦ DFunLike.congr_fun hfg z

/-- Restriction of the invariance group, as a `ℂ`-linear map. -/
def ofLeₗ [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) : CuspForm Γ k →ₗ[ℂ] CuspForm Γ' k where
  toFun := ofLe h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma ofLeₗ_apply [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    ofLeₗ h f = ofLe h f := (rfl)

lemma ofLeₗ_injective [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ) :
    Function.Injective (ofLeₗ h : CuspForm Γ k → _) :=
  ofLe_injective h

/-- A cusp form for `Γ'` which is slash invariant under a group `Γ` every cusp of which is a
cusp of `Γ'` is a cusp form for `Γ`; see `ModularForm.ofSlashInvariant` for why the cusp
hypothesis is needed. -/
def ofSlashInvariant (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : CuspForm Γ' k)
    (hf : ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f) : CuspForm Γ k where
  toFun := f
  slash_action_eq' := hf
  holo' := f.holo'
  zero_at_cusps' hc' := f.zero_at_cusps' (hc _ hc')

@[simp]
lemma coe_ofSlashInvariant (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : CuspForm Γ' k)
    (hf : ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f) : ⇑(ofSlashInvariant hc f hf) = ⇑f := (rfl)

/-- For `Γ' ≤ Γ` with every cusp of `Γ` a cusp of `Γ'`, a cusp form for `Γ'` comes from a cusp
form for `Γ` exactly when it is `Γ`-slash invariant. -/
lemma mem_range_ofLeₗ_iff [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ)
    (hc : ∀ c, IsCusp c Γ → IsCusp c Γ') (f : CuspForm Γ' k) :
    f ∈ LinearMap.range (ofLeₗ h) ↔ ∀ γ ∈ Γ, ⇑f ∣[k] γ = ⇑f :=
  ⟨by rintro ⟨g, rfl⟩ γ hγ; exact g.slash_action_eq' γ hγ,
    fun hf ↦ ⟨ofSlashInvariant hc f hf, rfl⟩⟩

end CuspForm

end OfLe
