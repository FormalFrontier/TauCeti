/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Nat.Prime.Int
import TauCeti.Data.ZMod.Divisibility
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.Algebra.GroupWithZero.Divisibility
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Units
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The level-raising degeneracy maps `V_d`

For a positive integer `d`, the *level-raising* (or *degeneracy*) map `V_d` sends a function on
the upper half-plane to `τ ↦ f (d τ)`. It is the slash action by `diag(d, 1)`, renormalized by
`d ^ (1 - k)` so that no power of `d` is introduced.

Properties of `f` transport **up** to `V_d f` — the level of the congruence subgroup, the
eigenvalue and nebentypus transport, the `q`-expansion — which is what makes `V_d` a map of
modular forms. Two of them also read back **down**: the slash transformation law
(`slash_conjScale_eq_smul_of_slash_scaleGL`) and holomorphy
(`mdifferentiable_of_comp_scaleGL_smul`), which is what recognizes a bare function as a form at
the lower level. The `q`-expansion results go up only.

## Main definitions

* `TauCeti.scaleGL d`: the diagonal element `!![d, 0; 0, 1]` of `GL(2, ℝ)`, a value of
  `TauCeti.diagGL`.
* `TauCeti.conjScale`: its conjugation action on an integral matrix whose lower-left entry is
  divisible by `d`, `(a, b; d c, e) ↦ (a, d b; c, e)`.
* `TauCeti.ModularForm.levelRaise`, `TauCeti.CuspForm.levelRaise`: the operator `V_d`, taking a
  form for `𝒢` to a form for any group `𝒢'` conjugated into `𝒢` by `diag(d, 1)`, together with
  their `ℂ`-linear packagings `levelRaiseₗ`.

## Main results

* `TauCeti.ModularForm.levelRaise_apply`: `(V_d f) τ = f (d τ)`, the defining formula from which
  the algebraic properties (`levelRaise_one_apply`, `ModularForm.levelRaise_one`,
  `levelRaise_levelRaise`, `levelRaise_injective`) all follow by `ext`.
* `TauCeti.slash_mapGL_eq_self_of_mem_Gamma1_div`: a function whose level-raise carries a
  nebentypus that factors through `N / l` is invariant under all of `Γ₁(N / l)`.
* `TauCeti.Gamma1_map_le_conjAct_scaleGL`, `TauCeti.Gamma0_map_le_conjAct_scaleGL`: the level
  transport, `Γ₁(dM) ≤ diag(d,1)⁻¹ Γ₁(M) diag(d,1)` and likewise for `Γ₀`, which is what makes
  `V_d` a map `M_k(Γ₁(M)) → M_k(Γ₁(dM))`.
* `TauCeti.exists_eq_T_zpow_mul_conjScale_mul_T_zpow`: the `T`-factorisation, in the other
  direction. For `l ∣ N`, every `γ' ∈ Γ₀(N / l)` is `T ^ i * conjScale l γ c * T ^ j` for some
  `i, j, c : ℤ` and some `γ ∈ Γ₀(N)` whose lower-left entry factors as `γ 1 0 = l * c` — a level
  can be raised back from `N / l` to `N` at the cost of two translations — together with the
  bookkeeping `γ 1 1 = γ' 1 1 - γ' 1 0 * j` that pins the lower-right entry of `γ`, which is what
  a nebentypus of level `N` reads off it.
* `TauCeti.ModularForm.slash_levelRaise_eq_smul`, `TauCeti.CuspForm.slash_levelRaise_eq_smul`:
  the eigenvalue transport. Slashing `V_d f` by `γ` produces the same scalar that slashing `f`
  by the conjugate matrix `conjScale d γ` does.
* `TauCeti.CuspForm.diamondOpCusp_levelRaise`: `V_d` intertwines diamond operators between a
  divisor level and any multiple of the raised level.
* `TauCeti.ModularForm.levelRaise_mem_modFormCharSpace_of_dvd`,
  `TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd`: the nebentypus transport, stated
  at every level `N` with `d * M ∣ N`. Since the `diag(d, 1)`-conjugate of a `Γ₀(N)` matrix lies
  in `Γ₀(M)` with the same lower-right entry, `V_d` carries `M_k(Γ₁(M), χ)` into
  `M_k(Γ₁(N), χ ∘ ZMod.unitsMap)`, and likewise for `S_k`: the nebentypus of `V_d f` is that of
  `f` read along `(ZMod N)ˣ → (ZMod M)ˣ`.
* `TauCeti.ModularForm.levelRaise_mem_modFormCharSpace`,
  `TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace`: the `N = d * M` case, the transport to
  exactly the raised level.
* `TauCeti.ModularForm.ofLe_mem_modFormCharSpace`,
  `TauCeti.CuspForm.ofLe_mem_cuspFormCharSpace`: the same transport for the degeneracy map
  `V₁` at a divisor. Reading a form of level `M` as a form of level `N` for any `M ∣ N` carries
  `M_k(Γ₁(M), χ)` into `M_k(Γ₁(N), χ ∘ ZMod.unitsMap)`, and likewise for `S_k`. These are the
  `d = 1` case of the two theorems above, restated for the subgroup inclusion `ofLe`; the
  restatement is exactly `ModularForm.levelRaise_one` and `CuspForm.levelRaise_one`, so no
  nebentypus argument is repeated for them.
* `TauCeti.slash_conjScale_eq_smul_of_slash_scaleGL`,
  `TauCeti.mdifferentiable_of_comp_scaleGL_smul`: the descent, for an `f : ℍ → ℂ` not assumed to
  be a form. If the level-raise of `f` is an eigenvector of the slash by `γ`, then `f` is one
  for `conjScale d γ` with the same eigenvalue, and if the level-raise of `f` is holomorphic
  then so is `f`. These are what read a transformation law and holomorphy back down from
  `V_d f` to `f`, as the level-lowering step of the conductor theorem does.
* `TauCeti.ModularForm.qExpansion_levelRaise`, `TauCeti.CuspForm.qExpansion_levelRaise`: the
  `q`-expansion of `V_d f` is that of `f` with `q` replaced by `q ^ d`, that is, its
  `PowerSeries.expand d`; on coefficients (`TauCeti.ModularForm.qExpansion_levelRaise_coeff`
  and `TauCeti.CuspForm.qExpansion_levelRaise_coeff`), `aₙ(V_d f) = a_{n/d}(f)` for `d ∣ n` and
  `0` otherwise.

The old subspace of Layer 3 of the ModularForms roadmap is spanned by the images of the `V_d`,
and the conductor statement of Layer 4 is phrased with this normalization of `V_d`.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.6
* Miyake, *Modular forms*, §4.6
* The `T`-factorisation section is ported from the AINTLIB `LeanModularForms` project
  (Chris Birkbeck),
  [`HeckeRIngs/GL2/LevelRaise.lean`](https://github.com/CBirkbeck/AINTLIB), declarations
  `exists_T_levelRaiseConj_T_factor` (:491) and its supports
  `eq_T_zpow_mul_levelRaiseConj_mul_T_zpow` (:471), `primeProductCoprime` (:410),
  `dvd_primeProductCoprime_of_not_dvd` (:413), `not_dvd_primeProductCoprime_of_dvd` (:419),
  `exists_shift_isCoprime` (:430), `shiftJ` (:450), `shiftJ_spec` (:453) and
  `natCast_dvd_levelRaiseConj_lower_left` (:465), all Apache-2.0 at commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`. The source's `levelRaiseConjOfDvd` (:98) is this
  file's `conjScale`, so the statement is phrased with `conjScale` and TauCeti's `Gamma0` API
  rather than porting a second conjugation; the source's `shiftJ`/`shiftJ_spec` pair is not
  ported at all, its Bézout step being TauCeti's existing `ZMod.exists_dvd_sub_val_mul`.
* The descent section adapts [AINTLIB](https://github.com/CBirkbeck/AINTLIB) commit
  `2baa76f74`, Apache-2.0, Chris Birkbeck,
  `projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean` lines 84-137 —
  the level-lowering block of `conductor_theorem_dichotomy_cuspForm_strong`. Half of that block
  is deliberately not ported: `ModularGroup_T_mem_Gamma1`, `conductor_slash_levelRaise_eq` and
  `smul_levelRaiseFun` already exist here in more general form (`T_zpow_mem_Gamma1`,
  `ModularForm.slash_levelRaise_eq_smul` with `mem_modFormCharSpace_iff_nebentypus`, and the
  `ℂ`-linearity of `levelRaiseₗ`), and AINTLIB's two `fun_eq_..._inv_smul` lemmas are not
  needed, mathlib's `mdifferentiable_smul` reaching the holomorphy descent directly.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function

open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {k : ℤ} {d : ℕ}

/-! ### The scaling matrix `diag(d, 1)` -/

/-- The diagonal element `!![d, 0; 0, 1]` of `GL(2, ℝ)`, for `d` a nonzero natural number.
Slashing by it is, up to the normalizing scalar `d ^ (1 - k)`, the level-raising operator
`V_d`. -/
def scaleGL (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  diagGL ![Units.mk0 (d : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne d)), 1]

@[simp]
lemma coe_scaleGL [NeZero d] :
    ((scaleGL d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] := by
  rw [scaleGL, diagGL_coe, Matrix.diagonal_fin_two]
  simp

lemma coe_inv_scaleGL [NeZero d] :
    (((scaleGL d)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ)⁻¹, 0; 0, 1] := by
  rw [scaleGL, ← map_inv, diagGL_coe, Matrix.diagonal_fin_two]
  simp

lemma val_det_scaleGL [NeZero d] : ((scaleGL d).det : ℝ) = d := by
  rw [scaleGL, det_diagGL]
  simp [Fin.prod_univ_two]

lemma val_det_scaleGL_pos [NeZero d] : 0 < ((scaleGL d).det : ℝ) := by
  rw [val_det_scaleGL]
  exact mod_cast Nat.pos_of_ne_zero (NeZero.ne d)

@[simp]
lemma denom_scaleGL [NeZero d] (τ : ℍ) : denom (scaleGL d) τ = 1 := by
  simp [UpperHalfPlane.denom]

@[simp]
lemma coe_scaleGL_smul [NeZero d] (τ : ℍ) : ((scaleGL d • τ : ℍ) : ℂ) = d * τ := by
  rw [coe_smul_of_det_pos val_det_scaleGL_pos]
  simp [UpperHalfPlane.num]

@[simp]
lemma scaleGL_one : scaleGL 1 = 1 := by
  rw [scaleGL, ← map_one diagGL]
  congr 1
  ext i
  fin_cases i <;> simp

lemma scaleGL_mul (d e : ℕ) [NeZero d] [NeZero e] :
    scaleGL (d * e) = scaleGL d * scaleGL e := by
  rw [scaleGL, scaleGL, scaleGL, ← map_mul diagGL]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Slashing by `diag(d, 1)` rescales the argument and introduces the factor `d ^ (k - 1)`. -/
lemma slash_scaleGL_apply [NeZero d] (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] scaleGL d) τ = (d : ℂ) ^ (k - 1) * f (scaleGL d • τ) := by
  rw [ModularForm.slash_apply, σ_eq_refl_of_det_pos val_det_scaleGL_pos]
  simp [mul_comm]

/-- **The defining formula for `V_d`, for a bare function**: the renormalized slash
`d ^ (1 - k) • (f ∣[k] diag(d, 1))` is `τ ↦ f (d τ)`, with no stray power of `d`. This is
`ModularForm.levelRaise_apply` for an `f : ℍ → ℂ` that is not yet known to be a modular form,
which is the situation of the conductor theorem: there the transformation law of `f` is what is
being proved, so `f` cannot be assumed to carry one.

Stated between functions rather than pointwise, because that is the form in which a hypothesis
`⇑g = d ^ (1 - k) • (f ∣[k] diag(d, 1))` is rewritten; `congrFun` gives the values. It is not a
`simp` lemma: `Pi.smul_apply` takes the pointwise left-hand side out of simp-normal form. -/
lemma smul_slash_scaleGL_eq [NeZero d] (k : ℤ) (f : ℍ → ℂ) :
    (d : ℂ) ^ (1 - k) • (f ∣[k] scaleGL d) = fun τ ↦ f (scaleGL d • τ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, slash_scaleGL_apply, ← mul_assoc, ← zpow_add₀ hd]
  simp

/-! ### The level-raising operator -/

section LevelRaise

variable {𝒢 𝒢' 𝒢'' : Subgroup (GL (Fin 2) ℝ)}

/-- Membership in `diag(d,1)⁻¹ 𝒢 diag(d,1)`, spelled out as a conjugation condition. -/
lemma mem_conjAct_inv_scaleGL_iff [NeZero d] {g : GL (Fin 2) ℝ} :
    g ∈ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢 ↔ scaleGL d * g * (scaleGL d)⁻¹ ∈ 𝒢 := by
  rw [map_inv, 𝒢.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]

/-- The conjugation conditions compose: if `𝒢''` is conjugated into `𝒢'` by `diag(d,1)` and
`𝒢'` into `𝒢` by `diag(e,1)`, then `𝒢''` is conjugated into `𝒢` by `diag(de,1)`. -/
lemma le_conjAct_inv_scaleGL_mul {d e : ℕ} [NeZero d] [NeZero e]
    (h₁ : 𝒢'' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢')
    (h₂ : 𝒢' ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • 𝒢) :
    𝒢'' ≤ ConjAct.toConjAct (scaleGL (e * d))⁻¹ • 𝒢 := by
  intro g hg
  have k₁ : scaleGL d * g * (scaleGL d)⁻¹ ∈ 𝒢' := mem_conjAct_inv_scaleGL_iff.mp (h₁ hg)
  have k₂ := mem_conjAct_inv_scaleGL_iff.mp (h₂ k₁)
  have key : scaleGL (e * d) * g * (scaleGL (e * d))⁻¹ =
      scaleGL e * (scaleGL d * g * (scaleGL d)⁻¹) * (scaleGL e)⁻¹ := by
    rw [scaleGL_mul]; group
  rw [mem_conjAct_inv_scaleGL_iff, key]
  exact k₂

/-- At `d = 1` the conjugation condition *is* the subgroup inclusion: `diag(1, 1)` is the
identity, so `𝒢' ≤ diag(1, 1)⁻¹ 𝒢 diag(1, 1)` says no more than `𝒢' ≤ 𝒢`. This is what lets
`levelRaise_one` name its `ofLe` without carrying a second inclusion hypothesis. -/
lemma le_of_le_conjAct_inv_scaleGL_one (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢) :
    𝒢' ≤ 𝒢 := by
  simpa using h

namespace ModularForm

/-- The level-raising (degeneracy) operator `V_d`, `(V_d f) τ = f (d τ)`, as a map from modular
forms for `𝒢` to modular forms for a group `𝒢'` conjugated into `𝒢` by `diag(d, 1)`. -/
def levelRaise [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) : ModularForm 𝒢' k :=
  ((d : ℂ) ^ (1 - k)) • _root_.ModularForm.ofLe h (_root_.ModularForm.translate f (scaleGL d))

lemma coe_levelRaise [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    ⇑(levelRaise d h f) = (d : ℂ) ^ (1 - k) • (⇑f ∣[k] scaleGL d) := by
  unfold levelRaise
  rw [FunLike.coe_smul, _root_.ModularForm.coe_ofLe, _root_.ModularForm.coe_translate]

/-- **The defining formula for `V_d`**: `(V_d f) τ = f (d τ)`, with no stray power of `d`.
The algebraic properties of `V_d` all follow from this by `ext`. -/
@[simp]
lemma levelRaise_apply [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) (τ : ℍ) :
    levelRaise d h f τ = f (scaleGL d • τ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [congrFun (coe_levelRaise h f) τ, Pi.smul_apply, smul_eq_mul, slash_scaleGL_apply,
    ← mul_assoc, ← zpow_add₀ hd]
  simp

/-- The level-raising operator, as a `ℂ`-linear map. -/
def levelRaiseₗ [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    ModularForm 𝒢 k →ₗ[ℂ] ModularForm 𝒢' k where
  toFun := levelRaise d h
  map_add' f g := by ext τ; simp
  map_smul' c f := by ext τ; simp

@[simp]
lemma levelRaiseₗ_apply [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    levelRaiseₗ d h f = levelRaise d h f := (rfl)

/-- `V_d` is injective: `f (d τ)` determines `f`, since `τ ↦ d τ` is a bijection of `ℍ`. -/
lemma levelRaise_injective [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaise (k := k) d h) := by
  intro f g hfg
  refine _root_.ModularForm.ext fun τ ↦ ?_
  have := congr($hfg ((scaleGL d)⁻¹ • τ))
  simpa [smul_smul] using this

/-- `V_d` is injective as a `ℂ`-linear map, so its range is a copy of `M_k(𝒢)` inside
`M_k(𝒢')`. -/
lemma levelRaiseₗ_injective [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaiseₗ (k := k) d h) :=
  levelRaise_injective h

/-- `V₁` is the restriction map: it changes nothing but the invariance group. -/
lemma levelRaise_one_apply [𝒢'.HasDetOne] (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢)
    (f : ModularForm 𝒢 k) (τ : ℍ) : levelRaise 1 h f τ = f τ := by
  simp

/-- **`V₁` is the restriction map, as forms.** The pointwise statement of
`TauCeti.ModularForm.levelRaise_one_apply`, packaged as an equality of modular forms: at `d = 1`
the level-raising operator *is* `ofLe`. This is what lets a statement about `V_d` be specialised
to one about restriction along `𝒢' ≤ 𝒢`, rather than reproved for it.

It is stated in the root `ModularForm` namespace, beside `ModularForm.ofLe`, so that dot
notation on a `ModularForm` resolves. -/
@[simp]
lemma _root_.ModularForm.levelRaise_one [𝒢'.HasDetOne]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    levelRaise 1 h f = _root_.ModularForm.ofLe (le_of_le_conjAct_inv_scaleGL_one h) f :=
  _root_.ModularForm.ext fun τ ↦ (levelRaise_one_apply h f τ).trans
    (congrFun (_root_.ModularForm.coe_ofLe _ f) τ).symm

/-- The level-raising operators compose: `V_d ∘ V_e = V_{de}`. -/
@[simp]
lemma levelRaise_levelRaise {d e : ℕ} [𝒢'.HasDetOne] [𝒢''.HasDetOne] [NeZero d] [NeZero e]
    (h₁ : 𝒢'' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢')
    (h₂ : 𝒢' ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    levelRaise d h₁ (levelRaise e h₂ f) =
      levelRaise (e * d) (le_conjAct_inv_scaleGL_mul h₁ h₂) f := by
  refine _root_.ModularForm.ext fun τ ↦ ?_
  simp [scaleGL_mul, mul_smul]

end ModularForm

namespace CuspForm

/-- The level-raising (degeneracy) operator `V_d` on cusp forms, `(V_d f) τ = f (d τ)`. -/
def levelRaise [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) : CuspForm 𝒢' k :=
  ((d : ℂ) ^ (1 - k)) • _root_.CuspForm.ofLe h (_root_.CuspForm.translate f (scaleGL d))

lemma coe_levelRaise [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    ⇑(levelRaise d h f) = (d : ℂ) ^ (1 - k) • (⇑f ∣[k] scaleGL d) := by
  unfold levelRaise
  rw [FunLike.coe_smul, _root_.CuspForm.coe_ofLe, _root_.CuspForm.coe_translate_gl]

/-- **The defining formula for `V_d` on cusp forms**: `(V_d f) τ = f (d τ)`, with no stray
power of `d`. -/
@[simp]
lemma levelRaise_apply [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) (τ : ℍ) :
    levelRaise d h f τ = f (scaleGL d • τ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [congrFun (coe_levelRaise h f) τ, Pi.smul_apply, smul_eq_mul, slash_scaleGL_apply,
    ← mul_assoc, ← zpow_add₀ hd]
  simp

/-- The level-raising operator on cusp forms, as a `ℂ`-linear map. -/
def levelRaiseₗ [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    CuspForm 𝒢 k →ₗ[ℂ] CuspForm 𝒢' k where
  toFun := levelRaise d h
  map_add' f g := by ext τ; simp
  map_smul' c f := by ext τ; simp

@[simp]
lemma levelRaiseₗ_apply [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    levelRaiseₗ d h f = levelRaise d h f := (rfl)

/-- `V_d` is injective on cusp forms: `f (d τ)` determines `f`, since `τ ↦ d τ` is a bijection
of `ℍ`. -/
lemma levelRaise_injective [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaise (k := k) d h) := by
  intro f g hfg
  refine _root_.CuspForm.ext fun τ ↦ ?_
  have := congr($hfg ((scaleGL d)⁻¹ • τ))
  simpa [smul_smul] using this

/-- `V_d` is injective as a `ℂ`-linear map on cusp forms, so its range is a copy of `S_k(𝒢)`
inside `S_k(𝒢')`. These ranges are what span the old subspace. -/
lemma levelRaiseₗ_injective [𝒢.HasDetOne] [𝒢'.HasDetOne] (d : ℕ) [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaiseₗ (k := k) d h) :=
  levelRaise_injective h

/-- `V₁` is the restriction map: it changes nothing but the invariance group. -/
lemma levelRaise_one_apply [𝒢'.HasDetOne] (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢)
    (f : CuspForm 𝒢 k) (τ : ℍ) : levelRaise 1 h f τ = f τ := by
  simp

/-- **`V₁` is the restriction map, as forms.** The pointwise statement of
`TauCeti.CuspForm.levelRaise_one_apply`, packaged as an equality of cusp forms: at `d = 1` the
level-raising operator *is* `ofLe`. This is what lets a statement about `V_d` be specialised to
one about restriction along `𝒢' ≤ 𝒢`, rather than reproved for it.

It is stated in the root `CuspForm` namespace, beside `CuspForm.ofLe`, so that dot notation
on a `CuspForm` resolves. -/
@[simp]
lemma _root_.CuspForm.levelRaise_one [𝒢'.HasDetOne]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    levelRaise 1 h f = _root_.CuspForm.ofLe (le_of_le_conjAct_inv_scaleGL_one h) f :=
  _root_.CuspForm.ext fun τ ↦ (levelRaise_one_apply h f τ).trans
    (congrFun (_root_.CuspForm.coe_ofLe _ f) τ).symm

/-- The level-raising operators compose: `V_d ∘ V_e = V_{de}`. -/
@[simp]
lemma levelRaise_levelRaise {d e : ℕ} [𝒢'.HasDetOne] [𝒢''.HasDetOne] [NeZero d] [NeZero e]
    (h₁ : 𝒢'' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢')
    (h₂ : 𝒢' ≤ ConjAct.toConjAct (scaleGL e)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    levelRaise d h₁ (levelRaise e h₂ f) =
      levelRaise (e * d) (le_conjAct_inv_scaleGL_mul h₁ h₂) f := by
  refine _root_.CuspForm.ext fun τ ↦ ?_
  simp [scaleGL_mul, mul_smul]

end CuspForm

end LevelRaise

/-! ### Level transport for the congruence subgroups -/

section Transport

/-- The `diag(d, 1)`-conjugate of an integral matrix whose lower-left entry is `d * c`: the
entries are rearranged as `(a, b; d c, e) ↦ (a, d b; c, e)`, which is again integral of
determinant one. -/
def conjScale (d : ℕ) (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = d * c) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], by
    have hdet : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 :=
      Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    rw [hc] at hdet
    rw [Matrix.det_fin_two_of]
    linarith [hdet]⟩

@[simp]
lemma coe_conjScale (d : ℕ) (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = d * c) :
    ((conjScale d γ c hc : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1] := by
  rw [conjScale]

/-- Conjugation by `diag(d, 1)` realizes `conjScale`. -/
lemma mapGL_conjScale [NeZero d] (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = d * c) :
    scaleGL d * mapGL ℝ γ * (scaleGL d)⁻¹ = mapGL ℝ (conjScale d γ c hc) := by
  have hc' : ((γ 1 0 : ℤ) : ℝ) = d * (c : ℝ) := by exact_mod_cast congrArg Int.cast hc
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc', mul_comm]

/-- **Level transport for `Γ₁`**: conjugation by `diag(d, 1)` carries `Γ₁(dM)` into `Γ₁(M)`.
This is what makes `V_d` a map `M_k(Γ₁(M)) → M_k(Γ₁(dM))`. -/
theorem Gamma1_map_le_conjAct_scaleGL (M d : ℕ) [NeZero d] :
    ((Gamma1 (d * M)).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (scaleGL d)⁻¹ • ((Gamma1 M).map (mapGL ℝ)) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_conjAct_inv_scaleGL_iff]
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem _ _).mp hγ
  obtain ⟨t, ht⟩ : ((d * M : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hc : γ 1 0 = d * ((M : ℤ) * t) := by rw [ht]; push_cast; ring
  have hdM : M ∣ d * M := Dvd.intro_left d rfl
  -- the diagonal entries only need their congruence read modulo the divisor `M` of `dM`
  exact ⟨conjScale d γ _ hc, (Gamma1_mem _ _).mpr
    ⟨by simpa using congrArg (ZMod.castHom hdM (ZMod M)) h00,
      by simpa using congrArg (ZMod.castHom hdM (ZMod M)) h11, by simp⟩,
    (mapGL_conjScale γ _ hc).symm⟩

/-- **Level transport at a divisor.** Whenever `d * M ∣ N`, conjugation by `diag(d, 1)` carries
`Γ₁(N)` into `Γ₁(M)`: this is what makes `V_d` a map `S_k(Γ₁(M)) → S_k(Γ₁(N))`, not only for
`N = d * M` but for every multiple of it. -/
theorem Gamma1_map_le_conjAct_scaleGL_of_dvd {M d N : ℕ} [NeZero d] (h : d * M ∣ N) :
    ((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (scaleGL d)⁻¹ • ((Gamma1 M).map (mapGL ℝ)) :=
  (Gamma1_map_le_Gamma1_map_of_dvd h).trans (Gamma1_map_le_conjAct_scaleGL M d)

/-- **Level transport for `Γ₀`**: conjugation by `diag(d, 1)` carries `Γ₀(dM)` into `Γ₀(M)`. -/
theorem Gamma0_map_le_conjAct_scaleGL (M d : ℕ) [NeZero d] :
    ((Gamma0 (d * M)).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (scaleGL d)⁻¹ • ((Gamma0 M).map (mapGL ℝ)) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_conjAct_inv_scaleGL_iff]
  obtain ⟨t, ht⟩ : ((d * M : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  have hc : γ 1 0 = d * ((M : ℤ) * t) := by rw [ht]; push_cast; ring
  exact ⟨conjScale d γ _ hc, Gamma0_mem.mpr (by simp), (mapGL_conjScale γ _ hc).symm⟩

end Transport

/-! ### The `T`-factorisation of `Γ₀(N / l)` -/

section TFactor

/-- The product of those primes of `l` that do not divide `a`. Subtracting that multiple of `c`
from `a` clears every prime of `l` out of `a` in one step; see `exists_sub_mul_isCoprime`. -/
private def primeProductCoprime (a : ℤ) (l : ℕ) : ℕ :=
  (l.primeFactors.filter fun p : ℕ ↦ ¬(p : ℤ) ∣ a).prod id

/-- A prime of `l` that misses `a` divides `primeProductCoprime a l`. -/
private lemma dvd_primeProductCoprime_of_not_dvd {a : ℤ} {l p : ℕ} (hp : p ∈ l.primeFactors)
    (hpa : ¬(p : ℤ) ∣ a) : (p : ℤ) ∣ (primeProductCoprime a l : ℤ) :=
  mod_cast Finset.dvd_prod_of_mem id (Finset.mem_filter.mpr ⟨hp, hpa⟩)

/-- A prime dividing `a` does not divide `primeProductCoprime a l`, whose factors all miss `a`. -/
private lemma not_dvd_primeProductCoprime_of_dvd {a : ℤ} {l p : ℕ} (hp : p.Prime)
    (hpa : (p : ℤ) ∣ a) : ¬(p : ℤ) ∣ (primeProductCoprime a l : ℤ) := by
  intro hdvd
  rw [Int.natCast_dvd_natCast] at hdvd
  obtain ⟨q, hq_mem, hq_dvd⟩ := (Prime.dvd_finsetProd_iff hp.prime id).mp hdvd
  obtain ⟨hq_pf, hqa⟩ := Finset.mem_filter.mp hq_mem
  exact hqa ((Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq_pf)).mp hq_dvd ▸ hpa)

/-- **A coprime shift.** If `a` and `c` are coprime then some translate `a - i * c` is coprime to
a prescribed nonzero modulus `l`: clear the primes of `l` that divide `a` by hand, and the primes
that do not are already cleared because they would otherwise have to divide `c`. -/
private lemma exists_sub_mul_isCoprime (a c : ℤ) (l : ℕ) [NeZero l] (hac : IsCoprime a c) :
    ∃ i : ℤ, IsCoprime (a - i * c) (l : ℤ) := by
  refine ⟨(primeProductCoprime a l : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, Int.natAbs_natCast]
  by_contra hne
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
  rw [Nat.dvd_gcd_iff] at hp_dvd
  obtain ⟨hp_dvd_x, hp_dvd_l⟩ := hp_dvd
  have hp_dvd_x_int : (p : ℤ) ∣ a - (primeProductCoprime a l : ℤ) * c := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpa : (p : ℤ) ∣ a
  · rcases hp_int.dvd_mul.mp (by simpa using dvd_sub hpa hp_dvd_x_int) with h | h
    · exact not_dvd_primeProductCoprime_of_dvd hp hpa h
    · exact hp_int.not_isUnit (hac.isUnit_of_dvd' hpa h)
  · exact hpa (by
      simpa using dvd_add hp_dvd_x_int
        ((dvd_primeProductCoprime_of_not_dvd
          (Nat.mem_primeFactors.mpr ⟨hp, hp_dvd_l, NeZero.ne l⟩) hpa).mul_right c))

/-- Membership in `Γ₀(N)` from a factored lower-left entry: if `l ∣ N` and `γ 1 0 = l * c` with
`N / l ∣ c`, then `γ ∈ Γ₀(N)`. -/
private lemma mem_Gamma0_of_eq_mul_of_dvd {l N : ℕ} (hlN : l ∣ N) {γ : SL(2, ℤ)} {c : ℤ}
    (hc : γ 1 0 = l * c) (hdvd : ((N / l : ℕ) : ℤ) ∣ c) : γ ∈ Gamma0 N := by
  refine Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_)
  rw [hc, ← Nat.mul_div_cancel' hlN, Nat.cast_mul]
  exact mul_dvd_mul_left _ hdvd

/-- **The `T`-factorisation of `Γ₀(N / l)`.** For `l ∣ N`, every `γ' ∈ Γ₀(N / l)` is a product
`T ^ i * conjScale l γ c * T ^ j` for some `i, j, c : ℤ` and some `γ ∈ Γ₀(N)` whose lower-left
entry factors as `γ 1 0 = l * c`: the level of `γ'` can be raised back from `N / l` to `N` at the
cost of two translations. Since `conjScale` and the translations all fix the lower-right entry up
to the recorded shift, the last conjunct `γ 1 1 = γ' 1 1 - γ' 1 0 * j` pins the lower-right entry
of `γ`, which is what a nebentypus of level `N` reads off it. -/
theorem exists_eq_T_zpow_mul_conjScale_mul_T_zpow (l N : ℕ) [NeZero l] (hlN : l ∣ N) (γ' : SL(2, ℤ))
    (hγ' : γ' ∈ Gamma0 (N / l)) : ∃ (i j c : ℤ) (γ : SL(2, ℤ)) (hc : γ 1 0 = l * c),
      γ ∈ Gamma0 N ∧ γ' = ModularGroup.T ^ i * conjScale l γ c hc * ModularGroup.T ^ j ∧
        γ 1 1 = γ' 1 1 - γ' 1 0 * j := by
  have hdet : γ' 0 0 * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ'
  -- move the upper-left entry, along its own column, until it is coprime to `l`
  obtain ⟨i, hi⟩ := exists_sub_mul_isCoprime (γ' 0 0) (γ' 1 0) l
    ⟨γ' 1 1, -γ' 0 1, by linear_combination hdet⟩
  -- then clear the upper-right entry modulo `l`, which the previous step made possible
  have hunit : IsUnit ((γ' 0 0 - i * γ' 1 0 : ℤ) : ZMod l) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr (isCoprime_comm.mp hi)
  obtain ⟨j₀, k, hk⟩ :=
    ZMod.exists_dvd_sub_val_mul l (γ' 0 1 - i * γ' 1 1) (γ' 0 0 - i * γ' 1 0) hunit
  set j : ℤ := (j₀.val : ℤ) with hj
  have hdetM : (!![γ' 0 0 - i * γ' 1 0, k; (l : ℤ) * γ' 1 0, γ' 1 1 - γ' 1 0 * j]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ' 1 0 * hk
  -- keep `γ` a variable of type `SL(2, ℤ)` until the coercion lemmas have fired
  set γ : SL(2, ℤ) := ⟨_, hdetM⟩ with hγ
  have hc : γ 1 0 = l * γ' 1 0 := by simp [hγ]
  refine ⟨i, j, γ' 1 0, γ, hc, mem_Gamma0_of_eq_mul_of_dvd hlN hc
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ')), ?_, by simp [hγ]⟩
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    ModularGroup.coe_T_zpow, coe_conjScale]
  simp only [hγ, Matrix.SpecialLinearGroup.coe_mk, Matrix.mul_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  conv_lhs => rw [Matrix.eta_fin_two (γ' : Matrix (Fin 2) (Fin 2) ℤ)]
  congrm !![?_, ?_; ?_, ?_] <;> first | linear_combination hk | ring

end TFactor

/-! ### Slashing a level-raise, and the transport of the nebentypus -/

section Slash

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}

/-- Slashing by `diag(d, 1)` and then by an integral matrix `γ` whose lower-left entry is
divisible by `d` is slashing by the conjugate matrix `conjScale d γ` and then by `diag(d, 1)`. -/
lemma slash_scaleGL_slash_mapGL [NeZero d] (F : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℤ}
    (hc : γ 1 0 = d * c) :
    (F ∣[k] scaleGL d) ∣[k] mapGL ℝ γ =
      (F ∣[k] mapGL ℝ (conjScale d γ c hc)) ∣[k] scaleGL d := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul,
    mul_inv_eq_iff_eq_mul.mp (mapGL_conjScale γ c hc)]

/-- Slashing a level-raise by an integral matrix `γ` whose lower-left entry is divisible by `d`
is the level-raise of the slash of `f` by the conjugate matrix `conjScale d γ`. -/
lemma ModularForm.coe_levelRaise_slash [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ =
      (d : ℂ) ^ (1 - k) • ((⇑f ∣[k] mapGL ℝ (conjScale d γ c hc)) ∣[k] scaleGL d) := by
  rw [coe_levelRaise, _root_.ModularForm.smul_slash, σ_mapGL_real_eq_refl,
    ContinuousAlgEquiv.refl_apply, slash_scaleGL_slash_mapGL]

/-- Slashing a level-raised cusp form by an integral matrix `γ` whose lower-left entry is
divisible by `d` is the level-raise of the slash of `f` by the conjugate matrix
`conjScale d γ`. -/
lemma CuspForm.coe_levelRaise_slash [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ =
      (d : ℂ) ^ (1 - k) • ((⇑f ∣[k] mapGL ℝ (conjScale d γ c hc)) ∣[k] scaleGL d) := by
  rw [coe_levelRaise, _root_.ModularForm.smul_slash, σ_mapGL_real_eq_refl,
    ContinuousAlgEquiv.refl_apply, slash_scaleGL_slash_mapGL]

/-- **Eigenvalue transport.** If `f` is an eigenvector of the slash by `conjScale d γ` with
eigenvalue `z`, then `V_d f` is an eigenvector of the slash by `γ` with the same eigenvalue.
Applied to `γ ∈ Γ₀(dM)` this is what transports the nebentypus, in
`levelRaise_mem_modFormCharSpace`. -/
lemma ModularForm.slash_levelRaise_eq_smul [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) {z : ℂ}
    (hf : ⇑f ∣[k] mapGL ℝ (conjScale d γ c hc) = z • ⇑f) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ = z • ⇑(levelRaise d hle f) := by
  rw [coe_levelRaise_slash hle f γ hc, hf, _root_.ModularForm.smul_slash, coe_levelRaise,
    smul_comm]
  congr 1
  rw [σ_eq_refl_of_det_pos val_det_scaleGL_pos, ContinuousAlgEquiv.refl_apply]

/-- **Eigenvalue transport (cusp forms).** If `f` is an eigenvector of the slash by
`conjScale d γ` with eigenvalue `z`, then `V_d f` is an eigenvector of the slash by `γ` with
the same eigenvalue. -/
lemma CuspForm.slash_levelRaise_eq_smul [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) {z : ℂ}
    (hf : ⇑f ∣[k] mapGL ℝ (conjScale d γ c hc) = z • ⇑f) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ = z • ⇑(levelRaise d hle f) := by
  rw [coe_levelRaise_slash hle f γ hc, hf, _root_.ModularForm.smul_slash, coe_levelRaise,
    smul_comm]
  congr 1
  rw [σ_eq_refl_of_det_pos val_det_scaleGL_pos, ContinuousAlgEquiv.refl_apply]

end Slash

/-! ### Descending along the level-raise -/

section Descent

/-- Slashing by a fixed matrix can be cancelled: it is a group action, so slashing by `A⁻¹`
undoes it. -/
private lemma slash_left_cancel (k : ℤ) (A : GL (Fin 2) ℝ) {f g : ℍ → ℂ}
    (h : f ∣[k] A = g ∣[k] A) : f = g := by
  simpa [← SlashAction.slash_mul] using congrArg (· ∣[k] A⁻¹) h

/-- **Eigenvalue descent**, the converse of `ModularForm.slash_levelRaise_eq_smul`. If the
level-raise of `f` is an eigenvector of the slash by `γ` with eigenvalue `z`, then `f` itself is
an eigenvector of the slash by the conjugate matrix `conjScale d γ`, with the same eigenvalue.

Both sides of the hypothesis and of the conclusion scale together, so the normalizing scalar
`d ^ (1 - k)` of `V_d` cancels and does not appear. Applied to `γ ∈ Γ₀(dM)`, this is what
descends a nebentypus through `V_d`: the level-lowering step of the conductor theorem, where
`f` is only known to be a function and this transformation law is what exhibits it as a form. -/
lemma slash_conjScale_eq_smul_of_slash_scaleGL [NeZero d] (f : ℍ → ℂ) (γ : SL(2, ℤ)) {c : ℤ}
    (hc : γ 1 0 = d * c) {z : ℂ}
    (hf : (f ∣[k] scaleGL d) ∣[k] mapGL ℝ γ = z • (f ∣[k] scaleGL d)) :
    f ∣[k] mapGL ℝ (conjScale d γ c hc) = z • f := by
  rw [slash_scaleGL_slash_mapGL f γ hc] at hf
  refine slash_left_cancel k (scaleGL d) ?_
  rw [hf, _root_.ModularForm.smul_slash, σ_eq_refl_of_det_pos val_det_scaleGL_pos,
    ContinuousAlgEquiv.refl_apply]

/-- **Holomorphy descent.** If `τ ↦ f (d τ)` is holomorphic on `ℍ`, then so is `f`. This is
`UpperHalfPlane.mdifferentiable_comp_smul_iff` — holomorphy is invariant under any
positive-determinant Möbius action — read at `g = diag(d, 1)`; with `smul_slash_scaleGL_eq` it
descends holomorphy through `V_d` at every weight. -/
lemma mdifferentiable_of_comp_scaleGL_smul [NeZero d] {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ ↦ f (scaleGL d • τ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  (UpperHalfPlane.mdifferentiable_comp_smul_iff val_det_scaleGL_pos).mp hf

end Descent

/-! ### The nebentypus character of a level-raise -/

section Nebentypus

/-- The lower-left entry of a matrix `γ ∈ Γ₀(dM)` is divisible by `d`, its `diag(d, 1)`-conjugate
`conjScale d γ` again lies in `Γ₀(M)`, and the conjugation leaves the lower-right entry alone: the
diamond label of `γ` is read along the reduction `(ZMod (dM))ˣ → (ZMod M)ˣ`. -/
lemma exists_conjScale_mem_Gamma0 (d M : ℕ) (γ : ↥(Gamma0 (d * M))) :
    ∃ (c : ℤ) (hc : (γ : SL(2, ℤ)) 1 0 = d * c) (hm : conjScale d γ c hc ∈ Gamma0 M),
      (Gamma0Map M).toHomUnits ⟨conjScale d γ c hc, hm⟩ =
        ZMod.unitsMap (Dvd.intro_left d rfl : M ∣ d * M) ((Gamma0Map (d * M)).toHomUnits γ) := by
  obtain ⟨t, ht⟩ : ((d * M : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  have hc : (γ : SL(2, ℤ)) 1 0 = d * ((M : ℤ) * t) := by rw [ht]; push_cast; ring
  refine ⟨_, hc, Gamma0_mem.mpr (by simp), ?_⟩
  ext
  simp [Gamma0Map_apply, ZMod.unitsMap_def]

/-- The `diag(d, 1)`-conjugate of a matrix of `Γ₀(N)` lies in `Γ₀(M)` whenever `d * M ∣ N`, and
the conjugation leaves the lower-right entry alone: the diamond label of `γ` is read along the
reduction `(ZMod N)ˣ → (ZMod M)ˣ`. This is the divisor form of
`TauCeti.exists_conjScale_mem_Gamma0`. -/
lemma exists_conjScale_mem_Gamma0_of_dvd (d M N : ℕ) (hdvd : d * M ∣ N) (γ : ↥(Gamma0 N)) :
    ∃ (c : ℤ) (hc : (γ : SL(2, ℤ)) 1 0 = d * c) (hm : conjScale d γ c hc ∈ Gamma0 M),
      (Gamma0Map M).toHomUnits ⟨conjScale d γ c hc, hm⟩ =
        ZMod.unitsMap ((Dvd.intro_left d rfl).trans hdvd) ((Gamma0Map N).toHomUnits γ) := by
  obtain ⟨c, hc, hm, heq⟩ := exists_conjScale_mem_Gamma0 d M ⟨γ, Gamma0_le_Gamma0_of_dvd hdvd γ.2⟩
  refine ⟨c, hc, hm, heq.trans ?_⟩
  rw [Gamma0Map_toHomUnits_of_dvd hdvd γ, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]

/-- **`V_d` intertwines the diamond operators.** For `d * M ∣ N`, the diamond operator `⟨u⟩` of
level `N` acts on a level-raised form `V_d f` as the diamond operator of level `M` at the
reduction of `u` acts on `f`. Both sides are slashes by a matrix of `Γ₀`, related by the
`diag(d, 1)`-conjugation, which preserves the lower-right entry. -/
theorem CuspForm.diamondOpCusp_levelRaise {M d N : ℕ} [NeZero N]
    (hdvd : d * M ∣ N) (k : ℤ) (u : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
    haveI : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
    diamondOpCusp k u (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f) =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd)
        (diamondOpCusp k (ZMod.unitsMap ((Dvd.intro_left d rfl).trans hdvd) u) f) := by
  let _ : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  let _ : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective u
  obtain ⟨c, hc, hm, heq⟩ := exists_conjScale_mem_Gamma0_of_dvd d M N hdvd γ
  refine DFunLike.coe_injective ?_
  rw [coe_diamondOpCusp k u γ hγ, CuspForm.coe_levelRaise_slash _ f γ hc,
    CuspForm.coe_levelRaise, coe_diamondOpCusp k _ ⟨conjScale d γ c hc, hm⟩ (heq.trans (by
      rw [hγ]))]

/-- **The nebentypus of a level-raise.** For `d * M ∣ N`, `V_d` carries `M_k(Γ₁(M), χ)` into
`M_k(Γ₁(N), χ ∘ (ZMod N)ˣ → (ZMod M)ˣ)`: the character of `V_d f` at level `N` is the character
of `f` read along the reduction map. The target level is any multiple of `d * M`. -/
theorem ModularForm.levelRaise_mem_modFormCharSpace_of_dvd {M d N : ℕ} [NeZero d]
    (hdvd : d * M ∣ N) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans hdvd))) := by
  rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
  intro γ
  obtain ⟨c, hc, hm, heq⟩ := exists_conjScale_mem_Gamma0_of_dvd d M N hdvd γ
  rw [MonoidHom.comp_apply, ← heq]
  exact slash_levelRaise_eq_smul _ f γ hc (hf ⟨_, hm⟩)

/-- **The nebentypus of a level-raise at the exact level.** The `N = d * M` case of
`TauCeti.ModularForm.levelRaise_mem_modFormCharSpace_of_dvd`. -/
theorem ModularForm.levelRaise_mem_modFormCharSpace (M d : ℕ) [NeZero d]
    (χ : (ZMod M)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Dvd.intro_left d rfl : M ∣ d * M))) :=
  levelRaise_mem_modFormCharSpace_of_dvd dvd_rfl χ hf

/-- **The nebentypus of a level-raise (cusp forms).** For `d * M ∣ N`, `V_d` carries
`S_k(Γ₁(M), χ)` into `S_k(Γ₁(N), χ ∘ (ZMod N)ˣ → (ZMod M)ˣ)`: the character of `V_d f` at level
`N` is the character of `f` read along the reduction map.

This is the character half only. That `V_d f` is *old* is the separate statement
`TauCeti.levelRaise_mem_cuspFormsOld`, which additionally needs `M ≠ N` and is about the
character-free `TauCeti.cuspFormsOld N k`. -/
theorem CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd {M d N : ℕ} [NeZero d]
    (hdvd : d * M ∣ N) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap ((Dvd.intro_left d rfl).trans hdvd))) := by
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf ⊢
  intro γ
  obtain ⟨c, hc, hm, heq⟩ := exists_conjScale_mem_Gamma0_of_dvd d M N hdvd γ
  rw [MonoidHom.comp_apply, ← heq]
  exact slash_levelRaise_eq_smul _ f γ hc (hf ⟨_, hm⟩)

/-- **The nebentypus of a level-raise at the exact level (cusp forms).** The `N = d * M` case of
`TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd`. -/
theorem CuspForm.levelRaise_mem_cuspFormCharSpace (M d : ℕ) [NeZero d]
    (χ : (ZMod M)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Dvd.intro_left d rfl : M ∣ d * M))) :=
  levelRaise_mem_cuspFormCharSpace_of_dvd dvd_rfl χ hf

/-- **Γ₁(N/l)-invariance from a nebentypus of level `N` that factors through `N / l`.**

If the level-raise `f ∣[k] V_l` is an eigenvector of every `γ ∈ Γ₀(N)` with eigenvalue the
character value `χ` reads off `γ`, if `f` is `T`-periodic, and if `χ` is trivial on the kernel of
the reduction `(ZMod N)ˣ → (ZMod (N/l))ˣ`, then `f` is invariant under all of `Γ₁(N / l)`.

This is the step that converts a nebentypus into honest invariance, and it is where the conductor
drops: a form whose character already factors through `N / l` is invariant under all of
`Γ₁(N / l)`, the larger congruence subgroup at the lower level, which is what the conductor
argument turns into a statement about newforms.

Adapted from `conductor_slash_eq_self_of_mem_Gamma1_div` in AINTLIB
(`Eigenforms/ConductorTheorem.lean`:217, Chris Birkbeck, Apache-2.0, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`). The source states it over its own `levelRaiseFun`
and a `DirichletCharacter`, and routes through a conductor-specific helper; here it is stated over
`scaleGL` and a units-valued character, and assembled from
`exists_eq_T_zpow_mul_conjScale_mul_T_zpow`,
`slash_zpow_mul_mul_zpow_eq_smul` and
`slash_conjScale_eq_smul_of_slash_scaleGL`. -/
theorem slash_mapGL_eq_self_of_mem_Gamma1_div (l N : ℕ) [NeZero l] (hlN : l ∣ N)
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (hχ : ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hlN) u = 1 → χ u = 1) (f : ℍ → ℂ)
    (hnb : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N),
      (f ∣[k] scaleGL l) ∣[k] mapGL ℝ γ =
        (χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) • (f ∣[k] scaleGL l))
    (hT : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma1 (N / l)) :
    f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = f := by
  obtain ⟨i, j, c, γ, hc, hγ, hfactor, hdiag⟩ :=
    exists_eq_T_zpow_mul_conjScale_mul_T_zpow l N hlN δ (Gamma1_in_Gamma0 _ hδ)
  have hdet := det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨ModularGroup.T, rfl⟩)
  have hconj := slash_conjScale_eq_smul_of_slash_scaleGL (k := k) f γ hc (hnb γ hγ)
  -- the character value is `1`: `γ 1 1` is congruent to `δ 1 1 ≡ 1` modulo `N / l`
  have hchar : (χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) = 1 := by
    obtain ⟨-, hd, hcz⟩ := (Gamma1_mem _ _).mp hδ
    have hγ' : γ ∈ Gamma0 (N / l) := Gamma0_le_Gamma0_of_dvd (Nat.div_dvd_of_dvd hlN) hγ
    -- `Gamma0Map_apply` reads the label as the lower-right entry. Instantiating it here, with the
    -- entry spelled as `hdiag` spells it, keeps the subtype coercion in one named step instead of
    -- leaving it for `rw` to discharge silently.
    have hentry : Gamma0Map (N / l) ⟨γ, hγ'⟩ = ((γ 1 1 : ℤ) : ZMod (N / l)) := Gamma0Map_apply _
    have hlabel : Gamma0Map (N / l) ⟨γ, hγ'⟩ = 1 := by
      rw [hentry, hdiag]
      push_cast
      rw [hd, hcz, zero_mul, sub_zero]
    have hred : ZMod.unitsMap (Nat.div_dvd_of_dvd hlN)
        ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) = 1 := by
      rw [← Gamma0Map_toHomUnits_of_dvd (Nat.div_dvd_of_dvd hlN) ⟨γ, hγ⟩ hγ']
      exact Units.ext hlabel
    rw [hχ _ hred, Units.val_one]
  rw [hfactor, map_mul, map_mul, map_zpow, map_zpow,
    slash_zpow_mul_mul_zpow_eq_smul k f hdet hT hconj i j, hchar, one_smul]

end Nebentypus

/-! ### The nebentypus character of a level restriction -/

section Restriction

/-- **The nebentypus of a level restriction.** For `M ∣ N`, reading a form of level `M` as a form
of level `N` carries `M_k(Γ₁(M), χ)` into `M_k(Γ₁(N), χ ∘ (ZMod N)ˣ → (ZMod M)ˣ)`: the character
is pulled back along the reduction map.

This is the degeneracy map `V₁` at the pair `M ∣ N`, the one operator the old subspace excludes
at `M = N`; unlike `TauCeti.ModularForm.levelRaise_mem_modFormCharSpace`, which raises the level
to exactly `d * M`, the target level here is an arbitrary multiple of `M`.

Follows `restrictSubgroup_mem_modFormCharSpace` of the AINTLIB `LeanModularForms` project
(`Eigenforms/MainLemma.lean`, <https://github.com/CBirkbeck/AINTLIB>, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0). -/
theorem ModularForm.ofLe_mem_modFormCharSpace {M N : ℕ} (χ : (ZMod M)ˣ →* ℂˣ) (h : M ∣ N)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    _root_.ModularForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd h) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  have hdvd : 1 * M ∣ N := by rwa [one_mul]
  have := levelRaise_mem_modFormCharSpace_of_dvd hdvd χ hf
  rwa [_root_.ModularForm.levelRaise_one] at this

/-- **The nebentypus of a level restriction (cusp forms).** For `M ∣ N`, reading a cusp form of
level `M` as a cusp form of level `N` carries `S_k(Γ₁(M), χ)` into
`S_k(Γ₁(N), χ ∘ (ZMod N)ˣ → (ZMod M)ˣ)`. Together with `TauCeti.ofLe_mem_cuspFormsOld` this
places the restriction of a `χ`-form of proper divisor level inside the old subspace, with a
known character. -/
theorem CuspForm.ofLe_mem_cuspFormCharSpace {M N : ℕ} (χ : (ZMod M)ˣ →* ℂˣ) (h : M ∣ N)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    _root_.CuspForm.ofLe (Gamma1_map_le_Gamma1_map_of_dvd h) f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  have hdvd : 1 * M ∣ N := by rwa [one_mul]
  have := levelRaise_mem_cuspFormCharSpace_of_dvd hdvd χ hf
  rwa [_root_.CuspForm.levelRaise_one] at this

end Restriction

/-! ### The `q`-expansion of a level-raise -/

section QExpansion

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}

/-- Scaling the argument by `d` raises the local parameter at the cusp `∞` to the `d`-th
power: `q(d τ) = q(τ) ^ d`. -/
lemma qParam_one_scaleGL_smul [NeZero d] (τ : ℍ) :
    Function.Periodic.qParam 1 ((scaleGL d • τ : ℍ) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ d := by
  simp only [Function.Periodic.qParam, coe_scaleGL_smul]
  rw [← Complex.exp_nat_mul]
  ring_nf

/-- **The `q`-expansion of a level-raise.** Level-raising substitutes `q ↦ q ^ d` in the
`q`-expansion, which on power series is `PowerSeries.expand d`. -/
theorem ModularForm.qExpansion_levelRaise [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) :
    qExpansion 1 (ModularForm.levelRaise d hle f) =
      (qExpansion 1 f).expand d (NeZero.ne d) := by
  have hd : d ≠ 0 := NeZero.ne d
  have : Fact (IsCusp OnePoint.infty 𝒢) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h𝒢⟩
  have key : ∀ τ : ℍ, HasSum (fun m ↦ ((qExpansion 1 f).expand d hd).coeff m •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.levelRaise d hle f τ) := by
    intro τ
    have h1 := ModularForm.hasSum_qExpansion f (h := 1) one_pos h𝒢 (scaleGL d • τ)
    rw [ModularForm.levelRaise_apply]
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hd) ?_).mp ?_
    · intro m hm
      have : ¬ d ∣ m := fun ⟨j, hj⟩ ↦ hm ⟨j, hj.symm⟩
      simp [PowerSeries.coeff_expand_of_not_dvd _ hd _ this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, PowerSeries.coeff_expand_mul, smul_eq_mul, pow_mul,
        ← qParam_one_scaleGL_smul]
  exact PowerSeries.ext fun n ↦ (ModularFormClass.qExpansion_coeff_unique one_pos h𝒢' key n).symm

/-- **The `q`-expansion of a level-raise, on coefficients.** `aₙ(V_d f) = a_{n/d}(f)` when
`d ∣ n`, and `0` otherwise. -/
theorem ModularForm.qExpansion_levelRaise_coeff [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) (n : ℕ) :
    (qExpansion 1 (ModularForm.levelRaise d hle f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [ModularForm.qExpansion_levelRaise h𝒢 h𝒢' hle f, PowerSeries.coeff_expand]

/-- **The `q`-expansion of a level-raise, at `Γ₁`.** For `f` of level `Γ₁(M)`, its image `V_d f`
has level `Γ₁(dM)` and `q`-expansion coefficients `aₙ(V_d f) = a_{n/d}(f)` when `d ∣ n`, and `0`
otherwise. -/
theorem ModularForm.qExpansion_levelRaise_coeff_Gamma1 (M : ℕ) [NeZero M] [NeZero d]
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  refine ModularForm.qExpansion_levelRaise_coeff ?_ ?_ _ f n <;>
    exact one_mem_strictPeriods_Gamma1_map _

/-- **The `q`-expansion of a level-raised cusp form.** A cusp form and its image under the
inclusion into modular forms have the same underlying function, so the substitution `q ↦ q ^ d`
of `ModularForm.qExpansion_levelRaise` reads the same way on cusp forms. -/
theorem CuspForm.qExpansion_levelRaise [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) :
    qExpansion 1 (CuspForm.levelRaise d hle f) = (qExpansion 1 f).expand d (NeZero.ne d) := by
  have hcoe : ⇑(CuspForm.levelRaise d hle f) =
      ⇑(ModularForm.levelRaise d hle (f : ModularForm 𝒢 k)) := by
    rw [CuspForm.coe_levelRaise, ModularForm.coe_levelRaise]
    rfl
  rw [hcoe]
  exact ModularForm.qExpansion_levelRaise h𝒢 h𝒢' hle _

/-- **The `q`-expansion of a level-raised cusp form, on coefficients.**
`aₙ(V_d f) = a_{n/d}(f)` when `d ∣ n`, and `0` otherwise. -/
theorem CuspForm.qExpansion_levelRaise_coeff [𝒢'.HasDetOne] [NeZero d]
    (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods) (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : CuspForm 𝒢 k) (n : ℕ) :
    (qExpansion 1 (CuspForm.levelRaise d hle f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [CuspForm.qExpansion_levelRaise h𝒢 h𝒢' hle f, PowerSeries.coeff_expand]

/-- **The `q`-expansion of a level-raised cusp form, at `Γ₁`.** For `f` of level `Γ₁(M)`, its
image `V_d f` has level `Γ₁(dM)` and `q`-expansion coefficients `aₙ(V_d f) = a_{n/d}(f)` when
`d ∣ n`, and `0` otherwise. These are the coefficients of the spanning forms of the old
subspace. -/
theorem CuspForm.qExpansion_levelRaise_coeff_Gamma1 (M : ℕ) [NeZero M] [NeZero d]
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  refine CuspForm.qExpansion_levelRaise_coeff ?_ ?_ _ f n <;>
    exact one_mem_strictPeriods_Gamma1_map _

end QExpansion

end TauCeti

end
