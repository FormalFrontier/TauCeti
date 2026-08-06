/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal

/-!
# The level-raising degeneracy maps `V_d`

For a positive integer `d`, the *level-raising* (or *degeneracy*) map `V_d` sends a function on
the upper half-plane to `τ ↦ f (d τ)`. It is the slash action by `diag(d, 1)`, renormalized by
`d ^ (1 - k)` so that no power of `d` is introduced.

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
  the algebraic properties (`levelRaise_one_apply`, `levelRaise_levelRaise`,
  `levelRaise_injective`) all follow by `ext`.
* `TauCeti.Gamma1_map_le_conjAct_scaleGL`, `TauCeti.Gamma0_map_le_conjAct_scaleGL`: the level
  transport, `Γ₁(dM) ≤ diag(d,1)⁻¹ Γ₁(M) diag(d,1)` and likewise for `Γ₀`, which is what makes
  `V_d` a map `M_k(Γ₁(M)) → M_k(Γ₁(dM))`.
* `TauCeti.ModularForm.slash_levelRaise_eq_smul`: the character transport. Slashing `V_d f` by
  `γ` produces the same scalar that slashing `f` by the conjugate matrix `conjScale d γ` does;
  for `γ ∈ Γ₀(dM)` the conjugate lies in `Γ₀(M)` with the same lower-right entry, so the
  nebentypus of `V_d f` is that of `f` read along `(ZMod (dM))ˣ → (ZMod M)ˣ`.
* `TauCeti.ModularForm.qExpansion_levelRaise_coeff`: the `q`-expansion of `V_d f` is that of `f`
  with `q` replaced by `q ^ d`; on coefficients, `aₙ(V_d f) = a_{n/d}(f)` for `d ∣ n` and `0`
  otherwise.

The old subspace of Layer 3 of the ModularForms roadmap is spanned by the images of the `V_d`,
and the conductor statement of Layer 4 is phrased with this normalization of `V_d`.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.6
* Miyake, *Modular forms*, §4.6
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {k : ℤ} {d : ℕ}

/-! ### The scaling matrix `diag(d, 1)` -/

/-- The diagonal element `!![d, 0; 0, 1]` of `GL(2, ℝ)`, for `d` a nonzero natural number.
Slashing by it is, up to the normalizing scalar `d ^ (1 - k)`, the level-raising operator
`V_d`. -/
@[expose]
def scaleGL (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  diagGL ![Units.mk0 (d : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne d)), 1]

@[simp]
lemma coe_scaleGL [NeZero d] :
    ((scaleGL d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] := by
  rw [scaleGL, diagGL_coe, Matrix.diagonal_fin_two]
  simp

@[simp]
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
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos val_det_scaleGL_pos]
  simp [mul_comm]

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

lemma levelRaise_injective [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaise (k := k) d h) := by
  intro f g hfg
  refine _root_.ModularForm.ext fun τ ↦ ?_
  have := congr($hfg ((scaleGL d)⁻¹ • τ))
  simpa [smul_smul] using this

/-- `V₁` is the restriction map: it changes nothing but the invariance group. -/
lemma levelRaise_one_apply [𝒢'.HasDetOne] (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL 1)⁻¹ • 𝒢)
    (f : ModularForm 𝒢 k) (τ : ℍ) : levelRaise 1 h f τ = f τ := by
  simp

/-- The level-raising operators compose: `V_d ∘ V_e = V_{de}`. -/
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

lemma levelRaise_injective [𝒢'.HasDetOne] [NeZero d]
    (h : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) :
    Injective (levelRaise (k := k) d h) := by
  intro f g hfg
  refine _root_.CuspForm.ext fun τ ↦ ?_
  have := congr($hfg ((scaleGL d)⁻¹ • τ))
  simpa [smul_smul] using this

/-- The level-raising operators compose: `V_d ∘ V_e = V_{de}`. -/
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
@[expose]
def conjScale (d : ℕ) (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = d * c) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], by
    have hdet : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
      have := γ.2; rwa [Matrix.det_fin_two] at this
    rw [hc] at hdet
    rw [Matrix.det_fin_two_of]
    linarith [hdet]⟩

@[simp]
lemma coe_conjScale (d : ℕ) (γ : SL(2, ℤ)) (c : ℤ) (hc : γ 1 0 = d * c) :
    ((conjScale d γ c hc : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1] := rfl

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

/-! ### Slashing a level-raise, and the transport of the nebentypus -/

section Slash

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}

/-- Slashing a level-raise by an integral matrix `γ` whose lower-left entry is divisible by `d`
is the level-raise of the slash of `f` by the conjugate matrix `conjScale d γ`. -/
lemma ModularForm.coe_levelRaise_slash [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ =
      (d : ℂ) ^ (1 - k) • ((⇑f ∣[k] mapGL ℝ (conjScale d γ c hc)) ∣[k] scaleGL d) := by
  rw [coe_levelRaise, _root_.ModularForm.smul_slash, σ_mapGL_real_eq_refl,
    ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul, ← SlashAction.slash_mul,
    mul_inv_eq_iff_eq_mul.mp (mapGL_conjScale γ c hc)]

/-- **Nebentypus transport.** If `f` is an eigenvector of the slash by `conjScale d γ` with
eigenvalue `z`, then `V_d f` is an eigenvector of the slash by `γ` with the same eigenvalue.
Applied to `γ ∈ Γ₀(dM)` — whose conjugate lies in `Γ₀(M)` with the same lower-right entry, by
`Gamma0_map_le_conjAct_scaleGL` and `coe_conjScale` — this carries the nebentypus of `f` at
level `M` to `V_d f` at level `dM`, the character read along `(ZMod (dM))ˣ → (ZMod M)ˣ`. -/
lemma ModularForm.slash_levelRaise_eq_smul [𝒢'.HasDetOne] [NeZero d]
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k)
    (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = d * c) {z : ℂ}
    (hf : ⇑f ∣[k] mapGL ℝ (conjScale d γ c hc) = z • ⇑f) :
    ⇑(levelRaise d hle f) ∣[k] mapGL ℝ γ = z • ⇑(levelRaise d hle f) := by
  rw [coe_levelRaise_slash hle f γ hc, hf, _root_.ModularForm.smul_slash, coe_levelRaise,
    smul_comm]
  congr 1
  have hdpos : (0 : ℝ) < d := mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  simp [UpperHalfPlane.σ, hdpos]

end Slash

/-! ### The `q`-expansion of a level-raise -/

section QExpansion

local notation "𝕢" => Function.Periodic.qParam

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)}

/-- Scaling the argument by `d` raises the local parameter at the cusp `∞` to the `d`-th
power: `q(d τ) = q(τ) ^ d`. -/
lemma qParam_one_scaleGL_smul [NeZero d] (τ : ℍ) :
    𝕢 1 ((scaleGL d • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ d := by
  simp only [Function.Periodic.qParam, coe_scaleGL_smul]
  rw [← Complex.exp_nat_mul]
  ring_nf

/-- **The `q`-expansion of a level-raise.** Substituting `q ↦ q ^ d` in the `q`-expansion:
`aₙ(V_d f) = a_{n/d}(f)` when `d ∣ n`, and `0` otherwise. -/
theorem ModularForm.qExpansion_levelRaise_coeff [𝒢.HasDetOne] [𝒢'.HasDetOne] [NeZero d]
    [𝒢.IsArithmetic] [𝒢'.IsArithmetic] (h𝒢 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (h𝒢' : (1 : ℝ) ∈ 𝒢'.strictPeriods)
    (hle : 𝒢' ≤ ConjAct.toConjAct (scaleGL d)⁻¹ • 𝒢) (f : ModularForm 𝒢 k) (n : ℕ) :
    (qExpansion 1 (ModularForm.levelRaise d hle f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have hd : d ≠ 0 := NeZero.ne d
  set c : ℕ → ℂ := fun n ↦ if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 with hc
  have key : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 (τ : ℂ) ^ m)
      (ModularForm.levelRaise d hle f τ) := by
    intro τ
    have h1 := ModularForm.hasSum_qExpansion f (h := 1) one_pos h𝒢 (scaleGL d • τ)
    rw [ModularForm.levelRaise_apply]
    refine (Function.Injective.hasSum_iff (mul_right_injective₀ hd) ?_).mp ?_
    · intro m hm
      have : ¬ d ∣ m := fun ⟨j, hj⟩ ↦ hm ⟨j, hj.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, if_pos (Dvd.intro m rfl),
        Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hd), smul_eq_mul, pow_mul,
        ← qParam_one_scaleGL_smul]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos h𝒢' key n).symm

/-- **The `q`-expansion of a level-raise, at `Γ₁`.** -/
theorem ModularForm.qExpansion_levelRaise_coeff_Gamma1 (M : ℕ) [NeZero M] [NeZero d]
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (ModularForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL M d) f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  refine ModularForm.qExpansion_levelRaise_coeff ?_ ?_ _ f n <;>
    simp [CongruenceSubgroup.strictPeriods_Gamma1]

end QExpansion

end TauCeti

end
