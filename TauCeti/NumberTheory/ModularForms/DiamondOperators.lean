/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups
public import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# Diamond operators and modular forms with character

The diamond operators `⟨d⟩` on modular and cusp forms for `Γ₁(N)`, and the nebentypus
character spaces `M_k(Γ₁(N), χ)` and `S_k(Γ₁(N), χ)` they cut out.

Since `Γ₁(N)` is normal in `Γ₀(N)` with quotient `(ZMod N)ˣ` (via the lower-right entry, the
map `CongruenceSubgroup.Gamma0Map`), slashing by any lift of `d ∈ (ZMod N)ˣ` is a well-defined
linear endomorphism of `M_k(Γ₁(N))` and of `S_k(Γ₁(N))`: the diamond operator `⟨d⟩`, packaged
as monoid homomorphisms `diamondOpHom` and `diamondOpCuspHom` into the endomorphism algebras.
The character space `modFormCharSpace k χ` (resp. `cuspFormCharSpace k χ`) is the simultaneous
`χ`-eigenspace of the diamond operators, a `Submodule` of Mathlib's `ModularForm` — not a new
bundled type — and membership in it is equivalent to the classical nebentypus transformation
law `f ∣[k] γ = χ(d_γ) • f` for `γ ∈ Γ₀(N)` (`mem_modFormCharSpace_iff_nebentypus`).

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`, Chris Birkbeck), realizing Layer 0 of the
ModularForms roadmap; the roadmap pins these definitions (eigenspace-in-a-`Submodule`, not a
re-founded slash action with built-in character) and their names. The Hecke pair
`(Γ₁(N), Δ₁(N))` from the same source file is Layer-2 material and is not ported here.

## Main definitions

* `(CongruenceSubgroup.Gamma0Map N).toHomUnits` (Mathlib): the lower-right entry as a
  `Γ₀(N) →* (ZMod N)ˣ`.
* `diamondOp`/`diamondOpCusp`: the diamond operator `⟨d⟩` for `d : (ZMod N)ˣ`, a linear
  endomorphism of `ModularForm ((Gamma1 N).map (mapGL ℝ)) k` resp. `CuspForm _ k`, evaluated
  by `coe_diamondOp`/`coe_diamondOpCusp` as slashing by any representative.
* `diamondOpHom`/`diamondOpCuspHom`: the diamond operators as monoid homomorphisms into the
  endomorphism algebras.
* `diamondOpNat`/`diamondOpCuspNat`: the same operator indexed by a natural number, `⟨n⟩` of
  Diamond–Shurman §5.3, extended by zero when `n` is not coprime to `N`.
* `modFormCharSpace`/`cuspFormCharSpace`: the nebentypus character spaces `M_k(Γ₁(N), χ)` and
  `S_k(Γ₁(N), χ)`, cut out as simultaneous diamond eigenspaces.

## Main results

* `mem_modFormCharSpace_iff_nebentypus`/`mem_cuspFormCharSpace_iff_nebentypus`: membership in the
  character space is the classical nebentypus relation `f ∣[k] g = χ(d_g) • f` for all
  `g ∈ Γ₀(N)`.
* `slash_mapGL_eq_diamondOpNat`/`slash_mapGL_eq_diamondOpCuspNat`: rational slashing by a
  suitable `Γ₀(N)` representative is the corresponding natural-indexed diamond operator;
  `slash_mapGL_gamma0Twist_eq_diamondOpNat` and its cusp counterpart specialize to the explicit
  Bézout representative.

## References

* Miyake, *Modular forms*, §4.5
* Diamond–Shurman, *A first course in modular forms*, §5.1 and §5.3
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ}

open CongruenceSubgroup

/-- Pointwise formula for the translated-and-transported modular form underlying
`diamondOpAux`. -/
private lemma mcast_translate_apply (k : ℤ) (g : ↥(Gamma0 N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (z : ℍ) :
    (ModularForm.mcast rfl (ModularForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
      (Gamma1_map_inv_conjAct_eq g).symm) z = (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) z :=
  (ModularForm.mcast_apply rfl (ModularForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
    (Gamma1_map_inv_conjAct_eq g).symm z).trans (congr_fun (ModularForm.coe_translate f _) z)

/-- Pointwise formula for the translated-and-transported cusp form underlying
`diamondOpCuspAux`. -/
private lemma cusp_mcast_translate_apply (k : ℤ) (g : ↥(Gamma0 N))
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : ℍ) :
    (CuspForm.mcast rfl (CuspForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
      (Gamma1_map_inv_conjAct_eq g).symm) z = (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) z :=
  (CuspForm.mcast_apply rfl (CuspForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
    (Gamma1_map_inv_conjAct_eq g).symm z).trans (congr_fun (CuspForm.coe_translate_gl f _) z)

-- The diamond operator at a chosen representative: for `g ∈ Gamma0 N`, translation by
-- `mapGL ℝ g` lands at the conjugated level, which `Gamma1_map_inv_conjAct_eq` identifies
-- with the original one.
private noncomputable def diamondOpAux (k : ℤ) (g : ↥(Gamma0 N)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    ModularForm.mcast rfl (ModularForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
      (Gamma1_map_inv_conjAct_eq g).symm
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    refine ModularForm.ext fun z ↦ ((mcast_translate_apply k g (c • f) z).trans ?_).trans
      (congrArg (fun w : ℂ ↦ c • w) (mcast_translate_apply k g f z)).symm
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp

/-- Slash-transport for `Γ₁(N)`-invariant functions: if `f` is invariant under
`(Gamma1 N).map (mapGL ℝ)` and `Gamma0Map N g₁ = Gamma0Map N g₂`, then
`f ∣[k] g₁ = f ∣[k] g₂`. -/
lemma slash_eq_of_Gamma0Map_eq {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N).map (mapGL ℝ), f ∣[k] γ = f)
    (g₁ g₂ : ↥(Gamma0 N)) (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    f ∣[k] mapGL ℝ (g₁ : SL(2, ℤ)) = f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ)) := by
  -- the ascription pins the factor-through-g₂ regrouping; no rewriting lemma produces it
  rw [show (g₁ : SL(2, ℤ)) = ((g₁ : SL(2, ℤ)) * (g₂ : SL(2, ℤ))⁻¹) * (g₂ : SL(2, ℤ)) by group,
    map_mul, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map.mpr ⟨_, mul_inv_mem_Gamma1_of_Gamma0Map_eq g₁ g₂ heq, rfl⟩)]

-- The diamond operator depends only on the `Gamma0Map` value.
private theorem diamondOpAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) : diamondOpAux k g₁ = diamondOpAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- The diamond operator `⟨d⟩` on modular forms for `Gamma1 N`, indexed by
`d : (ZMod N)ˣ`. -/
noncomputable def diamondOp (k : ℤ) (d : (ZMod N)ˣ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpAux k (Gamma0Map_toHomUnits_surjective d).choose

-- `diamondOp` equals `diamondOpAux` on any representative with the right image.
private theorem diamondOp_eq_diamondOpAux (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) : diamondOp k d = diamondOpAux k g :=
  diamondOpAux_eq_of_Gamma0Map_eq k _ g
    (congrArg Units.val ((Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm))

/-- Evaluation of the diamond operator: at any representative `g ∈ Γ₀(N)` with lower-right
entry `d`, the diamond operator `⟨d⟩` is slashing by `g`. -/
theorem coe_diamondOp (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOp k d f) = ⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  rw [diamondOp_eq_diamondOpAux k d g hg]
  exact funext (mcast_translate_apply k g f)

/-- The diamond operator at `1` is the identity. -/
@[simp]
theorem diamondOp_one (k : ℤ) : diamondOp (N := N) k 1 = LinearMap.id := by
  rw [diamondOp_eq_diamondOpAux k 1 1 (map_one _)]
  ext f z
  -- state the unfolded slash of the coercion so `slash_one` applies
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

/-- Diamond operators compose: `⟨d₁ * d₂⟩ = ⟨d₁⟩ ∘ ⟨d₂⟩`. -/
theorem diamondOp_mul (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp k (d₁ * d₂) = (diamondOp k d₁).comp (diamondOp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₂
  rw [diamondOp_eq_diamondOpAux k (d₁ * d₂) (g₂ * g₁) (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOp_eq_diamondOpAux k d₁ g₁ hg₁, diamondOp_eq_diamondOpAux k d₂ g₂ hg₂]
  ext f z
  -- state the unfolded slash of the coercion so `slash_mul` applies
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The diamond operator as a monoid homomorphism `(ZMod N)ˣ →* Module.End ℂ (...)`. -/
noncomputable def diamondOpHom (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOp k
  map_one' := diamondOp_one k
  map_mul' := diamondOp_mul k

@[simp]
lemma diamondOpHom_apply (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpHom k d = diamondOp k d := (rfl)

-- Auxiliary form of the cusp-form diamond operator: translation by a fixed
-- `Γ₀(N)`-representative, before descending to the `Γ₀(N)/Γ₁(N)`-quotient.
private noncomputable def diamondOpCuspAux (k : ℤ) (g : ↥(Gamma0 N)) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    CuspForm.mcast rfl (CuspForm.translate f (mapGL ℝ (g : SL(2, ℤ))))
      (Gamma1_map_inv_conjAct_eq g).symm
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash k (mapGL ℝ (g : SL(2, ℤ))) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    refine CuspForm.ext fun z ↦ ((cusp_mcast_translate_apply k g (c • f) z).trans ?_).trans
      (congrArg (fun w : ℂ ↦ c • w) (cusp_mcast_translate_apply k g f z)).symm
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp

-- Well-definedness for the cusp-form diamond operator.
private theorem diamondOpCuspAux_eq_of_Gamma0Map_eq (k : ℤ) (g₁ g₂ : ↥(Gamma0 N))
    (heq : Gamma0Map N g₁ = Gamma0Map N g₂) :
    diamondOpCuspAux k g₁ = diamondOpCuspAux k g₂ := by
  ext f z
  exact congr_fun (slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ) g₁ g₂ heq) z

/-- The cusp-form diamond operator indexed by `d : (ZMod N)ˣ`. -/
noncomputable def diamondOpCusp (k : ℤ) (d : (ZMod N)ˣ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCuspAux k (Gamma0Map_toHomUnits_surjective d).choose

-- `diamondOpCusp` equals `diamondOpCuspAux` on any representative.
private theorem diamondOpCusp_eq_diamondOpCuspAux (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) :
    diamondOpCusp k d = diamondOpCuspAux k g :=
  diamondOpCuspAux_eq_of_Gamma0Map_eq k _ g
    (congrArg Units.val ((Gamma0Map_toHomUnits_surjective d).choose_spec.trans hg.symm))

/-- Evaluation of the cusp-form diamond operator: at any representative `g ∈ Γ₀(N)` with
lower-right entry `d`, the diamond operator `⟨d⟩` is slashing by `g`. -/
theorem coe_diamondOpCusp (k : ℤ) (d : (ZMod N)ˣ) (g : ↥(Gamma0 N))
    (hg : (Gamma0Map N).toHomUnits g = d) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOpCusp k d f) = ⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ)) := by
  rw [diamondOpCusp_eq_diamondOpCuspAux k d g hg]
  exact funext (cusp_mcast_translate_apply k g f)

/-- The cusp diamond operator at `1` is the identity. -/
@[simp]
theorem diamondOpCusp_one (k : ℤ) : diamondOpCusp (N := N) k 1 = LinearMap.id := by
  rw [diamondOpCusp_eq_diamondOpCuspAux k 1 1 (map_one _)]
  ext f z
  -- state the unfolded slash of the coercion so `slash_one` applies
  change (⇑f ∣[k] mapGL ℝ (1 : SL(2, ℤ))) z = f z
  simp only [map_one, SlashAction.slash_one]

/-- Cusp diamond operators compose multiplicatively. -/
theorem diamondOpCusp_mul (k : ℤ) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOpCusp k (d₁ * d₂) = (diamondOpCusp k d₁).comp (diamondOpCusp k d₂) := by
  obtain ⟨g₁, hg₁⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₁
  obtain ⟨g₂, hg₂⟩ := Gamma0Map_toHomUnits_surjective (N := N) d₂
  rw [diamondOpCusp_eq_diamondOpCuspAux k (d₁ * d₂) (g₂ * g₁)
      (by simp [map_mul, hg₁, hg₂, mul_comm]),
    diamondOpCusp_eq_diamondOpCuspAux k d₁ g₁ hg₁, diamondOpCusp_eq_diamondOpCuspAux k d₂ g₂ hg₂]
  ext f z
  -- state the unfolded slash of the coercion so `slash_mul` applies
  change (⇑f ∣[k] mapGL ℝ ((g₂ : SL(2, ℤ)) * (g₁ : SL(2, ℤ)))) z =
    ((⇑f ∣[k] mapGL ℝ (g₂ : SL(2, ℤ))) ∣[k] mapGL ℝ (g₁ : SL(2, ℤ))) z
  rw [map_mul, SlashAction.slash_mul]

/-- The cusp-form diamond operator as a monoid homomorphism. -/
noncomputable def diamondOpCuspHom (k : ℤ) :
    (ZMod N)ˣ →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := diamondOpCusp k
  map_one' := diamondOpCusp_one k
  map_mul' := diamondOpCusp_mul k

@[simp]
lemma diamondOpCuspHom_apply (k : ℤ) (d : (ZMod N)ˣ) :
    diamondOpCuspHom k d = diamondOpCusp k d := (rfl)

/-- The nebentypus character space `S_k(Γ₁(N), χ)`: cusp forms on which every
diamond operator `⟨d⟩` acts by the scalar `χ(d)`. -/
noncomputable def cuspFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpCuspHom k d) (↑(χ d))

/-- Defining equation for the sealed `cuspFormCharSpace`: it is the joint eigenspace of the
diamond operators. -/
lemma cuspFormCharSpace_def (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ =
      ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpCuspHom k d) (↑(χ d)) := (rfl)

/-- Membership in `S_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff
`⟨d⟩ f = χ(d) • f` for every `d ∈ (ZMod N)ˣ`. -/
@[simp]
theorem mem_cuspFormCharSpace_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpCuspHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [cuspFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Diamond operators act by `χ(d)` on elements of `S_k(Γ₁(N), χ)`. Not `@[simp]`: `χ`
occurs only in the hypothesis and the right-hand side, so `simp` cannot infer it. -/
theorem diamondOpCusp_apply_of_mem_cuspFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (d : (ZMod N)ˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    diamondOpCusp k d f = (↑(χ d) : ℂ) • f :=
  (mem_cuspFormCharSpace_iff k χ f).mp hf d

/-- The modular-form nebentypus character space `M_k(Γ₁(N), χ)`. -/
noncomputable def modFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpHom k d) (↑(χ d))

/-- Defining equation for the sealed `modFormCharSpace`: it is the joint eigenspace of the
diamond operators. -/
lemma modFormCharSpace_def (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    modFormCharSpace k χ =
      ⨅ d : (ZMod N)ˣ, Module.End.eigenspace (diamondOpHom k d) (↑(χ d)) := (rfl)

/-- Membership in `M_k(Γ₁(N), χ)`: `f` is in the `χ`-eigenspace iff `⟨d⟩ f = χ(d) • f`
for every `d ∈ (ZMod N)ˣ`. -/
@[simp]
theorem mem_modFormCharSpace_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpHom k d f = (↑(χ d) : ℂ) • f := by
  simp only [modFormCharSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- Diamond operators act by `χ(d)` on elements of `M_k(Γ₁(N), χ)`. Not `@[simp]`: `χ`
occurs only in the hypothesis and the right-hand side, so `simp` cannot infer it. -/
theorem diamondOp_apply_of_mem_modFormCharSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (d : (ZMod N)ˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    diamondOp k d f = (↑(χ d) : ℂ) • f :=
  (mem_modFormCharSpace_iff k χ f).mp hf d

/-- **Bridge**: for a `Gamma1`-invariant modular form `f`, membership in the
diamond-eigenspace `modFormCharSpace k χ₀` is equivalent to the classical nebentypus
relation `f ∣[k] g = χ₀(d_g) • f` for all `g ∈ Γ₀(N)`. -/
theorem mem_modFormCharSpace_iff_nebentypus (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ modFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N),
      (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ ((Gamma0Map N).toHomUnits g)) : ℂ) • ⇑f := by
  rw [mem_modFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h ((Gamma0Map N).toHomUnits g)
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k _ g rfl] at hd
    exact congr_arg (⇑· : ModularForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
    rw [diamondOpHom_apply, diamondOp_eq_diamondOpAux k d g hg, ← hg]
    exact ModularForm.ext (congr_fun (h g))

/-- **Bridge (cusp forms)**: for a `Gamma1`-invariant cusp form `f`, membership in the
diamond-eigenspace `cuspFormCharSpace k χ₀` is equivalent to the classical nebentypus
relation `f ∣[k] g = χ₀(d_g) • f` for all `g ∈ Γ₀(N)`. -/
theorem mem_cuspFormCharSpace_iff_nebentypus (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : f ∈ cuspFormCharSpace k χ₀ ↔
    ∀ g : ↥(Gamma0 N),
      (⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) = (↑(χ₀ ((Gamma0Map N).toHomUnits g)) : ℂ) • ⇑f := by
  rw [mem_cuspFormCharSpace_iff]
  refine ⟨fun h g ↦ ?_, fun h d ↦ ?_⟩
  · have hd := h ((Gamma0Map N).toHomUnits g)
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq_diamondOpCuspAux k _ g rfl] at hd
    exact congr_arg (⇑· : CuspForm _ k → _) hd
  · obtain ⟨g, hg⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
    rw [diamondOpCuspHom_apply, diamondOpCusp_eq_diamondOpCuspAux k d g hg, ← hg]
    exact CuspForm.ext (congr_fun (h g))

/-- The diamond operator indexed by a natural number: `⟨n⟩` is `diamondOp` at the unit `n mod N`
when `n` is coprime to `N`, and `0` otherwise.

This is `⟨n⟩` as Diamond–Shurman §5.3 writes it. Extending the index from `(ZMod N)ˣ` to `ℕ` by
zero is what lets the Hecke recurrence at a prime power be stated uniformly: the `⟨p⟩` term
simply vanishes when `p ∣ N`, instead of the recurrence needing a separate case.

Follows `diamondOp_n` of the AINTLIB `LeanModularForms` project
(`HeckeRIngs/GL2/HeckeT_n.lean`, <https://github.com/CBirkbeck/AINTLIB>, commit
`ce76186b5f61c846d770d2f87eb76ba5b9c9117a`, Apache-2.0). -/
-- The statement is that project's; the proofs below are re-derived against the current Mathlib
-- pin, where `dif_pos`/`dif_neg` are deprecated and the coprime lemma cannot carry `@[simp]`.
noncomputable def diamondOpNat (k : ℤ) (n : ℕ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  if h : Nat.Coprime n N then diamondOp k (ZMod.unitOfCoprime n h) else 0

/-- When `n` is coprime to `N`, `⟨n⟩` is the diamond operator at the unit `n mod N`. -/
-- Not a `simp` lemma: the right-hand side mentions the coprimality proof `h`, which `simp`
-- cannot recover from the left-hand side, so it could never apply. Its negative counterpart is
-- `simp`-able because that right-hand side is just `0`.
lemma diamondOpNat_of_coprime (k : ℤ) {n : ℕ} (h : Nat.Coprime n N) :
    diamondOpNat k n = diamondOp k (ZMod.unitOfCoprime n h) :=
  dite_eq_left_of_eq_true (by simpa using h)

/-- When `n` is not coprime to `N`, `⟨n⟩` vanishes. This is the case that lets the prime-power
Hecke recurrence be stated without splitting on whether `p` divides the level. -/
@[simp]
lemma diamondOpNat_of_not_coprime (k : ℤ) {n : ℕ} (h : ¬ Nat.Coprime n N) :
    diamondOpNat (N := N) k n = 0 :=
  dite_eq_right_of_eq_false (by simpa using h)

/-- The cusp-form diamond operator indexed by a natural number: `⟨n⟩` is `diamondOpCusp` at the
unit `n mod N` when `n` is coprime to `N`, and `0` otherwise — the cusp-form counterpart of
`diamondOpNat`, and the reason the prime Hecke operator on `S_k(Γ₁(N))` has one formula at every
prime rather than one per divisibility case. -/
noncomputable def diamondOpCuspNat (k : ℤ) (n : ℕ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  if h : Nat.Coprime n N then diamondOpCusp k (ZMod.unitOfCoprime n h) else 0

/-- When `n` is coprime to `N`, `⟨n⟩` is the cusp diamond operator at the unit `n mod N`. -/
-- Not a `simp` lemma, for the reason given at `diamondOpNat_of_coprime`.
lemma diamondOpCuspNat_of_coprime (k : ℤ) {n : ℕ} (h : Nat.Coprime n N) :
    diamondOpCuspNat k n = diamondOpCusp k (ZMod.unitOfCoprime n h) :=
  dite_eq_left_of_eq_true (by simpa using h)

/-- When `n` is not coprime to `N`, `⟨n⟩` vanishes on cusp forms. -/
@[simp]
lemma diamondOpCuspNat_of_not_coprime (k : ℤ) {n : ℕ} (h : ¬ Nat.Coprime n N) :
    diamondOpCuspNat (N := N) k n = 0 :=
  dite_eq_right_of_eq_false (by simpa using h)

/-- Slashing by a `Γ₀(N)` representative with lower-right unit `n` is the zero-extended
diamond operator `⟨n⟩` on modular forms. -/
theorem slash_mapGL_eq_diamondOpNat {n : ℕ} (k : ℤ) (h : Nat.Coprime n N)
    (g : ↥(Gamma0 N)) (hg : (Gamma0Map N).toHomUnits g = ZMod.unitOfCoprime n h)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) = ⇑(diamondOpNat k n f) := by
  rw [ModularForm.rat_slash_mapGL, diamondOpNat_of_coprime k h, coe_diamondOp k _ g hg f]

/-- The cusp-form counterpart of `slash_mapGL_eq_diamondOpNat`. -/
theorem slash_mapGL_eq_diamondOpCuspNat {n : ℕ} (k : ℤ) (h : Nat.Coprime n N)
    (g : ↥(Gamma0 N)) (hg : (Gamma0Map N).toHomUnits g = ZMod.unitOfCoprime n h)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (mapGL ℚ (g : SL(2, ℤ)) : GL (Fin 2) ℚ) = ⇑(diamondOpCuspNat k n f) := by
  rw [ModularForm.rat_slash_mapGL, diamondOpCuspNat_of_coprime k h,
    coe_diamondOpCusp k _ g hg f]

/-- **Slashing by the Bézout twist is the diamond operator `⟨p⟩`.** The twist is the `Γ₀(N)`
element of lower-right entry `p`, so this is `coe_diamondOp` at that representative, transported
across the `ℚ`/`ℝ` bridge. -/
theorem slash_mapGL_gamma0Twist_eq_diamondOpNat {p : ℕ} (k : ℤ) (h : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (mapGL ℚ (gamma0Twist N p h) : GL (Fin 2) ℚ) = ⇑(diamondOpNat k p f) :=
  slash_mapGL_eq_diamondOpNat k h ⟨gamma0Twist N p h, gamma0Twist_mem_Gamma0 h⟩
    (Gamma0Map_toHomUnits_gamma0Twist h) f

/-- **Slashing by the Bézout twist is the diamond operator `⟨p⟩`**, on cusp forms. -/
theorem slash_mapGL_gamma0Twist_eq_diamondOpCuspNat {p : ℕ} (k : ℤ) (h : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (mapGL ℚ (gamma0Twist N p h) : GL (Fin 2) ℚ) = ⇑(diamondOpCuspNat k p f) :=
  slash_mapGL_eq_diamondOpCuspNat k h ⟨gamma0Twist N p h, gamma0Twist_mem_Gamma0 h⟩
    (Gamma0Map_toHomUnits_gamma0Twist h) f
