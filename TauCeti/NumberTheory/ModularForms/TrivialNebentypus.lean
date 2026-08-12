/-
Copyright (c) 2026 TauCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# The two spellings of `M_k(Γ₀(N))`

There are two ways to say "modular form of level `N` with trivial nebentypus": as a modular
form for the bare congruence subgroup `Γ₀(N)`, and as an element of the character space
`M_k(Γ₁(N), χ)` of `TauCeti.NumberTheory.ModularForms.DiamondOperators` for the trivial
character `χ = 1`. The ModularForms roadmap flags the clash and pins its resolution: prove the
two isomorphic, then use `M_k(Γ₀(N))` as the default spelling and convert to it. This file is
that milestone, for modular forms (`TauCeti.modFormCharSpaceOneEquiv`) and for cusp forms
(`TauCeti.cuspFormCharSpaceOneEquiv`), both stated for `N ≠ 0`.

Both directions are instances of the generic subgroup-change API of
`TauCeti.NumberTheory.ModularForms.Basic`. Restricting a `Γ₀(N)`-form to `Γ₁(N)`
(`ModularForm.ofLe`) is unconditional, and the resulting form has trivial nebentypus because
the diamond operators are slashes by elements of `Γ₀(N)`. Conversely, a `Γ₁(N)`-form with
trivial nebentypus is `Γ₀(N)`-slash invariant by the nebentypus criterion
`mem_modFormCharSpace_iff_nebentypus`, and it is bounded (resp. zero) at every cusp of `Γ₀(N)`
because for `N ≠ 0` the groups `Γ₀(N)` and `Γ₁(N)` are arithmetic, hence share the cusps of
`SL(2, ℤ)` (`Subgroup.IsArithmetic.isCusp_of_isCusp`); this is `ModularForm.ofSlashInvariant`.
Both constructions preserve the underlying function `ℍ → ℂ`, so the resulting bijections are
`ℂ`-linear and conversion in either direction costs nothing: see the `coe_…_apply` lemmas
below.

The hypothesis `N ≠ 0` is therefore needed only for that converse direction: the
characterisations of trivial nebentypus and the results about restricting a `Γ₀(N)`-form hold
at every level, while the range equalities and the two equivalences assume `[NeZero N]`.

Note what the isomorphism is *not*: `M_k(Γ₁(N), 1)` is a `Submodule` of `M_k(Γ₁(N))`, so the
statement is that a submodule of the level-`Γ₁(N)` space is linearly equivalent to another
space of forms, not an equality of types.

## Main definitions

* `TauCeti.modFormCharSpaceOneEquiv`, `TauCeti.cuspFormCharSpaceOneEquiv`: for `N ≠ 0`, the
  `ℂ`-linear equivalences `M_k(Γ₁(N), 1) ≃ₗ M_k(Γ₀(N))` and `S_k(Γ₁(N), 1) ≃ₗ S_k(Γ₀(N))`.

## Main results

* `TauCeti.mem_modFormCharSpace_one_iff`, `TauCeti.mem_cuspFormCharSpace_one_iff`: trivial
  nebentypus means `Γ₀(N)`-slash invariance.
* `TauCeti.mem_modFormCharSpace_one_iff_diamondOp`,
  `TauCeti.mem_cuspFormCharSpace_one_iff_diamondOpCusp`: equivalently, being fixed by every
  diamond operator.
* `TauCeti.modFormCharSpace_one_eq_range`, `TauCeti.cuspFormCharSpace_one_eq_range`: for
  `N ≠ 0`, the trivial-nebentypus space is the image of the restriction map from level
  `Γ₀(N)`.

## References

* Diamond–Shurman, *A first course in modular forms*, §5.1
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {N : ℕ} {k : ℤ}

/-! ### Trivial nebentypus is `Γ₀(N)`-invariance -/

/-- A modular form for `Γ₁(N)` has trivial nebentypus exactly when it is `Γ₀(N)`-slash
invariant. -/
theorem mem_modFormCharSpace_one_iff (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  refine ⟨?_, fun h g ↦ ?_⟩
  · rintro h - ⟨g, hg, rfl⟩
    simpa using h ⟨g, hg⟩
  · simpa using h _ (Subgroup.mem_map_of_mem _ g.2)

/-- A cusp form for `Γ₁(N)` has trivial nebentypus exactly when it is `Γ₀(N)`-slash
invariant. -/
theorem mem_cuspFormCharSpace_one_iff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ⇑f ∣[k] γ = ⇑f := by
  rw [mem_cuspFormCharSpace_iff_nebentypus]
  refine ⟨?_, fun h g ↦ ?_⟩
  · rintro h - ⟨g, hg, rfl⟩
    simpa using h ⟨g, hg⟩
  · simpa using h _ (Subgroup.mem_map_of_mem _ g.2)

/-- Trivial nebentypus means being fixed by every diamond operator. -/
theorem mem_modFormCharSpace_one_iff_diamondOp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔ ∀ d : (ZMod N)ˣ, diamondOp k d f = f := by
  simp

/-- Trivial nebentypus means being fixed by every diamond operator. -/
theorem mem_cuspFormCharSpace_one_iff_diamondOpCusp (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) ↔
      ∀ d : (ZMod N)ˣ, diamondOpCusp k d f = f := by
  simp

/-! ### Restricting a `Γ₀(N)`-form to `Γ₁(N)` -/

/-- Restricted to `Γ₁(N)`, a modular form for `Γ₀(N)` has trivial nebentypus. -/
theorem ofLe_mem_modFormCharSpace_one (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f ∈
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) :=
  (mem_modFormCharSpace_one_iff _).mpr fun γ hγ ↦ by
    simpa using f.slash_action_eq' γ hγ

/-- Restricted to `Γ₁(N)`, a cusp form for `Γ₀(N)` has trivial nebentypus. -/
theorem ofLe_mem_cuspFormCharSpace_one (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f ∈ cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) :=
  (mem_cuspFormCharSpace_one_iff _).mpr fun γ hγ ↦ by
    simpa using f.slash_action_eq' γ hγ

/-- The diamond operators fix the restriction of a `Γ₀(N)`-form: they are slashes by elements
of `Γ₀(N)`, under which such a form is already invariant. -/
theorem diamondOp_ofLe (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ) :
    diamondOp k d (ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f) =
      ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (mem_modFormCharSpace_one_iff_diamondOp _).mp (ofLe_mem_modFormCharSpace_one f) d

/-- The diamond operators fix the restriction of a `Γ₀(N)`-cusp form. -/
theorem diamondOpCusp_ofLe (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ) :
    diamondOpCusp k d (CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f) =
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (mem_cuspFormCharSpace_one_iff_diamondOpCusp _).mp (ofLe_mem_cuspFormCharSpace_one f) d

/-- The trivial-nebentypus space is exactly the image of `M_k(Γ₀(N))` under restriction. -/
theorem modFormCharSpace_one_eq_range [NeZero N] :
    modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) =
      LinearMap.range (ModularForm.ofLeₗ (k := k) (Gamma1_map_le_Gamma0_map N)) :=
  Submodule.ext fun f ↦
    (mem_modFormCharSpace_one_iff f).trans
      (ModularForm.mem_range_ofLeₗ_iff _ Subgroup.IsArithmetic.isCusp_of_isCusp f).symm

/-- The trivial-nebentypus space is exactly the image of `S_k(Γ₀(N))` under restriction. -/
theorem cuspFormCharSpace_one_eq_range [NeZero N] :
    cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) =
      LinearMap.range (CuspForm.ofLeₗ (k := k) (Gamma1_map_le_Gamma0_map N)) :=
  Submodule.ext fun f ↦
    (mem_cuspFormCharSpace_one_iff f).trans
      (CuspForm.mem_range_ofLeₗ_iff _ Subgroup.IsArithmetic.isCusp_of_isCusp f).symm

/-! ### The isomorphisms

The two equivalences are deliberately not `@[expose]`, so the `coe_…` lemmas recording that
they preserve the underlying function are written `(rfl)` rather than `rfl`: the parentheses opt
out of exporting the definitional equality, which those lemmas themselves replace downstream.
-/

/-- **The two spellings of `M_k(Γ₀(N))` agree**: the trivial-nebentypus character space
`M_k(Γ₁(N), 1)` is `ℂ`-linearly isomorphic to the space `M_k(Γ₀(N))` of modular forms for the
bare congruence subgroup `Γ₀(N)`, by an isomorphism preserving the underlying function on `ℍ`
(`coe_modFormCharSpaceOneEquiv_apply`). -/
noncomputable def modFormCharSpaceOneEquiv (N : ℕ) [NeZero N] (k : ℤ) :
    modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ((mem_modFormCharSpace_one_iff _).mp f.2)
  map_add' _ _ := ModularForm.ext fun _ ↦ by simp
  map_smul' _ _ := ModularForm.ext fun _ ↦ by simp
  invFun f := ⟨ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f,
    ofLe_mem_modFormCharSpace_one f⟩
  left_inv _ := Subtype.ext (ModularForm.ext fun _ ↦ by simp)
  right_inv _ := ModularForm.ext fun _ ↦ by simp

/-- `modFormCharSpaceOneEquiv` does not change the underlying function on `ℍ`: a
trivial-nebentypus form is converted to a `Γ₀(N)`-form by re-reading it, not by transporting
it. -/
@[simp]
theorem coe_modFormCharSpaceOneEquiv_apply [NeZero N]
    (f : modFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ⇑(modFormCharSpaceOneEquiv N k f) = ⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ModularForm.coe_ofSlashInvariant _ _ _

/-- The inverse of `modFormCharSpaceOneEquiv` is the restriction `ModularForm.ofLe` of a
`Γ₀(N)`-form to `Γ₁(N)`; in particular it too preserves the underlying function on `ℍ`. -/
@[simp]
theorem coe_modFormCharSpaceOneEquiv_symm_apply [NeZero N]
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (((modFormCharSpaceOneEquiv N k).symm f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ModularForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (rfl)

/-- **The two spellings of `S_k(Γ₀(N))` agree**: the cusp-form analogue of
`modFormCharSpaceOneEquiv`. -/
noncomputable def cuspFormCharSpaceOneEquiv (N : ℕ) [NeZero N] (k : ℤ) :
    cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := CuspForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ((mem_cuspFormCharSpace_one_iff _).mp f.2)
  map_add' _ _ := CuspForm.ext fun _ ↦ by simp
  map_smul' _ _ := CuspForm.ext fun _ ↦ by simp
  invFun f := ⟨CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f, ofLe_mem_cuspFormCharSpace_one f⟩
  left_inv _ := Subtype.ext (CuspForm.ext fun _ ↦ by simp)
  right_inv _ := CuspForm.ext fun _ ↦ by simp

/-- `cuspFormCharSpaceOneEquiv` does not change the underlying function on `ℍ`: a
trivial-nebentypus cusp form is converted to a `Γ₀(N)`-cusp form by re-reading it, not by
transporting it. -/
@[simp]
theorem coe_cuspFormCharSpaceOneEquiv_apply [NeZero N]
    (f : cuspFormCharSpace (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :
    ⇑(cuspFormCharSpaceOneEquiv N k f) = ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  CuspForm.coe_ofSlashInvariant _ _ _

/-- The inverse of `cuspFormCharSpaceOneEquiv` is the restriction `CuspForm.ofLe` of a
`Γ₀(N)`-cusp form to `Γ₁(N)`; in particular it too preserves the underlying function on `ℍ`. -/
@[simp]
theorem coe_cuspFormCharSpaceOneEquiv_symm_apply [NeZero N]
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (((cuspFormCharSpaceOneEquiv N k).symm f : cuspFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.ofLe (Gamma1_map_le_Gamma0_map N) f :=
  (rfl)

end TauCeti
