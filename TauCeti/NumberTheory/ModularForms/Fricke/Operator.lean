/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.ModularForms.Basic
public import TauCeti.NumberTheory.ModularForms.Fricke.Conjugation

/-!
# The Fricke slash operator on modular and cusp forms

The Fricke matrix `W = !![0, -1; N, 0]` of `TauCeti/NumberTheory/ModularForms/Fricke/Matrix.lean`
normalizes `Γ₁(N)`, by `frickeConjSL_mem_Gamma1` of
`TauCeti/NumberTheory/ModularForms/Fricke/Conjugation.lean`. Read in `GL (Fin 2) ℝ` that is the
subgroup identity `Gamma1_map_inv_conjAct_frickeGL_eq`, and this file packages `f ↦ f ∣[k] W` as
a `ℂ`-linear endomorphism `frickeOperator` of `M_k(Γ₁(N))` and `frickeOperatorCusp` of
`S_k(Γ₁(N))`.

## What this operator is, and what it is not

`frickeOperator` is the **raw slash by `W`**: it carries no normalizing scalar, and it is
therefore **not an involution**. With mathlib's weight-`k` slash and `W² = (-N) • 1`
(`coe_frickeGL_sq`) it squares to multiplication by the scalar `N ^ (2 * (k - 1)) * (-N) ^ (-k)`,
that is `(-1) ^ k * N ^ (k - 2)`. That scalar is AINTLIB's `frickeScalar N k`, where the identity
is proved; it is not restated here.

The roadmap's Fricke operator is the **normalized** `𝒲_N = (√N) ^ (2 - k) • (· ∣[k] W)`, which
brings that scalar down to `(-1) ^ k` and so is an involution in even weight — the weights the
sign theory lives in. It is a later rung, and every downstream statement about signs, eigenvalues
and functional equations is about `𝒲_N`, not about the map defined here. The name
`frickeOperator` is AINTLIB's own name for the un-normalized map that this file ports, and the
roadmap names it as the declaration to migrate, so it is kept; a consumer wanting `𝒲_N` must
supply the normalization.

## Construction

Both operators are mathlib's `ModularForm.translate`/`CuspForm.translate` — which slash by an
arbitrary `g : GL (Fin 2) ℝ` and carry holomorphy and the cusp conditions with them — transported
back to level `Γ₁(N)` along `Gamma1_map_inv_conjAct_frickeGL_eq` with `mcast`. This is the
construction `diamondOpAux` of `TauCeti/NumberTheory/ModularForms/DiamondOperators.lean` already
uses for conjugation by `Γ₀(N)`. Nothing about the cusps is proved here.

## `ℂ`-linearity

Scalars commute past a slash only on the positive-determinant branch — mathlib's
`ModularForm.smul_slash` otherwise carries the twist `σ A c`, which is complex conjugation.
`det W = N > 0`, so `ModularForm.smul_slash_of_det_pos` of
`TauCeti/NumberTheory/ModularForms/Basic.lean` applies and gives `map_smul'` for both operators.

## Main definitions

* `TauCeti.frickeOperator`: the un-normalized Fricke slash operator on `M_k(Γ₁(N))`.
* `TauCeti.frickeOperatorCusp`: the un-normalized Fricke slash operator on `S_k(Γ₁(N))`.

## Main results

* `TauCeti.Gamma1_map_inv_conjAct_frickeGL_eq`: `W` normalizes the image of `Γ₁(N)` in
  `GL (Fin 2) ℝ`. This is the group-level content of the construction, and what the later rungs
  (the character-space transport, the `W_Q` family) consume.
* `TauCeti.coe_frickeOperator`, `TauCeti.coe_frickeOperatorCusp`: on underlying functions both
  operators are `⇑f ∣[k] W`.
* `TauCeti.frickeOperator_coe_cuspForm`: the two operators agree under the coercion
  `S_k(Γ₁(N)) → M_k(Γ₁(N))`.

## Provenance

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Fricke.lean`](https://github.com/CBirkbeck/AINTLIB),
commit `340875adfb2`, Apache-2.0, Chris Birkbeck), realizing part of Layer 6 of the ModularForms
roadmap.

AINTLIB slashes by `(frickeGL N : GL (Fin 2) ℚ)` and lets the coercion to `GL (Fin 2) ℝ` do the
work, so its `frickeSlash_invariant` consumes the hand-transported identity
`glMap_frickeGL_mul_mapGL`; here `W` is read over `ℝ` directly, as an instance of the
field-parameterized `frickeGL_mul_mapGL`, so no transport lemma appears. For the same reason
AINTLIB's `frickeGL_det_pos` is `val_det_frickeGL_pos` read at `ℝ`.

Neither the slash-invariance nor the cusp conditions are ported. AINTLIB builds both operators
field by field, deriving invariance from its own `frickeSlash_invariant` and rebuilding the image
cusp by hand out of `isCusp_SL2Z_iff` before descending along the finite index of `Γ₁(N)` in
`SL₂(ℤ)`. Here the normalizer identity `Gamma1_map_inv_conjAct_frickeGL_eq` reduces both
operators to `translate`, which mathlib proves for an arbitrary real matrix, so neither argument
is needed.

AINTLIB proves `ℂ`-linearity with its own `smul_slash_pos_det`; the corresponding TauCeti lemma
`ModularForm.smul_slash_of_det_pos` was already on hand, and is more general (any scalar `α`
acting on `ℂ` by an `IsScalarTower`, rather than `ℂ` itself).

The diamond-shift theorem `frickeOperator_diamondOp` of the source (`W ∘ ⟨d⟩ = ⟨d⁻¹⟩ ∘ W`) is
deliberately *not* ported here: it is stated through AINTLIB's `Gamma0MapUnits`, the unit-valued
refinement of mathlib's `CongruenceSubgroup.Gamma0Map`, which TauCeti does not have — the same
definition whose absence already kept `Gamma0MapUnits_frickeConjSL` out of
`Fricke/Conjugation.lean`.
It belongs with that definition and with the character-space transport, not here.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §5.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **`W` normalizes `Γ₁(N)` in `GL (Fin 2) ℝ`**: conjugating the image of `Γ₁(N)` by the Fricke
matrix returns that same subgroup. This is `frickeConjSL_mem_Gamma1` — that `W σ W⁻¹` stays in
`Γ₁(N)` — turned into a statement about the subgroup itself, which is the form the operators
below and the later Fricke rungs consume.

Both inclusions come from the normalization identities of `Fricke/Conjugation.lean`:
`frickeGL_mul_mapGL` moves `W` rightwards past `σ` and gives `⊇`, and `mapGL_mul_frickeGL`
moves it leftwards and gives `⊆`. The shape matches `Gamma1_map_inv_conjAct_eq`, the same
statement for conjugation by `Γ₀(N)`. -/
public theorem Gamma1_map_inv_conjAct_frickeGL_eq :
    ConjAct.toConjAct (frickeGL ℝ N)⁻¹ • (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτy⟩
    refine ⟨frickeConjSL ⟨τ, Gamma1_in_Gamma0 N hτ⟩, frickeConjSL_mem_Gamma1 τ hτ, ?_⟩
    have h : mapGL ℝ τ * frickeGL ℝ N
        = frickeGL ℝ N * mapGL ℝ (frickeConjSL ⟨τ, Gamma1_in_Gamma0 N hτ⟩) :=
      mapGL_mul_frickeGL ℝ ⟨τ, Gamma1_in_Gamma0 N hτ⟩
    rw [hτy] at h
    refine (mul_left_cancel (a := frickeGL ℝ N) ?_).symm
    rw [← h]
    group
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨frickeConjSL ⟨σ, Gamma1_in_Gamma0 N hσ⟩, frickeConjSL_mem_Gamma1 σ hσ, ?_⟩
    have h : frickeGL ℝ N * mapGL ℝ σ
        = mapGL ℝ (frickeConjSL ⟨σ, Gamma1_in_Gamma0 N hσ⟩) * frickeGL ℝ N :=
      frickeGL_mul_mapGL ℝ ⟨σ, Gamma1_in_Gamma0 N hσ⟩
    rw [h]
    group

/-- **The Fricke slash operator** on `M_k(Γ₁(N))`: `f ↦ f ∣[k] W` for `W = !![0, -1; N, 0]`,
as a `ℂ`-linear endomorphism.

This is mathlib's `ModularForm.translate` by `W`, whose level `W⁻¹ Γ₁(N) W` is `Γ₁(N)` again by
`Gamma1_map_inv_conjAct_frickeGL_eq`; `mcast` transports it back. It carries **no** normalizing
scalar and is not an involution — see the module docstring. -/
public noncomputable def frickeOperator (k : ℤ) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    ModularForm.mcast rfl (ModularForm.translate f (frickeGL ℝ N))
      Gamma1_map_inv_conjAct_frickeGL_eq.symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (frickeGL ℝ N) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun (ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos ⇑f c) z

/-- On underlying functions the Fricke slash operator is `⇑f ∣[k] W`. -/
@[simp]
public theorem coe_frickeOperator (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(frickeOperator (N := N) k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := (rfl)

/-- **The Fricke slash operator on cusp forms** `S_k(Γ₁(N))`: the cusp-form counterpart of
`frickeOperator`, built the same way from `CuspForm.translate`, so vanishing at the cusps comes
from mathlib exactly as boundedness does. -/
public noncomputable def frickeOperatorCusp (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    CuspForm.mcast rfl (CuspForm.translate f (frickeGL ℝ N))
      Gamma1_map_inv_conjAct_frickeGL_eq.symm
  map_add' f g := by
    ext z
    exact congr_fun (SlashAction.add_slash k (frickeGL ℝ N) ⇑f ⇑g) z
  map_smul' c f := by
    ext z
    exact congr_fun (ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos ⇑f c) z

/-- On underlying functions the Fricke slash operator on cusp forms is `⇑f ∣[k] W`. -/
@[simp]
public theorem coe_frickeOperatorCusp (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(frickeOperatorCusp (N := N) k f) : ℍ → ℂ) = ⇑f ∣[k] frickeGL ℝ N := (rfl)

/-- **The two Fricke slash operators agree under the coercion** `S_k(Γ₁(N)) → M_k(Γ₁(N))`:
both slash by `W`, which does not see whether a form vanishes at the cusps. This is the
counterpart of `diamondOp_coe_cuspForm` for the diamond operators. -/
@[simp]
public theorem frickeOperator_coe_cuspForm (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    frickeOperator k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (frickeOperatorCusp k f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  DFunLike.coe_injective <| by
    rw [coe_frickeOperator, ModularFormClass.coe_modularForm, ModularFormClass.coe_modularForm,
      coe_frickeOperatorCusp]

end TauCeti
