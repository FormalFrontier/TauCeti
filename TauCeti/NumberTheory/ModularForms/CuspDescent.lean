/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.Rat.Basic
public import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Vanishing at the cusps descends through the level-raising operator

`Degeneracy.lean` has a `Descent` section, which answers the question the conductor theorem asks:
given only that the *level-raise* `V_d f` is a form, what can be said about `f` itself? Two of the
three conditions a form must satisfy are answered there — the transformation law by
`slash_conjScale_eq_smul_of_slash_scaleGL`, and holomorphy by
`mdifferentiable_of_comp_scaleGL_smul`. The third, vanishing at the cusps, is not: the whole file
mentions `IsCusp` once. This file is that missing third member.

## The one geometric input

Everything rests on the fact that `diag(d, 1)⁻¹ · A` carries `∞` to a cusp, for any
`A ∈ SL(2, ℤ)`. That is *not* a computation: the matrix is rational, and rational matrices carry
cusps to cusps — `IsCusp.smul_map_ratCast`, already in `Cusps/Rat/Basic.lean`. So the only work
is to name `diag(d, 1)` over `ℚ` and record that it pushes forward to `scaleGL d`.

## Main results

* `TauCeti.scaleGLRat`, `TauCeti.map_ratCast_scaleGLRat`: `diag(d, 1)` over `ℚ`, and its
  pushforward to `ℝ`.
* `TauCeti.isCusp_inv_scaleGL_mul_mapGL_smul_infty`: `diag(d, 1)⁻¹ · A` sends `∞` to a cusp of
  any arithmetic subgroup.
* `TauCeti.isZeroAtImInfty_slash_inv_scaleGL_mul_mapGL`: a cusp form therefore vanishes at
  `i∞` after slashing by `diag(d, 1)⁻¹ · A`.
* `TauCeti.isZeroAt_of_smul_slash_scaleGL_eq`: **vanishing at the cusps descends** — if the
  level-raise of `f` is a cusp form for any arithmetic subgroup, then `f` vanishes at every cusp of
  any arithmetic subgroup.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Eigenforms/ConductorTheorem.lean`, Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `2baa76f742bdb4fb8ee323fabba41203bd390e08`), lines
354–486, whose `zero_at_cusps_of_levelRaiseFun_eq` (:471) is the final theorem here.

Statements only, and four of the source's nine declarations are not reproduced at all:

* `cuspWitnessLevelRaiseInv` (:354), its private helper `cuspWitnessLevelRaiseInv_first_col`
  (:360) and `gcd_levelRaise_first_col_ne_zero` build an explicit `SL(2, ℤ)` witness by
  `Classical.choose` over `IsCoprime.exists_SL2_col`, because the source proves the cusp condition
  through mathlib's `isCusp_SL2Z_iff'` (the `SL(2, ℤ)`-orbit criterion). Mathlib also offers
  `isCusp_SL2Z_iff`, which says the cusps of `SL(2, ℤ)` are exactly `ℙ¹(ℚ)`, and `isCusp_SL2Z_iff'`
  is *derived* from it by manufacturing that witness internally. Routing through rationality
  instead — `IsCusp.smul_map_ratCast` — discharges the cusp condition with no witness, no
  `Classical.choose`, and no gcd arithmetic.
* `isZeroAtImInfty_slash_iff_levelRaiseFun_eq` (:425) is one rewrite of what this repository
  already has as `slash_scaleGL_slash_mapGL`, so it is inlined rather than named.

The source is phrased over its own `levelRaiseFun` and `levelRaiseMatrix`, neither of which exists
here; the statements below use `scaleGL` and the hypothesis shape
`⇑g = d ^ (1 - k) • (f ∣[k] scaleGL d)` that `smul_slash_scaleGL_eq` was written to be rewritten
with.

## References

* [Miyake, *Modular forms*][miyake1989], Theorem 4.6.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup OnePoint

open scoped MatrixGroups ModularForm

namespace TauCeti

variable {d : ℕ} [NeZero d]

/-- **`diag(d, 1)` over `ℚ`.** `scaleGL` is stated over `ℝ`, where the slash action lives, but the
cusp argument needs the same matrix over `ℚ`, because what makes `diag(d, 1)⁻¹ · A` carry cusps to
cusps is precisely that it is *rational*. -/
noncomputable def scaleGLRat (d : ℕ) [NeZero d] : GL (Fin 2) ℚ :=
  diagGL ![Units.mk0 (d : ℚ) (Nat.cast_ne_zero.mpr (NeZero.ne d)), 1]

/-- `scaleGLRat` pushes forward to `scaleGL`. -/
@[simp] lemma map_ratCast_scaleGLRat (d : ℕ) [NeZero d] :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (scaleGLRat d) = scaleGL d := by
  -- `scaleGL` sits in a `public section` without `@[expose]`, so its body is sealed to this
  -- module; `coe_scaleGL` is the interface, exactly as `Degeneracy.lean` uses it itself.
  refine Units.ext ?_
  rw [coe_scaleGL]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, scaleGLRat, diagGL_coe,
    Matrix.diagonal_fin_two]
  fin_cases i <;> fin_cases j <;> simp

/-- **`diag(d, 1)⁻¹ · A` carries `∞` to a cusp.** For any `A ∈ SL(2, ℤ)` and any arithmetic
subgroup, the point `(diag(d, 1)⁻¹ · A) • ∞` is a cusp.

The matrix is rational, and that is the whole proof: `IsCusp.smul_map_ratCast` carries the cusp
`∞` along it. The source instead exhibits an explicit `SL(2, ℤ)` matrix with the same first
column; nothing here needs one. -/
lemma isCusp_inv_scaleGL_mul_mapGL_smul_infty (d : ℕ) [NeZero d] (A : SL(2, ℤ))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] :
    IsCusp ((((scaleGL d)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) •
      (∞ : OnePoint ℝ)) Γ := by
  have hinfty : IsCusp (∞ : OnePoint ℝ) Γ :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mpr (isCusp_SL2Z_iff'.mpr ⟨1, by simp⟩)
  have := hinfty.smul_map_ratCast ((scaleGLRat d)⁻¹ * (mapGL ℚ A : GL (Fin 2) ℚ))
  rwa [map_mul, map_inv, map_ratCast_scaleGLRat, A.map_mapGL] at this

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- A cusp form vanishes at `i∞` after slashing by `diag(d, 1)⁻¹ · A`, because that matrix sends
`∞` to a cusp and `CuspFormClass.zero_at_cusps` covers every cusp.

Nothing here is specific to a level: the cusp condition above holds for *any* arithmetic subgroup,
and `zero_at_cusps` asks only that `g` be a cusp form for the same one. Stated over
`CuspFormClass` so it applies to `CuspForm` and to anything else carrying that class. -/
lemma isZeroAtImInfty_slash_inv_scaleGL_mul_mapGL {Γ' : Subgroup (GL (Fin 2) ℝ)}
    [Γ'.IsArithmetic] [CuspFormClass F Γ' k] (d : ℕ) [NeZero d] (g : F) (A : SL(2, ℤ)) :
    IsZeroAtImInfty (⇑g ∣[k] (((scaleGL d)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ))) :=
  CuspFormClass.zero_at_cusps g (isCusp_inv_scaleGL_mul_mapGL_smul_infty d A Γ') _ rfl

/-- **Vanishing at the cusps descends through `V_d`.** If the level-raise of `f` is a cusp form —
for *any* arithmetic subgroup — then `f` vanishes at every cusp of any arithmetic subgroup.

The two subgroups are independent and neither is a level of `f`: `Γ'` is where `g` is a cusp form,
and `Γ` is where the cusp `c` lives. `f` itself is only a function, which is the situation the
conductor theorem is in.

With the transformation law (`slash_conjScale_eq_smul_of_slash_scaleGL`) and holomorphy
(`mdifferentiable_of_comp_scaleGL_smul`) of `Degeneracy.lean`'s `Descent` section, this is the
third and last condition needed to exhibit `f` as a cusp form of the lower level. -/
theorem isZeroAt_of_smul_slash_scaleGL_eq {Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ'.IsArithmetic]
    [CuspFormClass F Γ' k] (d : ℕ) [NeZero d] (f : ℍ → ℂ) (g : F)
    (hg : ⇑g = (d : ℂ) ^ (1 - k) • (f ∣[k] scaleGL d))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    IsZeroAt c f k := by
  have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mp hc
  rw [isZeroAt_iff_exists_SL2Z hcSL]
  obtain ⟨A, hA⟩ := isCusp_SL2Z_iff'.mp hcSL
  refine ⟨A, hA.symm, ?_⟩
  rw [ModularForm.SL_slash]
  -- `g` slashed by `diag(d, 1)⁻¹ · A` is `d ^ (1 - k)` times `f` slashed by `A`: the two
  -- `diag(d, 1)` factors cancel, and the normalizing scalar passes through both slashes because
  -- every matrix in sight has positive determinant.
  have hd : ((d : ℂ) ^ (1 - k)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne d))
  have hkey : ⇑g ∣[k] (((scaleGL d)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) =
      ((d : ℂ) ^ (1 - k)) • (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) := by
    rw [SlashAction.slash_mul, hg, _root_.ModularForm.smul_slash,
      σ_eq_refl_of_det_pos (by simpa using val_det_scaleGL_pos (d := d)),
      ContinuousAlgEquiv.refl_apply, ← SlashAction.slash_mul, mul_inv_cancel,
      SlashAction.slash_one, _root_.ModularForm.smul_slash,
      σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply]
  have := (isZeroAtImInfty_slash_inv_scaleGL_mul_mapGL d g A).smul ((d : ℂ) ^ (1 - k))⁻¹
  rwa [hkey, smul_smul, inv_mul_cancel₀ hd, one_smul] at this

end TauCeti

end
