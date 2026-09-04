/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.Analysis.Complex.Periodic

/-!
# The `q`-expansion as a linear map, and uniqueness of coefficients for raw functions

The `q`-expansion of modular forms for a determinant-one subgroup of `GL(2, ℝ)`, bundled as
a `ℂ`-linear map into power series, refining Mathlib's additive `ModularForm.qExpansionAddHom`.

Alongside it, the raw-function form of Mathlib's coefficient-uniqueness statement. Mathlib's
`UpperHalfPlane.qExpansion_coeff_unique` is stated for a bundled `f : F` with
`[FunLike F ℍ ℂ]`, and `ℍ → ℂ` carries no such instance, so an operator built as a plain
function on `ℍ` — every Hecke-style slash sum before it is packaged as a `ModularForm` — cannot
invoke it. The proof is Mathlib's, run through `UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction`,
which *is* stated for `{f : ℍ → ℂ}`, with `qExpansionFormalMultilinearSeries` spelled out
inline for the same reason.

Alongside those, the effect of a `1 / d` translation on the `q`-powers a support condition
leaves alive: shifting the argument by `1 / d` scales the `n`-th `q`-power by a `d`-th root of
unity raised to `n`, so a coefficient function supported on the multiples of `d` does not see the
shift. That is what a `q`-support hypothesis is spent on when descending along `V_d`, and it is
stated here rather than at the descent because it mentions only coefficients, divisibility and
`Function.Periodic.qParam`.

## Main declarations

* `TauCeti.ModularForm.qExpansionLinearMap`.
* `TauCeti.UpperHalfPlane.qExpansion_coeff_unique`.
* `TauCeti.smul_qParam_pow_shift_eq`: a shift by `1 / d` fixes every `q`-power that a
  `d`-supported coefficient function leaves alive.

## References

* [Mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane

namespace TauCeti

variable {h : ℝ}

/-- The `q`-expansion map as a `ℂ`-linear map to power series over `ℂ`, refining the additive
`ModularForm.qExpansionAddHom`. -/
def ModularForm.qExpansionLinearMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toAddHom := (_root_.ModularForm.qExpansionAddHom hh hΓ k).toAddHom
  map_smul' a f := _root_.ModularForm.qExpansion_smul hh hΓ a f

@[simp]
lemma ModularForm.qExpansionLinearMap_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm.qExpansionLinearMap hh hΓ k f = qExpansion h f := by
  unfold ModularForm.qExpansionLinearMap
  rfl

/-- **Uniqueness of `q`-expansion coefficients, for a raw function on `ℍ`.** If `f` is given by
a convergent expansion `f τ = ∑' m, c m * 𝕢 h τ ^ m` and its cusp function is analytic at `0`,
then the `c m` are the coefficients of `qExpansion h f`.

This is Mathlib's `UpperHalfPlane.qExpansion_coeff_unique` with the `[FunLike F ℍ ℂ]` bundling
removed: `ℍ → ℂ` has no `FunLike` instance, so the bundled statement does not apply to an
operator that is still a plain function. -/
lemma UpperHalfPlane.qExpansion_coeff_unique {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 := (_root_.UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction hh hfanalytic
    hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f)
      (.ofScalars ℂ fun m ↦ (qExpansion h f).coeff m) 0 := by
    simpa [_root_.UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

/-- The translate `1 / d +ᵥ σ`, read in `ℂ`, is the subtraction `TauCeti.Periodic.qParam_sub`
expects: that lemma is stated at `z - j`, and the shift here enters as a `+ᵥ` on `ℍ`. Naming the
coercion bridge keeps the root-of-unity computation below free of casting. -/
private lemma coe_vadd_one_div_eq_sub {d : ℕ} (σ : ℍ) :
    ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) = (σ : ℂ) - -(1 / (d : ℂ)) := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- **A shift by `1 / d` fixes every `q`-power the support condition leaves alive.** Translating
the argument by `1 / d` scales the `n`-th `q`-power by a `d`-th root of unity raised to `n`, which
is trivial exactly on the multiples of `d` — and a coefficient function supported there kills
every other index. This is what a `q`-support hypothesis is spent on when descending along `V_d`.
-/
theorem smul_qParam_pow_shift_eq {d : ℕ} [NeZero d] {c : ℕ → ℂ}
    (hc : ∀ n : ℕ, ¬ d ∣ n → c n = 0) (σ : ℍ) (n : ℕ) :
    c n • Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) ^ n =
      c n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  have hqP : Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (d : ℝ)) +ᵥ σ : ℍ) : ℂ) =
      Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (d : ℂ)) := by
    rw [coe_vadd_one_div_eq_sub, TauCeti.Periodic.qParam_sub]
    congr 1
    push_cast
    ring_nf
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    rw [hqP, mul_pow, pow_mul (Complex.exp _) d m,
      (Complex.isPrimitiveRoot_exp d (NeZero.ne d)).pow_eq_one, one_pow, mul_one]
  · rw [hc n hdn, zero_smul, zero_smul]

end TauCeti

end
