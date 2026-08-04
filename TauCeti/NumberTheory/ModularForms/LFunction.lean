/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# L-functions of modular forms

For a weight-`k` modular form `f` with `q`-expansion `f(τ) = Σ_{n≥0} aₙ qⁿ`, the
**L-function** is the Dirichlet series `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}`, built on
Mathlib's `LSeries` infrastructure applied to the coefficient sequence of
`UpperHalfPlane.qExpansion` at the strict width of the level at `∞`.

## Main definitions

* `ModularForm.lCoeff f`: the coefficient sequence `n ↦ aₙ(f)`, as `ℕ → ℂ`.
* `ModularForm.lSeries f`: the L-function `s ↦ LSeries (lCoeff f) s`.
* `ModularForm.imAxis f`: `f` along the positive imaginary axis (`0` off it). For a
  *cusp form* `f`, whose decay makes the integral converge, the Mellin transform of this
  restriction is the completed L-function; for general modular forms that reading needs
  the constant term subtracted first.

## Main results

Hecke's convergence bounds, from Mathlib's `q`-expansion coefficient growth:

* `ModularForm.abscissaOfAbsConv_lCoeff_le`: for a modular form of weight `k ≥ 0`,
  the abscissa of absolute convergence is at most `k + 1` (from `aₙ = O(nᵏ)`).
* `ModularForm.abscissaOfAbsConv_lCoeff_le_cuspForm`: for a cusp form, at most
  `k/2 + 1` (from Hecke's `aₙ = O(n^{k/2})`).

The non-cuspidal abscissa bound `k + 1` is weaker than Diamond–Shurman Prop. 5.9.1
(which gives convergence for `Re s > k` via `aₙ = O(n^{k-1})`); tightening it is a
separate milestone of the roadmap's Layer 7.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/LFunction.lean`), with the abscissa bounds — advertised
but not present there — supplied from Mathlib's `ModularFormClass.qExpansion_isBigO` and
`CuspFormClass.qExpansion_isBigO`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16
* The AINTLIB `LeanModularForms` project,
  <https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>
  (`Modularforms/LFunction.lean`)
-/

public section

noncomputable section

open Filter LSeries UpperHalfPlane

namespace ModularForm

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The coefficient sequence `n ↦ aₙ(f)` of the `q`-expansion of `f` at the strict width
at `∞` of its level, viewed as `ℕ → ℂ` — the natural input to Mathlib's `LSeries`. -/
def lCoeff [ModularFormClass F Γ k] (f : F) : ℕ → ℂ :=
  fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n

@[simp]
lemma lCoeff_apply [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    lCoeff f n = (qExpansion Γ.strictWidthInfty f).coeff n := (rfl)

/-- The **L-function** of a modular form: the Dirichlet series
`L(s, f) = Σ_{n ≥ 1} aₙ(f) · n^{-s}` of its `q`-expansion coefficients. -/
def lSeries [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  LSeries (lCoeff f) s

@[simp]
lemma lSeries_apply [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lSeries f s = LSeries (lCoeff f) s := (rfl)


/-- **A function on `ℍ` along the positive imaginary axis**: `t > 0` maps to `f(i·t)`,
and `t ≤ 0` to `0`. For a cusp form `f`, whose decay makes the integral converge, the
Mellin transform of this restriction is the completed L-function. -/
def imAxis (f : ℍ → ℂ) (t : ℝ) : ℂ :=
  if h : 0 < t then
    f ⟨Complex.I * (t : ℂ), by simpa only [Complex.I_mul_im, Complex.ofReal_re] using h⟩
  else 0

@[simp]
lemma imAxis_apply_of_pos (f : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    imAxis f t =
      f ⟨Complex.I * (t : ℂ), by simpa only [Complex.I_mul_im, Complex.ofReal_re] using ht⟩ := by
  rw [imAxis, dif_pos ht]

@[simp]
lemma imAxis_apply_of_nonpos (f : ℍ → ℂ) {t : ℝ} (ht : ¬ 0 < t) :
    imAxis f t = 0 := by
  rw [imAxis, dif_neg ht]

variable [Γ.IsArithmetic]

/-- **Hecke's abscissa bound for modular forms**: for weight `k ≥ 0`, the L-series of a
modular form converges absolutely for `Re s > k + 1` (from `aₙ = O(nᵏ)`). -/
theorem abscissaOfAbsConv_lCoeff_le (hk : 0 ≤ k) [ModularFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ ((k : ℝ) : EReal) + 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow ?_
  have h := ModularFormClass.qExpansion_isBigO hk f
  have h_lCoeff : lCoeff f = fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n :=
    funext (lCoeff_apply f)
  rw [h_lCoeff]
  refine h.congr' EventuallyEq.rfl (Eventually.of_forall fun n ↦ ?_)
  simp only [Real.rpow_intCast]

/-- **Hecke's abscissa bound for cusp forms**: the L-series of a cusp form converges
absolutely for `Re s > k/2 + 1` (from Hecke's `aₙ = O(n^{k/2})`). -/
theorem abscissaOfAbsConv_lCoeff_le_cuspForm [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 := by
  have h_lCoeff : lCoeff f = fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n :=
    funext (lCoeff_apply f)
  rw [h_lCoeff]
  exact LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (CuspFormClass.qExpansion_isBigO f)

end ModularForm
