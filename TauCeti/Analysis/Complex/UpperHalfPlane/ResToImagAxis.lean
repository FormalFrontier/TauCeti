/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Notation

/-!
# Restriction of a function on the upper half-plane to the imaginary axis

The Mellin transform computing the completed L-function of a modular form integrates the
form along the positive imaginary axis: Mathlib's `CuspForm.Λ_eq_mellin` reads
`Λ hk f = mellin (fun t ↦ f (ofComplex (I * t)))` for a cusp form. This file names that
restriction,
`resToImagAxis F t = F (i t)` for `t > 0` (and `0` otherwise, since `i t ∈ ℍ` fails for
`t ≤ 0`), for an arbitrary `F : ℍ → ℂ`.

The three predicates `RealOnImagAxis`, `PosOnImagAxis` and `EventuallyPosOnImagAxis` record
that the restriction is real-valued, real and positive, or real and eventually positive along
`atTop`. `RealOnImagAxis` is closed under constants, negation, addition, subtraction,
multiplication, multiplication by a real scalar, and natural powers; the two positivity
predicates are closed under the operations that preserve strict positivity —
positive constants, addition, multiplication, multiplication by a positive real scalar, and
natural powers — but not under negation or subtraction. The closure lemmas are tagged
`@[fun_prop]`, except `PosOnImagAxis.const` and `EventuallyPosOnImagAxis.const`, whose
constant is not determined by the goal.

## Main definitions

* `UpperHalfPlane.resToImagAxis`: the restriction `t ↦ F (i t)`, extended by `0` on `t ≤ 0`.
* `UpperHalfPlane.RealOnImagAxis`, `PosOnImagAxis`, `EventuallyPosOnImagAxis`: the restriction
  is real-valued, positive, or eventually positive along `atTop`.

## Main results

* `UpperHalfPlane.resToImagAxis_of_pos`, `resToImagAxis_of_nonpos`: the characteristic
  equations of the restriction.
* `UpperHalfPlane.resToImagAxis_zero`, `_add`, `_neg`, `_sub`, `_mul`, `_smul`: the
  restriction commutes with the pointwise operations, unconditionally.
* `UpperHalfPlane.differentiableAt_resToImagAxis`: the restriction is real-differentiable at
  `t > 0` when `F ∘ ofComplex` is, and `differentiableAt_resToImagAxis_of_mDiffAt`: the same
  from manifold differentiability at the corresponding point.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/ResToImagAxis.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), with the
`Function.resToImagAxis` dot-notation alias dropped in favour of the single definition, the
repeated unfolding replaced by `resToImagAxis_of_pos`, and eventual positivity phrased with
the `atTop` filter. The slash-action behaviour of the restriction, the one modular-forms
statement of the source file, lives in
`TauCeti/NumberTheory/ModularForms/ResToImagAxis.lean`.
-/

public section

open Complex Filter Topology

open scoped Manifold

namespace UpperHalfPlane

/-- The restriction of `F : ℍ → ℂ` to the positive imaginary axis, `t ↦ F (i t)`. Since
`i t` lies in `ℍ` only for `t > 0`, the restriction is extended by `0` on `t ≤ 0`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨Complex.I * t, by simpa using ht⟩ else 0

/-- The characteristic equation of `resToImagAxis` on its domain of interest. -/
@[simp]
theorem resToImagAxis_of_pos (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    resToImagAxis F t = F ⟨Complex.I * t, by simpa using ht⟩ := dite_eq_left ht

/-- Off the positive axis the restriction is `0` by convention. -/
@[simp]
theorem resToImagAxis_of_nonpos (F : ℍ → ℂ) {t : ℝ} (ht : t ≤ 0) :
    resToImagAxis F t = 0 := dite_eq_right (not_lt.mpr ht)

/-! ### The restriction commutes with the pointwise operations

Each identity is unconditional in `t`: off the positive axis both sides are `0`.
-/

/-- The restriction of `0` is `0`. -/
@[simp]
theorem resToImagAxis_zero : resToImagAxis 0 = 0 := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The restriction commutes with negation. -/
@[simp]
theorem resToImagAxis_neg (F : ℍ → ℂ) : resToImagAxis (-F) = -resToImagAxis F := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The restriction commutes with addition. -/
@[simp]
theorem resToImagAxis_add (F G : ℍ → ℂ) :
    resToImagAxis (F + G) = resToImagAxis F + resToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The restriction commutes with subtraction. -/
@[simp]
theorem resToImagAxis_sub (F G : ℍ → ℂ) :
    resToImagAxis (F - G) = resToImagAxis F - resToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The restriction commutes with pointwise multiplication. -/
@[simp]
theorem resToImagAxis_mul (F G : ℍ → ℂ) :
    resToImagAxis (F * G) = resToImagAxis F * resToImagAxis G := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The restriction commutes with scalar multiplication. -/
@[simp]
theorem resToImagAxis_smul (c : ℂ) (F : ℍ → ℂ) :
    resToImagAxis (c • F) = c • resToImagAxis F := by
  funext t
  rcases le_or_gt t 0 with ht | ht <;> simp [resToImagAxis_of_pos, resToImagAxis_of_nonpos, ht]

/-- The real-scalar form of `resToImagAxis_smul`: the complex-scalar law does not fire on
`(c : ℝ) • F`. Private, since its three consumers — `RealOnImagAxis.const_smul`,
`PosOnImagAxis.const_smul` and `EventuallyPosOnImagAxis.const_smul` — are all in this file. -/
@[simp]
private theorem resToImagAxis_real_smul (c : ℝ) (F : ℍ → ℂ) :
    resToImagAxis (c • F) = c • resToImagAxis F := by
  simpa [Complex.real_smul] using resToImagAxis_smul (c : ℂ) F

/-! ### Real-valuedness, positivity, and eventual positivity -/

/-- `F` is real-valued on the positive imaginary axis. -/
@[fun_prop]
def RealOnImagAxis (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (resToImagAxis F t).im = 0

/-- `F` is real and strictly positive on the positive imaginary axis. -/
@[fun_prop]
def PosOnImagAxis (F : ℍ → ℂ) : Prop :=
  RealOnImagAxis F ∧ ∀ t : ℝ, 0 < t → 0 < (resToImagAxis F t).re

/-- `F` is real on the positive imaginary axis and strictly positive far out along it. -/
@[fun_prop]
def EventuallyPosOnImagAxis (F : ℍ → ℂ) : Prop :=
  RealOnImagAxis F ∧ ∀ᶠ t : ℝ in atTop, 0 < (resToImagAxis F t).re

/-! ### Differentiability -/

/-- The restriction is real-differentiable at `t > 0` whenever `F ∘ ofComplex` is: the
restriction is its composite with `t ↦ i t`, so only real differentiability at the
corresponding point is used — holomorphy is not needed. -/
theorem differentiableAt_resToImagAxis (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t)
    (hF : DifferentiableAt ℝ (fun z : ℂ ↦ F (ofComplex z)) (Complex.I * t)) :
    DifferentiableAt ℝ (resToImagAxis F) t := by
  have h_diff : DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    have hmul : DifferentiableAt ℝ (fun s : ℝ ↦ Complex.I * s) t := by fun_prop
    simpa only [Function.comp_def] using hF.comp t hmul
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [resToImagAxis_of_pos F hs, ofComplex_apply_of_im_pos (by simp [hs])]

/-- The manifold-differentiable case, which is how modular forms supply the hypothesis. -/
@[fun_prop]
theorem differentiableAt_resToImagAxis_of_mDiffAt (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t)
    (hF : MDiffAt F ⟨Complex.I * t, by simpa using ht⟩) :
    DifferentiableAt ℝ (resToImagAxis F) t :=
  differentiableAt_resToImagAxis F ht ((mdifferentiableAt_iff.mp hF).restrictScalars ℝ)

/-! ### Real-valuedness is preserved by the algebraic operations -/

namespace RealOnImagAxis

/-- A real constant is real-valued on the imaginary axis. -/
@[fun_prop]
theorem const (c : ℝ) : RealOnImagAxis (fun _ ↦ (c : ℂ)) := fun t ht ↦ by
  simp [resToImagAxis_of_pos _ ht]

/-- The zero function is real-valued on the imaginary axis. -/
@[fun_prop]
theorem zero : RealOnImagAxis (fun _ ↦ 0) := by simpa using const 0

/-- The constant function `1` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem one : RealOnImagAxis (fun _ ↦ 1) := by simpa using const 1

/-- Negation preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem neg {F : ℍ → ℂ} (hF : RealOnImagAxis F) : RealOnImagAxis (-F) := fun t ht ↦ by
  simp [hF t ht]

/-- Addition preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F + G) := fun t ht ↦ by
  simp [hF t ht, hG t ht]

/-- Subtraction preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem sub {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F - G) := by simpa [sub_eq_add_neg] using hF.add hG.neg

/-- Multiplication preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : RealOnImagAxis F) (hG : RealOnImagAxis G) :
    RealOnImagAxis (F * G) := fun t ht ↦ by
  simp [Complex.mul_im, hF t ht, hG t ht]

/-- Real scalar multiplication preserves real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem const_smul {F : ℍ → ℂ} {c : ℝ} (hF : RealOnImagAxis F) : RealOnImagAxis (c • F) :=
  fun t ht ↦ by
  rw [resToImagAxis_real_smul]
  simp [Complex.real_smul, Complex.mul_im, hF t ht]

/-- Natural powers preserve real-valuedness on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : RealOnImagAxis F) (n : ℕ) : RealOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end RealOnImagAxis

/-! ### Positivity is preserved by the algebraic operations -/

namespace PosOnImagAxis

/-- A positive real constant is positive on the imaginary axis. -/
theorem const {c : ℝ} (hc : 0 < c) : PosOnImagAxis (fun _ ↦ (c : ℂ)) :=
  ⟨RealOnImagAxis.const c, fun t ht ↦ by simpa [resToImagAxis_of_pos _ ht] using hc⟩

/-- The constant function `1` is positive on the imaginary axis. -/
@[fun_prop]
theorem one : PosOnImagAxis (fun _ ↦ 1) := by simpa using const one_pos

/-- Addition preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : PosOnImagAxis F) (hG : PosOnImagAxis G) :
    PosOnImagAxis (F + G) :=
  ⟨hF.1.add hG.1, fun t ht ↦ by simpa using add_pos (hF.2 t ht) (hG.2 t ht)⟩

/-- Multiplication preserves positivity on the imaginary axis: the two restrictions are real
there, so the real part of the product is the product of the real parts. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : PosOnImagAxis F) (hG : PosOnImagAxis G) :
    PosOnImagAxis (F * G) :=
  ⟨hF.1.mul hG.1, fun t ht ↦ by
    simpa [Complex.mul_re, hF.1 t ht, hG.1 t ht] using mul_pos (hF.2 t ht) (hG.2 t ht)⟩

/-- Positive scalar multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem const_smul {F : ℍ → ℂ} {c : ℝ} (hF : PosOnImagAxis F) (hc : 0 < c) :
    PosOnImagAxis (c • F) :=
  ⟨hF.1.const_smul, fun t ht ↦ by
    rw [resToImagAxis_real_smul]
    simpa [Complex.real_smul, Complex.mul_re] using mul_pos hc (hF.2 t ht)⟩

/-- Natural powers preserve positivity on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : PosOnImagAxis F) (n : ℕ) : PosOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end PosOnImagAxis

/-! ### Eventual positivity is preserved by the algebraic operations -/

namespace EventuallyPosOnImagAxis

/-- Positivity everywhere implies positivity far out. -/
@[fun_prop]
theorem _root_.UpperHalfPlane.PosOnImagAxis.eventuallyPos {F : ℍ → ℂ}
    (hF : PosOnImagAxis F) : EventuallyPosOnImagAxis F :=
  ⟨hF.1, by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hF.2 t ht⟩

/-- The constant function `1` is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem one : EventuallyPosOnImagAxis (fun _ ↦ 1) := PosOnImagAxis.one.eventuallyPos

/-- A positive real constant is eventually positive on the imaginary axis. -/
theorem const {c : ℝ} (hc : 0 < c) : EventuallyPosOnImagAxis (fun _ ↦ (c : ℂ)) :=
  (PosOnImagAxis.const hc).eventuallyPos

/-- Addition preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem add {F G : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (hG : EventuallyPosOnImagAxis G) :
    EventuallyPosOnImagAxis (F + G) :=
  ⟨hF.1.add hG.1, by
    filter_upwards [hF.2, hG.2] with t hf hg
    simpa using add_pos hf hg⟩

/-- Multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem mul {F G : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (hG : EventuallyPosOnImagAxis G) :
    EventuallyPosOnImagAxis (F * G) :=
  ⟨hF.1.mul hG.1, by
    filter_upwards [hF.2, hG.2, eventually_gt_atTop (0 : ℝ)] with t hf hg ht
    simpa [Complex.mul_re, hF.1 t ht, hG.1 t ht] using mul_pos hf hg⟩

/-- Positive scalar multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem const_smul {F : ℍ → ℂ} {c : ℝ} (hF : EventuallyPosOnImagAxis F) (hc : 0 < c) :
    EventuallyPosOnImagAxis (c • F) :=
  ⟨hF.1.const_smul, by
    filter_upwards [hF.2] with t hf
    rw [resToImagAxis_real_smul]
    simpa [Complex.real_smul, Complex.mul_re] using mul_pos hc hf⟩

/-- Natural powers preserve eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem pow {F : ℍ → ℂ} (hF : EventuallyPosOnImagAxis F) (n : ℕ) :
    EventuallyPosOnImagAxis (F ^ n) := by
  induction n with
  | zero => simpa [Pi.one_def] using one
  | succ n hn => simpa [pow_succ] using hn.mul hF

end EventuallyPosOnImagAxis

end UpperHalfPlane
