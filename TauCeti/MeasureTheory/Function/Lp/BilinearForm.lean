/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Bilinear forms with `L∞` coefficients on `L²`

An essentially bounded field of continuous bilinear forms acts on two square-integrable
functions by pointwise evaluation and integration.  This file packages that operation as a
continuous bilinear form using Mathlib's Hölder multiplication and `Lᵖ` pairing.

## Main declarations

* `TauCeti.lpBilinearForm`: the continuous bilinear form associated to an `L∞` field.
* `TauCeti.lpBilinearForm_apply`: its integral characterization.
* `TauCeti.lpBilinearForm_congr_ae`: invariance under a.e. equality of coefficient fields.
-/

public section

noncomputable section

namespace TauCeti

open ENNReal MeasureTheory

variable {X J : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup J] [NormedSpace ℝ J]

/-- The continuous bilinear form obtained by integrating an essentially bounded field of
continuous bilinear forms against two square-integrable functions. -/
noncomputable def lpBilinearForm (μ : Measure X)
    (B : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ μ) :
    Lp J 2 μ →L[ℝ] Lp J 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ (E := J)).flip.lpPairing μ 2 2).comp
    (((ContinuousLinearMap.apply ℝ (J →L[ℝ] ℝ) (E := J)).flip.holderL
      μ ⊤ 2 2) B)

/-- The `L∞`-coefficient bilinear form is the integral of its pointwise action. -/
@[simp]
theorem lpBilinearForm_apply (μ : Measure X) (B : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ μ)
    (U V : Lp J 2 μ) :
    lpBilinearForm μ B U V = ∫ x, B x (U x) (V x) ∂μ := by
  rw [lpBilinearForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards
      [((ContinuousLinearMap.apply ℝ (J →L[ℝ] ℝ)
        (E := J)).flip.coeFn_holder (r := 2) B U)] with x hx
  simp [hx]

/-- Replacing an `L∞` coefficient field by an almost-everywhere equal field does not change
the associated bilinear form. -/
theorem lpBilinearForm_congr_ae {μ : Measure X}
    {B B' : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ μ} (hB : B =ᵐ[μ] B') :
    lpBilinearForm μ B = lpBilinearForm μ B' := by
  ext U V
  rw [lpBilinearForm_apply, lpBilinearForm_apply]
  apply integral_congr_ae
  filter_upwards [hB] with x hx
  rw [hx]

/-- Applying an `L∞` field of bilinear forms to two `L²` functions gives an integrable
scalar-valued function. -/
theorem integrable_bilinear_apply_of_memLp {μ : Measure X}
    {B : X → J →L[ℝ] J →L[ℝ] ℝ} (hB : MemLp B ⊤ μ) (U V : Lp J 2 μ) :
    Integrable (fun x => B x (U x) (V x)) μ := by
  have hBU : MemLp (fun x => B x (U x)) 2 μ :=
    (ContinuousLinearMap.apply ℝ (J →L[ℝ] ℝ) (E := J)).flip.memLp_of_bilin
      (f := B) (g := fun x => U x) 2 hB (Lp.memLp U)
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.apply ℝ ℝ (E := J)).flip.memLp_of_bilin
      (f := fun x => B x (U x)) (g := fun x => V x) 1 hBU (Lp.memLp V))

end TauCeti

end
